import WMFKI_Stochastic.FluctuationTimeIntegral
import WMFKI_Stochastic.ParticlePathComparison

open MeasureTheory Set
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
open WMFKISynchronousModel WMFKIExternalProbe
open scoped NNReal BigOperators
namespace WMFKIRealizedFluctuation
variable {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω] {N d : ℕ}

noncomputable def couplingEnvelope (π : Measure A) (P : Measure Ω) (T : ℝ) (L : ℝ≥0)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d)) (i : Fin N)
    (z : (Fin N → A) × (Fin N → Ω)) : ℝ :=
  (fluctuationTimeEnvelope π P T K Y i z +
    (((L : ℝ)+1)*T*Real.exp (2*((L : ℝ)+1)*T))*
      ((N : ℝ)⁻¹*∑ j, fluctuationTimeEnvelope π P T K Y j z))*Real.exp (((L : ℝ)+1)*T)

/-- 期待値の連続性を仮定せず、まず実際の差分方程式に経路ごとGronwallを適用する。 -/
theorem synchronous_path_envelope (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P] (hN : 0 < N)
    (W : Fin d → ℝ≥0 → Ω → ℝ) (ξ : A → EuclideanSpace ℝ (Fin d))
    (T : ℝ) (hT : 0 ≤ T) (σ R C : ℝ) {L : ℝ≥0}
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : LipschitzWith L K)
    (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d))
    (hy : ArrayNonlinearFamily π P T K ξ
      (fun t z => σ • WithLp.toLp 2 (fun j => W j (halfTimeReal (realTimeClamp t)) z.2)) Y R)
    (hF : UniformFluctuationFourth π P T K Y C)
    (B : BrownianSystem (arrayMeasure π P (Fin N)) (N*d))
    (X : HalfClosedTime → (Fin N → A) × (Fin N → Ω) → Fin (N*d) → ℝ)
    (hs : SynchronousParticlePair π P W ξ T σ K Y B X) :
    ∀ᵐ z ∂arrayMeasure π P (Fin N), ∀ i : Fin N, ∀ t ∈ Icc 0 T,
      ‖realParticle X i t z-arrayCopy Y i t z‖ ≤ couplingEnvelope π P T L K Y i z := by
  have hx := particle_real_paths (arrayMeasure π P (Fin N)) B K σ
    (fun z => packParticles N d (fun i => ξ (z.1 i))) X hs.solution
  have hyc := ae_all_iff.mpr (fun i : Fin N => (hy.paths N i).continuous)
  have hzint := ae_all_iff.mpr (fun i : Fin N => (fluctuation_time_fourth π P hT hK hy hF hN i).2.2)
  filter_upwards [hs.difference,hyc,hzint] with z hd hc hzi
  let u := fun i t => ‖realParticle X i t z-arrayCopy Y i t z‖
  let m := fun t => (N : ℝ)⁻¹*∑ j, u j t
  let a := fun i => fluctuationTimeEnvelope π P T K Y i z
  let g : ℝ := (L : ℝ)+1
  have hg : 0 < g := by dsimp [g];positivity
  have huc i : ContinuousOn (u i) (Icc 0 T) := ((hx z i).continuousOn.sub (hc i)).norm
  have hmc : ContinuousOn m (Icc 0 T) := (continuousOn_finsetSum _ (fun i _ => huc i)).const_mul _
  have hmn s : 0 ≤ m s := mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hb i t (ht : t ∈ Icc 0 T) : u i t ≤ a i + g*(∫ s in (0 : ℝ)..t, u i s+m s) := by
    have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 T := by
      rw [uIcc_of_le ht.1,uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl ht.2
    have hdi := (hd i).1.mono_set hsub
    have hfi := (hzi i).mono_set hsub
    have hui : IntervalIntegrable (fun s => u i s+m s) volume 0 t :=
      ((huc i).add hmc).intervalIntegrable_of_Icc hT |>.mono_set hsub
    have hbi : IntervalIntegrable (fun s => g*(u i s+m s)+‖arrayFluctuation π P K Y i s z‖) volume 0 t :=
      (hui.const_mul g).add hfi
    have hint := intervalIntegral.integral_mono_on ht.1 hdi.norm hbi (fun s _ => by
      have hbound := synchronous_drift_gap_bound hN π P K hK Y X i s z
      change ‖driftGap π P K Y X i s z‖ ≤ g*(u i s+m s)+‖arrayFluctuation π P K Y i s z‖
      change ‖driftGap π P K Y X i s z‖ ≤ (L : ℝ)*u i s+(L : ℝ)*m s+‖arrayFluctuation π P K Y i s z‖ at hbound
      dsimp only [g]
      nlinarith [norm_nonneg (realParticle X i s z-arrayCopy Y i s z),hmn s])
    have hni := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (f := fun s => driftGap π P K Y X i s z) ht.1
    rw [intervalIntegral.integral_add (hui.const_mul g) hfi,intervalIntegral.integral_const_mul] at hint
    have hfa : (∫ s in (0 : ℝ)..t, ‖arrayFluctuation π P K Y i s z‖) ≤ a i :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (ae_of_all _ (fun _ => norm_nonneg _)) (hzi i)
    change ‖realParticle X i t z-arrayCopy Y i t z‖ ≤ _
    rw [(hd i).2 t ht]
    linarith
  have hen := particle_path_comparison hN u a g T hg hT huc
    (fun i => fluctuation_time_nonneg π P hT K Y i z) hb
  intro i t ht
  apply (hen i t ht).trans_eq
  dsimp only [couplingEnvelope,a,g]
  ring

end WMFKIRealizedFluctuation
