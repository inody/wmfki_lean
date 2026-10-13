import WMFKI_Stochastic.ParticleArrayDrivers
import WMFKI_Stochastic.ParticleSDEEnvelope

open MeasureTheory Set
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
open WMFKIExternalProbe
namespace WMFKISynchronousModel
variable {Ω : Type*} [MeasurableSpace Ω] {N d : ℕ}

noncomputable def realParticle (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (i : Fin N) (t : ℝ) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  particlePositions N d (X (realTimeClamp t) ω) i

theorem particle_real_paths (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P (N*d)) (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (σ : ℝ) (ξ : Ω → Fin (N*d) → ℝ) (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hX : VectorSDESolution P B.F B.W (particleCoordinateDrift N d K)
      (fun i j _ => if i = j then σ else 0) ξ X) :
    ∀ ω i, Continuous (fun t => realParticle X i t ω) := by
  have hf (r : ℝ) : (realTimeClamp r : HalfClosedTime) < ⊤ := by
    apply (real_time_clamp_mono (le_max_left r 0)).trans_lt
    exact real_time_below (max r 0) (le_max_right r 0) (EReal.coe_lt_top _)
  have hc ω : Continuous (fun r : ℝ => X (realTimeClamp r) ω) :=
    continuous_iff_continuousAt.mpr (fun r =>
      (hX.path ω _ (hf r)).comp real_time_clamp_continuous.continuousAt)
  exact fun ω i => (continuous_particlePositions N d i).comp (hc ω)

/-- 座標SDEをベクトルの実際の時間積分へ戻す。可積分性を連続性から証明する。 -/
theorem particle_vector_equation (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P (N*d)) (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hK : Continuous K) (σ : ℝ) (ξ : Ω → Fin (N*d) → ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hX : VectorSDESolution P B.F B.W (particleCoordinateDrift N d K)
      (fun i j _ => if i = j then σ else 0) ξ X) :
    (∀ ω i a b, IntervalIntegrable
      (fun s => particleDrift K (fun j => realParticle X j s ω) i) volume a b) ∧
    (∀ᵐ ω ∂P, ∀ i t, 0 ≤ t → realParticle X i t ω = particlePositions N d (ξ ω) i +
      (∫ s in (0 : ℝ)..t, particleDrift K (fun j => realParticle X j s ω) i) +
        σ • WithLp.toLp 2 (fun j => B.W (finProdFinEquiv (i,j)) (realTimeClamp t) ω)) := by
  have hc := particle_real_paths P B K σ ξ X hX
  have hi ω i a b : IntervalIntegrable
      (fun s => particleDrift K (fun j => realParticle X j s ω) i) volume a b :=
    (particleDrift_path_continuous K hK
      (fun j t => realParticle X j t ω) (hc ω) i).intervalIntegrable a b
  refine ⟨hi,?_⟩
  filter_upwards [additive_sde_equation P B (particleCoordinateDrift N d K) σ ξ X hX] with ω he
  intro i t ht
  ext j
  have hev := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j).intervalIntegral_comp_comm (hi ω i 0 t)
  change (∫ s in (0 : ℝ)..t, (particleDrift K (fun k => realParticle X k s ω) i) j) =
    (∫ s in (0 : ℝ)..t, particleDrift K (fun k => realParticle X k s ω) i) j at hev
  change X (realTimeClamp t) ω (finProdFinEquiv (i,j)) =
    ξ ω (finProdFinEquiv (i,j)) +
      (∫ s in (0 : ℝ)..t, particleDrift K (fun k => realParticle X k s ω) i) j +
      σ * B.W (finProdFinEquiv (i,j)) (realTimeClamp t) ω
  rw [← hev]
  simpa only [particleCoordinateDrift,Equiv.symm_apply_apply,realParticle] using he t ht (finProdFinEquiv (i,j))

end WMFKISynchronousModel
