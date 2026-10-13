import WMFKI_Stochastic.ArrayNonlinearCopies
import WMFKI_Stochastic.ParticleVectorEquation

open MeasureTheory ProbabilityTheory Set
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
open WMFKIMeanFieldCopies WMFKIExternalProbe
open scoped NNReal
namespace WMFKISynchronousModel
variable {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω] {N d : ℕ}

noncomputable def driftGap (π : Measure A) (P : Measure Ω)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d))
    (X : HalfClosedTime → (Fin N → A) × (Fin N → Ω) → Fin (N*d) → ℝ)
    (i : Fin N) (s : ℝ) (z : (Fin N → A) × (Fin N → Ω)) : EuclideanSpace ℝ (Fin d) :=
  particleDrift K (fun j => realParticle X j s z) i -
    ∫ y, K (arrayCopy Y i s z-y) ∂((π.prod P).map (Y s))

/-- 同じ原始初期値・Brownianの相殺。差の時間積分の可積分性も先に確保する。 -/
theorem synchronous_difference_equation (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P]
    (W : Fin d → ℝ≥0 → Ω → ℝ) (ξ : A → EuclideanSpace ℝ (Fin d))
    (T : ℝ) (hT : 0 ≤ T) (σ C : ℝ) {L : ℝ≥0}
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : LipschitzWith L K)
    (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d))
    (hY : ArrayNonlinearFamily π P T K ξ
      (fun t z => σ • WithLp.toLp 2 (fun j => W j (halfTimeReal (realTimeClamp t)) z.2)) Y C)
    (B : BrownianSystem (arrayMeasure π P (Fin N)) (N*d))
    (X : HalfClosedTime → (Fin N → A) × (Fin N → Ω) → Fin (N*d) → ℝ)
    (hBW : ∀ᵐ z ∂arrayMeasure π P (Fin N), ∀ i j t,
      B.W (finProdFinEquiv (i,j)) t z = W j (halfTimeReal t) (z.2 i))
    (hX : VectorSDESolution (arrayMeasure π P (Fin N)) B.F B.W (particleCoordinateDrift N d K)
      (fun i j _ => if i = j then σ else 0) (fun z => packParticles N d (fun i => ξ (z.1 i))) X) :
    ∀ᵐ z ∂arrayMeasure π P (Fin N), ∀ i : Fin N,
      IntervalIntegrable (fun s => driftGap π P K Y X i s z) volume 0 T ∧
      ∀ t ∈ Icc 0 T, realParticle X i t z - arrayCopy Y i t z =
        ∫ s in (0 : ℝ)..t, driftGap π P K Y X i s z := by
  obtain ⟨hXi,hXe⟩ := particle_vector_equation (arrayMeasure π P (Fin N)) B K hK.continuous σ
    (fun z => packParticles N d (fun i => ξ (z.1 i))) X hX
  have hYi := array_population_drift_integrable π P hT hK hY.base_paths N
  filter_upwards [hBW,hXe,hY.equation N,hYi] with z hb hx hy hi
  intro i
  refine ⟨(hXi z i 0 T).sub (hi i),?_⟩
  intro t ht
  have hyt := (hi i).mono_set (show uIcc (0 : ℝ) t ⊆ uIcc 0 T by
    rw [uIcc_of_le ht.1,uIcc_of_le hT];exact Icc_subset_Icc le_rfl ht.2)
  have he := hx i t ht.1
  have hbv : WithLp.toLp 2 (fun j => B.W (finProdFinEquiv (i,j)) (realTimeClamp t) z) =
      WithLp.toLp 2 (fun j => W j (halfTimeReal (realTimeClamp t)) (z.2 i)) := by
    apply congrArg (WithLp.toLp 2)
    funext j
    exact hb i j (realTimeClamp t)
  rw [particlePositions_pack,hbv] at he
  change realParticle X i t z - arrayCopy Y i t z = ∫ s in (0 : ℝ)..t,
    particleDrift K (fun j => realParticle X j s z) i -
      ∫ y, K (arrayCopy Y i s z-y) ∂((π.prod P).map (Y s))
  rw [intervalIntegral.integral_sub (hXi z i 0 t) hyt,he,(hy i).2 t ht]
  abel

/-- 原始入力から得る同期比較の出力。誤差率や未知の比較解を仮定しない。 -/
structure SynchronousParticlePair (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P]
    (W : Fin d → ℝ≥0 → Ω → ℝ) (ξ : A → EuclideanSpace ℝ (Fin d))
    (T σ : ℝ) (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d))
    (B : BrownianSystem (arrayMeasure π P (Fin N)) (N*d))
    (X : HalfClosedTime → (Fin N → A) × (Fin N → Ω) → Fin (N*d) → ℝ) : Prop where
  drivers : ∀ᵐ z ∂arrayMeasure π P (Fin N), ∀ i j t,
    B.W (finProdFinEquiv (i,j)) t z = W j (halfTimeReal t) (z.2 i)
  initial_independent : IndepFun (Prod.fst : (Fin N → A) × (Fin N → Ω) → Fin N → A)
    (fun z (q : Fin (N*d) × HalfClosedTime) => B.W q.1 q.2 z) (arrayMeasure π P (Fin N))
  solution : VectorSDESolution (arrayMeasure π P (Fin N)) B.F B.W (particleCoordinateDrift N d K)
    (fun i j _ => if i = j then σ else 0) (fun z => packParticles N d (fun i => ξ (z.1 i))) X
  difference : ∀ᵐ z ∂arrayMeasure π P (Fin N), ∀ i : Fin N,
    IntervalIntegrable (fun s => driftGap π P K Y X i s z) volume 0 T ∧
    ∀ t ∈ Icc 0 T, realParticle X i t z - arrayCopy Y i t z =
      ∫ s in (0 : ℝ)..t, driftGap π P K Y X i s z

set_option maxHeartbeats 800000 in
/-- 同じ原始入力から一粒子平均場解を先に選び、全Nの粒子系をそのコピーと同期する。 -/
theorem exists_synchronous_particle_family (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P] {d : ℕ}
    (W : Fin d → ℝ≥0 → Ω → ℝ) (hW : ∀ j, IsBrownianReal (W j) P)
    (hm : ∀ j t, Measurable (W j t)) (hI : iIndepFun (fun j ω t => W j t ω) P)
    (ξ : A → EuclideanSpace ℝ (Fin d)) (hξm : Measurable ξ) (hξ : MemLp ξ 4 π)
    (T : ℝ) (hT : 0 ≤ T) (σ : ℝ) {L : ℝ≥0}
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : LipschitzWith L K) :
    ∃ (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d)) (C : ℝ),
      ArrayNonlinearFamily π P T K ξ
        (fun t z => σ • WithLp.toLp 2 (fun j => W j (halfTimeReal (realTimeClamp t)) z.2)) Y C ∧
      ∀ N : ℕ, 0 < N → ∃ (B : BrownianSystem (arrayMeasure π P (Fin N)) (N*d))
        (X : HalfClosedTime → (Fin N → A) × (Fin N → Ω) → Fin (N*d) → ℝ),
        SynchronousParticlePair π P W ξ T σ K Y B X := by
  obtain ⟨_,Y,C,hY,_⟩ := exists_iid_nonlinear_family π P W hW hm hI ξ hξm hξ T hT σ K hK
  have hy := array_family_pullback π P hY
  refine ⟨Y,C,hy,fun N hN => ?_⟩
  obtain ⟨B,X,hbw,hind,hx⟩ := exists_particle_on_arrays π P W hW hm hI ξ hξm hξ N hN K hK σ
  exact ⟨B,X,⟨hbw,hind,hx,synchronous_difference_equation π P W ξ T hT σ C K hK Y hy B X hbw hx⟩⟩

end WMFKISynchronousModel
