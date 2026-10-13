import WMFKI_Stochastic.GenuineWeakAssembly

open MeasureTheory Set
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
open WMFKIExternalProbe
namespace WMFKIJointAssembly

/-- 位置L2は前段D0の同じ実粒子から供給する中間インターフェース。
    残差エネルギーは実際のSDEからここで導く。独立観測の積拡張・積分移送は
    凍結済みindependent_observed_particle_budgetの証明を再利用する。 -/
theorem independent_residual_from_position
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Pe : Measure Ξ) [IsProbabilityMeasure P] [IsProbabilityMeasure Pe]
    (L N nt d M : ℕ) [MeasurableSpace (EuclideanSpace ℝ (Fin d))] [BorelSpace (EuclideanSpace ℝ (Fin d))]
    (hL : 0 < L) (hN : 0 < N) (q : ℝ) (hq : 0 ≤ q)
    (ε : Fin nt → Fin N → Ξ → EuclideanSpace ℝ (Fin d))
    (hεm : ∀ t i, Measurable (ε t i)) (hεlp : ∀ t i, MemLp (ε t i) 2 Pe)
    (hεq : ∀ t i, (∫ z, ‖ε t i z‖^2 ∂Pe) ≤ q)
    (σ : ℝ) (w τ : Fin nt → ℝ) (W : ℝ) (hw : (∑ t,|w t|) ≤ W)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hKc : Continuous K)
    (Φ : Fin M → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hΦ : ∀ m, Continuous (Φ m))
    (θ : EuclideanSpace ℝ (Fin M)) (hReal : ∀ z, ∑ m, θ m • Φ m z = K z)
    (φ : Fin L → EuclideanSpace ℝ (Fin d) → ℝ) (ψ : Fin L → ℝ → ℝ) (hψc : ∀ a, ContDiff ℝ 1 (ψ a))
    (G H J C A B : ℝ) (hG : 0 ≤ G) (hH : 0 ≤ H) (hJ : 0 ≤ J) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hφ : ∀ a, C3TestBounds d (φ a) G H J)
    (hψ : ∀ a t, |ψ a (τ t)| ≤ B) (hdψ : ∀ a t, |deriv (ψ a) (τ t)| ≤ B)
    (hK : ∀ x, ‖K x‖ ≤ C*(1+‖x‖)) (hKl : ∀ x y, ‖K x-K y‖ ≤ A*‖x-y‖)
    (T : ℝ) (hT : 0 ≤ T) (hτ : ∀ t, τ t ∈ Icc 0 T)
    (hψ0 : ∀ a, ψ a 0 = 0) (hψT : ∀ a, ψ a T = 0)
    (Bsys : BrownianSystem P (N*d)) (ξ : Ω → Fin (N*d) → ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hX : VectorSDESolution P Bsys.F Bsys.W (particleCoordinateDrift N d K)
      (fun i j _ => if i=j then σ else 0) ξ X)
    (R : ℝ) (hR : 0 ≤ R)
    (hxl : ∀ t i, MemLp (particleGrid N d nt τ X t i) 2 P)
    (hxR : ∀ t i, (∫ ω, ‖particleGrid N d nt τ X t i ω‖^2 ∂P) ≤ R)
    (Q e : ℝ)
    (hqb : MemLp (fun ω => discreteResponseVector L N nt d σ w τ φ ψ (particleGrid N d nt τ X) ω-
      continuousResponseVector L N d σ φ ψ T X ω) 2 P)
    (hQb : (∫ ω, ‖discreteResponseVector L N nt d σ w τ φ ψ (particleGrid N d nt τ X) ω-
      continuousResponseVector L N d σ φ ψ T X ω‖^2 ∂P) ≤ Q*e)
    (hqa : MemLp (fun ω => (WithLp.toLp 2 (fun ij : Fin L × Fin M =>
      (discreteDictionaryDesign L N nt d M w τ Φ φ ψ (particleGrid N d nt τ X) ω-
        continuousDictionaryDesign L N d M Φ φ ψ T X ω) ij.1 ij.2) : EuclideanSpace ℝ (Fin L × Fin M))) 2 P)
    (hQa : (∫ ω, (WMFKI.frobenius (discreteDictionaryDesign L N nt d M w τ Φ φ ψ (particleGrid N d nt τ X) ω-
      continuousDictionaryDesign L N d M Φ φ ψ T X ω))^2 ∂P) ≤ Q*e) :
    let Γ := (∑ a : Fin L, G^2*(∫ s in 0..T, (ψ a s)^2))/(L : ℝ)
    let Y := fun t i (z : Ω × Ξ) => particleGrid N d nt τ X t i z.1+ε t i z.2
    let rY := fun z => discreteResponseVector L N nt d σ w τ φ ψ Y z-
      WMFKI.matrixMap (discreteDictionaryDesign L N nt d M w τ Φ φ ψ Y z) θ
    MemLp rY 2 (P.prod Pe) ∧ (∫ z, ‖rY z‖^2 ∂P.prod Pe) ≤
      6*((σ^2/(N : ℝ))*Γ)+12*Q*(1+‖θ‖^2)*e+
      3*(responseObservationConstant d σ W B G J+kernelObservationConstant W B G H C A R)*q := by
  have hxm t i : Measurable (particleGrid N d nt τ X t i) :=
    (continuous_particlePositions N d i).measurable.comp
      ((hX.adapted _ (real_time_below (τ t) (hτ t).1 (EReal.coe_lt_top _))).mono (Bsys.le _) le_rfl)
  let D := independentObservationSamples P Pe N nt R q (particleGrid N d nt τ X) ε hxm hεm
    hxl hεlp hxR hεq
  let Xp : HalfClosedTime → Ω × Ξ → Fin (N*d) → ℝ := fun t z => X t z.1
  have hφ2 a : ContDiff ℝ 2 (φ a) := (hφ a).smooth.of_le (by norm_num)
  obtain ⟨hr,_,hS⟩ := weak_residual_vector_energy P L N d hN Bsys K hKc σ ξ X hX φ hφ2
    (fun _ => G) (fun a => (hφ a).observation_bounds.1) ψ hψc T hT hψ0 hψT
  let S := (σ^2/(N : ℝ))*((∑ a : Fin L, G^2*(∫ s in 0..T, (ψ a s)^2))/(L : ℝ))
  have hrp : MemLp (weakResidualVector L N d K σ φ ψ T Xp) 2 (P.prod Pe) :=
    hr.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := Pe))
  have hSp : (∫ z, ‖weakResidualVector L N d K σ φ ψ T Xp z‖^2 ∂P.prod Pe) ≤ S := by
    change (∫ z : Ω × Ξ, (fun ω => ‖weakResidualVector L N d K σ φ ψ T X ω‖^2) z.1 ∂P.prod Pe) ≤ S
    rw [integral_fun_fst (fun ω => ‖weakResidualVector L N d K σ φ ψ T X ω‖^2)]
    simpa using hS
  have hqbp : MemLp (fun z => discreteResponseVector L N nt d σ w τ φ ψ (particleGrid N d nt τ Xp) z-
      continuousResponseVector L N d σ φ ψ T Xp z) 2 (P.prod Pe) :=
    hqb.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := Pe))
  have hQbp : (∫ z, ‖discreteResponseVector L N nt d σ w τ φ ψ (particleGrid N d nt τ Xp) z-
      continuousResponseVector L N d σ φ ψ T Xp z‖^2 ∂P.prod Pe) ≤ Q*e := by
    change (∫ z : Ω × Ξ, (fun ω => ‖discreteResponseVector L N nt d σ w τ φ ψ (particleGrid N d nt τ X) ω-
      continuousResponseVector L N d σ φ ψ T X ω‖^2) z.1 ∂P.prod Pe) ≤ Q*e
    rw [integral_fun_fst (fun ω => ‖discreteResponseVector L N nt d σ w τ φ ψ (particleGrid N d nt τ X) ω-
      continuousResponseVector L N d σ φ ψ T X ω‖^2)]
    simpa using hQb
  have hqap : MemLp (fun z => (WithLp.toLp 2 (fun ij : Fin L × Fin M =>
      (discreteDictionaryDesign L N nt d M w τ Φ φ ψ (particleGrid N d nt τ Xp) z-
        continuousDictionaryDesign L N d M Φ φ ψ T Xp z) ij.1 ij.2) : EuclideanSpace ℝ (Fin L × Fin M))) 2 (P.prod Pe) :=
    hqa.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := Pe))
  have hQap : (∫ z, (WMFKI.frobenius (discreteDictionaryDesign L N nt d M w τ Φ φ ψ (particleGrid N d nt τ Xp) z-
      continuousDictionaryDesign L N d M Φ φ ψ T Xp z))^2 ∂P.prod Pe) ≤ Q*e := by
    change (∫ z : Ω × Ξ, (fun ω => (WMFKI.frobenius (discreteDictionaryDesign L N nt d M w τ Φ φ ψ (particleGrid N d nt τ X) ω-
      continuousDictionaryDesign L N d M Φ φ ψ T X ω))^2) z.1 ∂P.prod Pe) ≤ Q*e
    rw [integral_fun_fst (fun ω => (WMFKI.frobenius (discreteDictionaryDesign L N nt d M w τ Φ φ ψ (particleGrid N d nt τ X) ω-
      continuousDictionaryDesign L N d M Φ φ ψ T X ω))^2)]
    simpa using hQa
  exact observed_assembly_full_pair_budget (P.prod Pe) L N nt d M hL hN R q hR hq D σ w τ W hw K hKc
    Φ hΦ θ hReal φ ψ (fun a => (hψc a).continuous) G H J C A B hG hH hJ hC hA hφ hψ hdψ hK hKl
    T Xp (fun z => half_process_real_continuous X hX.path z.1) rfl S Q e hrp hSp hqbp hQbp hqap hQap


end WMFKIJointAssembly
