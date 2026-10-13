import WMFKI_Stochastic.KernelDictionaryLinearity

open MeasureTheory Set
open scoped BigOperators
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
namespace WMFKIExternalProbe

/-- Explicit assembly interface: the continuous residual energy is supplied by
`weak_residual_vector_energy`; the only accuracy inputs are the manuscript's
separate response and Frobenius-design RMS quadrature assumptions. Observation
perturbation bounds and the coefficient direction are conclusions, not inputs. -/
theorem observed_assembly_full_pair_budget
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (L N nt d M : ℕ) [MeasurableSpace (EuclideanSpace ℝ (Fin d))] [BorelSpace (EuclideanSpace ℝ (Fin d))]
    (hL : 0 < L) (hN : 0 < N) (R q : ℝ) (hR : 0 ≤ R) (hq : 0 ≤ q)
    (D : ObservationSamples (E := EuclideanSpace ℝ (Fin d)) P N nt R q)
    (σ : ℝ) (w τ : Fin nt → ℝ) (W : ℝ) (hw : (∑ t,|w t|) ≤ W)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hKc : Continuous K)
    (Φ : Fin M → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hΦ : ∀ m, Continuous (Φ m))
    (θ : EuclideanSpace ℝ (Fin M)) (hReal : ∀ z, ∑ m, θ m • Φ m z = K z)
    (φ : Fin L → EuclideanSpace ℝ (Fin d) → ℝ) (ψ : Fin L → ℝ → ℝ) (hψc : ∀ a, Continuous (ψ a))
    (G H J C A B : ℝ) (hG : 0 ≤ G) (hH : 0 ≤ H) (hJ : 0 ≤ J) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hφ : ∀ a, C3TestBounds d (φ a) G H J)
    (hψ : ∀ a t, |ψ a (τ t)| ≤ B) (hdψ : ∀ a t, |deriv (ψ a) (τ t)| ≤ B)
    (hK : ∀ x, ‖K x‖ ≤ C*(1+‖x‖)) (hKl : ∀ x y, ‖K x-K y‖ ≤ A*‖x-y‖)
    (T : ℝ) (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hXc : ∀ ω, Continuous (fun s : ℝ => X (realTimeClamp s) ω))
    (hpos : D.pos = particleGrid N d nt τ X)
    (S Q e : ℝ)
    (hr : MemLp (weakResidualVector L N d K σ φ ψ T X) 2 P)
    (hS : (∫ ω, ‖weakResidualVector L N d K σ φ ψ T X ω‖^2 ∂P) ≤ S)
    (hqb : MemLp (fun ω => discreteResponseVector L N nt d σ w τ φ ψ (particleGrid N d nt τ X) ω-
      continuousResponseVector L N d σ φ ψ T X ω) 2 P)
    (hQb : (∫ ω, ‖discreteResponseVector L N nt d σ w τ φ ψ (particleGrid N d nt τ X) ω-
      continuousResponseVector L N d σ φ ψ T X ω‖^2 ∂P) ≤ Q*e)
    (hqa : MemLp (fun ω => (WithLp.toLp 2 (fun ij : Fin L × Fin M =>
      (discreteDictionaryDesign L N nt d M w τ Φ φ ψ (particleGrid N d nt τ X) ω-
        continuousDictionaryDesign L N d M Φ φ ψ T X ω) ij.1 ij.2) : EuclideanSpace ℝ (Fin L × Fin M))) 2 P)
    (hQa : (∫ ω, (WMFKI.frobenius (discreteDictionaryDesign L N nt d M w τ Φ φ ψ (particleGrid N d nt τ X) ω-
      continuousDictionaryDesign L N d M Φ φ ψ T X ω))^2 ∂P) ≤ Q*e) :
    let Y := fun t i ω => particleGrid N d nt τ X t i ω+D.noise t i ω
    let rY := fun ω => discreteResponseVector L N nt d σ w τ φ ψ Y ω-
      WMFKI.matrixMap (discreteDictionaryDesign L N nt d M w τ Φ φ ψ Y ω) θ
    MemLp rY 2 P ∧ (∫ ω, ‖rY ω‖^2 ∂P) ≤ 6*S+12*Q*(1+‖θ‖^2)*e+
      3*(responseObservationConstant d σ W B G J+kernelObservationConstant W B G H C A R)*q := by
  let x := particleGrid N d nt τ X
  let Y := fun t i ω => x t i ω+D.noise t i ω
  let bd := discreteResponseVector L N nt d σ w τ φ ψ x
  let bc := continuousResponseVector L N d σ φ ψ T X
  let kd := discreteKernelVector L N nt d w τ K φ ψ x
  let kc := continuousKernelVector L N d K φ ψ T X
  let bys := discreteResponseVector L N nt d σ w τ φ ψ Y
  let kys := discreteKernelVector L N nt d w τ K φ ψ Y
  have hφ2 a : ContDiff ℝ 2 (φ a) := (hφ a).smooth.of_le (by norm_num)
  have hobs := observed_weak_vector_perturbations P L N nt d hL hN R q hR hq D σ w τ W hw K hKc.measurable
    φ ψ G H J C A B hG hH hJ hC hA hφ hψ hdψ hK hKl
  simp only [hpos] at hobs
  have hdir := matrix_quadrature_direction_moment P L M
    (fun ω => discreteDictionaryDesign L N nt d M w τ Φ φ ψ x ω-continuousDictionaryDesign L N d M Φ φ ψ T X ω)
    hqa (Q*e) hQa θ
  have hdirEq ω : WMFKI.matrixMap (discreteDictionaryDesign L N nt d M w τ Φ φ ψ x ω-
      continuousDictionaryDesign L N d M Φ φ ψ T X ω) θ = kd ω-kc ω := by
    rw [WMFKI.matrixMap_sub]
    change WMFKI.matrixMap (discreteDictionaryDesign L N nt d M w τ Φ φ ψ x ω) θ-
      WMFKI.matrixMap (continuousDictionaryDesign L N d M Φ φ ψ T X ω) θ = _
    rw [discrete_dictionary_realizable L N nt d M w τ Φ θ K hReal φ ψ x ω,
      continuous_dictionary_realizable L N d M Φ hΦ θ K hReal φ hφ2 ψ hψc T X hXc ω]
  simp_rw [hdirEq] at hdir
  have hQk : (∫ ω, ‖kd ω-kc ω‖^2 ∂P) ≤ Q*‖θ‖^2*e := by
    calc
      _ ≤ (Q*e)*‖θ‖^2 := hdir.2
      _ = _ := by ring
  have hc := observed_residual_error_composition P (weakResidualVector L N d K σ φ ψ T X)
    (fun ω => bd ω-bc ω) (fun ω => kd ω-kc ω) (fun ω => bys ω-bd ω) (fun ω => kys ω-kd ω)
    hr hqb hdir.1 hobs.1.1 hobs.2.1 S Q (‖θ‖^2) e
    (responseObservationConstant d σ W B G J) (kernelObservationConstant W B G H C A R) q
    hS hQb hQk hobs.1.2 hobs.2.2
  have he ω : discreteResponseVector L N nt d σ w τ φ ψ Y ω-
      WMFKI.matrixMap (discreteDictionaryDesign L N nt d M w τ Φ φ ψ Y ω) θ =
      (weakResidualVector L N d K σ φ ψ T X ω+(bd ω-bc ω)-(kd ω-kc ω))+(bys ω-bd ω)-(kys ω-kd ω) := by
    rw [discrete_dictionary_realizable L N nt d M w τ Φ θ K hReal φ ψ Y ω,
      weak_residual_vector_response_sub_kernel]
    dsimp only [bd,bc,kd,kc,bys,kys]
    abel
  simpa only [←he] using hc

/-- Actual-particle endpoint for the full observed, discretized residual.
Second moments/independence are primitive sample data; continuous stochastic
energy is derived here from the supplied actual SDE, not postulated. -/
theorem particle_observed_full_pair_budget
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (L N nt d M : ℕ) [MeasurableSpace (EuclideanSpace ℝ (Fin d))] [BorelSpace (EuclideanSpace ℝ (Fin d))]
    (hL : 0 < L) (hN : 0 < N) (R q : ℝ) (hR : 0 ≤ R) (hq : 0 ≤ q)
    (D : ObservationSamples (E := EuclideanSpace ℝ (Fin d)) P N nt R q)
    (σ : ℝ) (w τ : Fin nt → ℝ) (W : ℝ) (hw : (∑ t,|w t|) ≤ W)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hKc : Continuous K)
    (Φ : Fin M → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hΦ : ∀ m, Continuous (Φ m))
    (θ : EuclideanSpace ℝ (Fin M)) (hReal : ∀ z, ∑ m, θ m • Φ m z = K z)
    (φ : Fin L → EuclideanSpace ℝ (Fin d) → ℝ) (ψ : Fin L → ℝ → ℝ) (hψc : ∀ a, ContDiff ℝ 1 (ψ a))
    (G H J C A B : ℝ) (hG : 0 ≤ G) (hH : 0 ≤ H) (hJ : 0 ≤ J) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hφ : ∀ a, C3TestBounds d (φ a) G H J)
    (hψ : ∀ a t, |ψ a (τ t)| ≤ B) (hdψ : ∀ a t, |deriv (ψ a) (τ t)| ≤ B)
    (hK : ∀ x, ‖K x‖ ≤ C*(1+‖x‖)) (hKl : ∀ x y, ‖K x-K y‖ ≤ A*‖x-y‖)
    (T : ℝ) (hT : 0 ≤ T) (hψ0 : ∀ a, ψ a 0 = 0) (hψT : ∀ a, ψ a T = 0)
    (Bsys : BrownianSystem P (N*d)) (ξ : Ω → Fin (N*d) → ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hX : VectorSDESolution P Bsys.F Bsys.W (particleCoordinateDrift N d K)
      (fun i j _ => if i=j then σ else 0) ξ X)
    (hpos : D.pos = particleGrid N d nt τ X)
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
    let Y := fun t i ω => particleGrid N d nt τ X t i ω+D.noise t i ω
    let rY := fun ω => discreteResponseVector L N nt d σ w τ φ ψ Y ω-
      WMFKI.matrixMap (discreteDictionaryDesign L N nt d M w τ Φ φ ψ Y ω) θ
    MemLp rY 2 P ∧ (∫ ω, ‖rY ω‖^2 ∂P) ≤ 6*((σ^2/(N : ℝ))*Γ)+12*Q*(1+‖θ‖^2)*e+
      3*(responseObservationConstant d σ W B G J+kernelObservationConstant W B G H C A R)*q := by
  have hφ2 a : ContDiff ℝ 2 (φ a) := (hφ a).smooth.of_le (by norm_num)
  obtain ⟨hr,_,hS⟩ := weak_residual_vector_energy P L N d hN Bsys K hKc σ ξ X hX φ hφ2
    (fun _ => G) (fun a => (hφ a).observation_bounds.1) ψ hψc T hT hψ0 hψT
  exact observed_assembly_full_pair_budget P L N nt d M hL hN R q hR hq D σ w τ W hw K hKc
    Φ hΦ θ hReal φ ψ (fun a => (hψc a).continuous) G H J C A B hG hH hJ hC hA hφ hψ hdψ hK hKl
    T X (half_process_real_continuous X hX.path) hpos _ Q e hr hS hqb hQb hqa hQa

/-- The averaged continuous energy constant has no hidden growth in L. -/
theorem averaged_time_energy_bound (L : ℕ) (hL : 0 < L) (G B T : ℝ)
    (hB : 0 ≤ B) (hT : 0 ≤ T) (ψ : Fin L → ℝ → ℝ) (hψ : ∀ a, Continuous (ψ a))
    (hb : ∀ a t, t ∈ Icc 0 T → |ψ a t| ≤ B) :
    0 ≤ (∑ a, G^2*(∫ s in 0..T, (ψ a s)^2))/(L : ℝ) ∧
    (∑ a, G^2*(∫ s in 0..T, (ψ a s)^2))/(L : ℝ) ≤ G^2*T*B^2 := by
  have hi0 a : 0 ≤ ∫ s in 0..T, (ψ a s)^2 := intervalIntegral.integral_nonneg hT (fun _ _ => sq_nonneg _)
  have hib a : (∫ s in 0..T, (ψ a s)^2) ≤ T*B^2 := by
    have hh := intervalIntegral.integral_mono_on hT ((hψ a).pow 2 |>.intervalIntegrable 0 T)
      (continuous_const.intervalIntegrable 0 T : IntervalIntegrable (fun _ : ℝ => B^2) volume 0 T)
      (fun s hs => by simpa only [Pi.pow_apply,sq_abs] using (sq_le_sq₀ (abs_nonneg (ψ a s)) hB).mpr (hb a s hs))
    simpa only [Pi.pow_apply,intervalIntegral.integral_const,sub_zero,smul_eq_mul] using hh
  refine ⟨div_nonneg (Finset.sum_nonneg (fun a _ => mul_nonneg (sq_nonneg G) (hi0 a))) (Nat.cast_nonneg L),?_⟩
  apply (div_le_iff₀ (by exact_mod_cast hL : (0 : ℝ) < L)).mpr
  calc
    _ ≤ ∑ _a : Fin L, G^2*(T*B^2) := Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hib a) (sq_nonneg G))
    _ = _ := by simp; ring

end WMFKIExternalProbe
