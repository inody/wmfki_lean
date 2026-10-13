import WMFKI_Stochastic.ObservedWeakPerturbations

open MeasureTheory Set
open scoped BigOperators
namespace WMFKIExternalProbe

noncomputable def discreteResponseVector {Ω : Type*} (L N nt d : ℕ) (σ : ℝ)
    (w τ : Fin nt → ℝ) (φ : Fin L → EuclideanSpace ℝ (Fin d) → ℝ) (ψ : Fin L → ℝ → ℝ)
    (x : Fin nt → Fin N → Ω → EuclideanSpace ℝ (Fin d)) : Ω → EuclideanSpace ℝ (Fin L) :=
  normalizedTestVector L (fun a => discreteWeakResponse N nt d σ w τ (φ a) (ψ a) x)

noncomputable def discreteKernelVector {Ω : Type*} (L N nt d : ℕ)
    (w τ : Fin nt → ℝ) (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (φ : Fin L → EuclideanSpace ℝ (Fin d) → ℝ) (ψ : Fin L → ℝ → ℝ)
    (x : Fin nt → Fin N → Ω → EuclideanSpace ℝ (Fin d)) : Ω → EuclideanSpace ℝ (Fin L) :=
  normalizedTestVector L (fun a => discreteKernelDesign N nt d w τ K (φ a) (ψ a) x)

noncomputable def responseObservationConstant (d : ℕ) (σ W B G J : ℝ) : ℝ :=
  W^2*(B*(G+(σ^2/2)*((d : ℝ)*J)))^2
noncomputable def kernelObservationConstant (W B G H C A R : ℝ) : ℝ :=
  W^2*B^2*(6*(H*C)^2*(1+2*R)+8*(G*A)^2)

theorem normalized_test_vector_sub {Ω : Type*} (L : ℕ) (f g : Fin L → Ω → ℝ) :
    (fun ω => normalizedTestVector L f ω-normalizedTestVector L g ω) =
      normalizedTestVector L (fun a ω => f a ω-g a ω) := by
  funext ω
  ext a
  simp [normalizedTestVector,mul_sub]

/-- Actual response and true-kernel design perturbations. Constants are
uniform in the particle count, number of tests and time grid under a stable
absolute weight sum; no inverse mesh size or independence across errors. -/
theorem observed_weak_vector_perturbations
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (L N nt d : ℕ) [MeasurableSpace (EuclideanSpace ℝ (Fin d))] [BorelSpace (EuclideanSpace ℝ (Fin d))]
    (hL : 0 < L) (hN : 0 < N) (R q : ℝ) (hR : 0 ≤ R) (hq : 0 ≤ q)
    (D : ObservationSamples (E := EuclideanSpace ℝ (Fin d)) P N nt R q)
    (σ : ℝ) (w τ : Fin nt → ℝ) (W : ℝ) (hw : (∑ t,|w t|) ≤ W)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hKm : Measurable K)
    (φ : Fin L → EuclideanSpace ℝ (Fin d) → ℝ) (ψ : Fin L → ℝ → ℝ)
    (G H J C A B : ℝ) (hG : 0 ≤ G) (hH : 0 ≤ H) (hJ : 0 ≤ J) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hφ : ∀ a, C3TestBounds d (φ a) G H J)
    (hψ : ∀ a t, |ψ a (τ t)| ≤ B) (hdψ : ∀ a t, |deriv (ψ a) (τ t)| ≤ B)
    (hK : ∀ x, ‖K x‖ ≤ C*(1+‖x‖)) (hKl : ∀ x y, ‖K x-K y‖ ≤ A*‖x-y‖) :
    let Y := fun t i ω => D.pos t i ω+D.noise t i ω
    let Eb := fun ω => discreteResponseVector L N nt d σ w τ φ ψ Y ω-discreteResponseVector L N nt d σ w τ φ ψ D.pos ω
    let Ek := fun ω => discreteKernelVector L N nt d w τ K φ ψ Y ω-discreteKernelVector L N nt d w τ K φ ψ D.pos ω
    (MemLp Eb 2 P ∧ (∫ ω,‖Eb ω‖^2 ∂P) ≤ responseObservationConstant d σ W B G J*q) ∧
    (MemLp Ek 2 P ∧ (∫ ω,‖Ek ω‖^2 ∂P) ≤ kernelObservationConstant W B G H C A R*q) := by
  dsimp only
  have hW0 : 0 ≤ W := (Finset.sum_nonneg (fun t _ => abs_nonneg (w t))).trans hw
  have hw2 := (sq_le_sq₀ (Finset.sum_nonneg (fun t _ => abs_nonneg (w t))) hW0).mpr hw
  have hb a := discrete_response_observation_moment P N nt d R q D hN σ w τ (φ a) (ψ a)
    G H J B hG hJ (hφ a) (hψ a) (hdψ a)
  have hk a := discrete_kernel_observation_moment P N nt d R q D hN hq hR w τ K hKm
    (φ a) (ψ a) G H J C A B hG hH hC hA (hφ a) (hψ a) hK hKl
  have hb' a : (∫ ω,(discreteWeakResponse N nt d σ w τ (φ a) (ψ a) (fun t i ω => D.pos t i ω+D.noise t i ω) ω-
      discreteWeakResponse N nt d σ w τ (φ a) (ψ a) D.pos ω)^2 ∂P) ≤ responseObservationConstant d σ W B G J*q := by
    apply (hb a).2.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw2 (sq_nonneg _)) hq
  have hk' a : (∫ ω,(discreteKernelDesign N nt d w τ K (φ a) (ψ a) (fun t i ω => D.pos t i ω+D.noise t i ω) ω-
      discreteKernelDesign N nt d w τ K (φ a) (ψ a) D.pos ω)^2 ∂P) ≤ kernelObservationConstant W B G H C A R*q := by
    apply (hk a).2.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw2 (sq_nonneg B)) (by positivity)) hq
  have hbr := normalized_vector_second_moment P L _ (fun a => (hb a).1) _ hb' hL
  have hkr := normalized_vector_second_moment P L _ (fun a => (hk a).1) _ hk' hL
  simpa only [discreteResponseVector,discreteKernelVector,←normalized_test_vector_sub] using And.intro hbr hkr

end WMFKIExternalProbe
