import WMFKI_Stochastic.ContinuousWeakVectors

open MeasureTheory Set
open scoped BigOperators
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
namespace WMFKIExternalProbe

noncomputable def configurationKernelFunctional (N d : ℕ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (x : Fin N → EuclideanSpace ℝ (Fin d)) :
    (EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] ℝ :=
  ((N : ℝ)⁻¹^2) • ∑ i, ∑ j, if i=j then 0 else
    (innerSL ℝ (gradient φ (x i))).toLinearMap.comp (LinearMap.proj (x i-x j))

theorem configuration_kernel_apply (N d : ℕ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (x : Fin N → EuclideanSpace ℝ (Fin d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    configurationKernelFunctional N d φ x K =
      ((N : ℝ)⁻¹^2)*∑ i, ∑ j, if i=j then 0 else inner ℝ (gradient φ (x i)) (K (x i-x j)) := by
  classical
  simp only [configurationKernelFunctional,LinearMap.smul_apply,LinearMap.sum_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i=j <;> simp [h]

theorem configuration_kernel_realizable (N d M : ℕ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (x : Fin N → EuclideanSpace ℝ (Fin d))
    (Φ : Fin M → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (θ : Fin M → ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : ∀ z, ∑ m, θ m • Φ m z = K z) :
    configurationKernelFunctional N d φ x K = ∑ m, θ m*configurationKernelFunctional N d φ x (Φ m) := by
  have he : K = ∑ m, θ m • Φ m := by funext z; simpa using (hK z).symm
  rw [he,map_sum]
  simp only [map_smul,smul_eq_mul]

theorem empirical_pair_kernel_realizable (N d M : ℕ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (x : Fin (N*d) → ℝ)
    (Φ : Fin M → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (θ : Fin M → ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : ∀ z, ∑ m, θ m • Φ m z = K z) :
    empiricalPairInteraction N d K φ x = ∑ m, θ m*empiricalPairInteraction N d (Φ m) φ x := by
  simpa only [configuration_kernel_apply,empiricalPairInteraction] using
    configuration_kernel_realizable N d M φ (particlePositions N d x) Φ θ K hK

theorem discrete_kernel_functional {Ω : Type*} (N nt d : ℕ) (w τ : Fin nt → ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (ψ : ℝ → ℝ)
    (x : Fin nt → Fin N → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    discreteKernelDesign N nt d w τ K φ ψ x ω =
      ∑ t, w t*ψ (τ t)*configurationKernelFunctional N d φ (fun i => x t i ω) K := by
  classical
  have hi (i j : Fin N) (a c : ℝ) : (if i=j then 0 else c*a) = c*(if i=j then 0 else a) := by
    by_cases h : i=j <;> simp [h]
  simp only [discreteKernelDesign,pairTimeAverage,configuration_kernel_apply,hi,←Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem discrete_kernel_realizable {Ω : Type*} (N nt d M : ℕ) (w τ : Fin nt → ℝ)
    (Φ : Fin M → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (θ : Fin M → ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : ∀ z, ∑ m, θ m • Φ m z = K z)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (ψ : ℝ → ℝ)
    (x : Fin nt → Fin N → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    discreteKernelDesign N nt d w τ K φ ψ x ω =
      ∑ m, θ m*discreteKernelDesign N nt d w τ (Φ m) φ ψ x ω := by
  rw [discrete_kernel_functional]
  simp_rw [configuration_kernel_realizable N d M φ _ Φ θ K hK,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [discrete_kernel_functional,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

noncomputable def discreteDictionaryDesign {Ω : Type*} (L N nt d M : ℕ)
    (w τ : Fin nt → ℝ) (Φ : Fin M → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (φ : Fin L → EuclideanSpace ℝ (Fin d) → ℝ) (ψ : Fin L → ℝ → ℝ)
    (x : Fin nt → Fin N → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) : Matrix (Fin L) (Fin M) ℝ :=
  fun a m => discreteKernelVector L N nt d w τ (Φ m) φ ψ x ω a

noncomputable def continuousDictionaryDesign {Ω : Type*} (L N d M : ℕ)
    (Φ : Fin M → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (φ : Fin L → EuclideanSpace ℝ (Fin d) → ℝ) (ψ : Fin L → ℝ → ℝ) (T : ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ) (ω : Ω) : Matrix (Fin L) (Fin M) ℝ :=
  fun a m => continuousKernelVector L N d (Φ m) φ ψ T X ω a

theorem discrete_dictionary_realizable {Ω : Type*} (L N nt d M : ℕ) (w τ : Fin nt → ℝ)
    (Φ : Fin M → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin M))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : ∀ z, ∑ m, θ m • Φ m z = K z)
    (φ : Fin L → EuclideanSpace ℝ (Fin d) → ℝ) (ψ : Fin L → ℝ → ℝ)
    (x : Fin nt → Fin N → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    WMFKI.matrixMap (discreteDictionaryDesign L N nt d M w τ Φ φ ψ x ω) θ =
      discreteKernelVector L N nt d w τ K φ ψ x ω := by
  ext a
  simp only [WMFKI.matrixMap_apply,discreteDictionaryDesign,discreteKernelVector,normalizedTestVector]
  change (∑ m, ((1/Real.sqrt (L : ℝ))*discreteKernelDesign N nt d w τ (Φ m) (φ a) (ψ a) x ω)*θ m) = _
  rw [discrete_kernel_realizable N nt d M w τ Φ θ K hK,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem continuous_dictionary_realizable {Ω : Type*} (L N d M : ℕ)
    (Φ : Fin M → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hΦ : ∀ m, Continuous (Φ m))
    (θ : EuclideanSpace ℝ (Fin M))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : ∀ z, ∑ m, θ m • Φ m z = K z)
    (φ : Fin L → EuclideanSpace ℝ (Fin d) → ℝ) (hφ : ∀ a, ContDiff ℝ 2 (φ a))
    (ψ : Fin L → ℝ → ℝ) (hψ : ∀ a, Continuous (ψ a)) (T : ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hX : ∀ ω, Continuous (fun s : ℝ => X (realTimeClamp s) ω)) (ω : Ω) :
    WMFKI.matrixMap (continuousDictionaryDesign L N d M Φ φ ψ T X ω) θ =
      continuousKernelVector L N d K φ ψ T X ω := by
  have hlin a : (∫ s in 0..T, ψ a s*empiricalPairInteraction N d K (φ a) (X (realTimeClamp s) ω)) =
      ∑ m, θ m*(∫ s in 0..T, ψ a s*empiricalPairInteraction N d (Φ m) (φ a) (X (realTimeClamp s) ω)) := by
    have hi m : IntervalIntegrable (fun s => ψ a s*empiricalPairInteraction N d (Φ m) (φ a) (X (realTimeClamp s) ω)) volume 0 T :=
      ((hψ a).mul ((empirical_pair_laplacian_continuous N d (Φ m) (hΦ m) (φ a) (hφ a)).1.comp (hX ω))).intervalIntegrable 0 T
    have he s : ψ a s*empiricalPairInteraction N d K (φ a) (X (realTimeClamp s) ω) =
        ∑ m, θ m*(ψ a s*empiricalPairInteraction N d (Φ m) (φ a) (X (realTimeClamp s) ω)) := by
      rw [empirical_pair_kernel_realizable N d M (φ a) _ Φ θ K hK,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    simp_rw [he]
    rw [intervalIntegral.integral_finsetSum (fun m _ => (hi m).const_mul (θ m))]
    simp only [intervalIntegral.integral_const_mul]
  ext a
  simp only [WMFKI.matrixMap_apply,continuousDictionaryDesign,continuousKernelVector,normalizedTestVector]
  change (∑ m, ((1/Real.sqrt (L : ℝ))*(∫ s in 0..T, ψ a s*empiricalPairInteraction N d (Φ m) (φ a) (X (realTimeClamp s) ω)))*θ m) = _
  rw [hlin a,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

end WMFKIExternalProbe
