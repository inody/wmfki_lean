import WMFKI_Stochastic.QuadratureResidualBudget

open MeasureTheory Set
open scoped BigOperators
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
namespace WMFKIExternalProbe

noncomputable def particleGrid {Ω : Type*} (N d nt : ℕ) (τ : Fin nt → ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ) : Fin nt → Fin N → Ω → EuclideanSpace ℝ (Fin d) :=
  fun t i ω => particlePositions N d (X (realTimeClamp (τ t)) ω) i

noncomputable def continuousResponseVector {Ω : Type*} (L N d : ℕ) (σ : ℝ)
    (φ : Fin L → EuclideanSpace ℝ (Fin d) → ℝ) (ψ : Fin L → ℝ → ℝ) (T : ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ) : Ω → EuclideanSpace ℝ (Fin L) :=
  normalizedTestVector L (fun a ω =>
    -(∫ s in 0..T, deriv (ψ a) s*empiricalObservable N d (φ a) (X (realTimeClamp s) ω)) -
    (σ^2/2)*(∫ s in 0..T, ψ a s*empiricalLaplacian N d (φ a) (X (realTimeClamp s) ω)))

noncomputable def continuousKernelVector {Ω : Type*} (L N d : ℕ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (φ : Fin L → EuclideanSpace ℝ (Fin d) → ℝ) (ψ : Fin L → ℝ → ℝ) (T : ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ) : Ω → EuclideanSpace ℝ (Fin L) :=
  normalizedTestVector L (fun a ω => ∫ s in 0..T,
    ψ a s*empiricalPairInteraction N d K (φ a) (X (realTimeClamp s) ω))

theorem weak_residual_vector_response_sub_kernel {Ω : Type*} (L N d : ℕ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (σ : ℝ)
    (φ : Fin L → EuclideanSpace ℝ (Fin d) → ℝ) (ψ : Fin L → ℝ → ℝ) (T : ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ) (ω : Ω) :
    weakResidualVector L N d K σ φ ψ T X ω =
      continuousResponseVector L N d σ φ ψ T X ω-continuousKernelVector L N d K φ ψ T X ω := by
  ext a
  simp [weakResidualVector,continuousResponseVector,continuousKernelVector,
    normalizedTestVector,empiricalWeakResidual,mul_sub]

end WMFKIExternalProbe
