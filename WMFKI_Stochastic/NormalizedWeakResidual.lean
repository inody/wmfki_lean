import WMFKI_Stochastic.EmpiricalResidualEnergy
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

open MeasureTheory Set
open scoped BigOperators
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
namespace WMFKIExternalProbe

noncomputable def normalizedTestVector {Ω : Type*} (L : ℕ) (r : Fin L → Ω → ℝ)
    (ω : Ω) : EuclideanSpace ℝ (Fin L) :=
  WithLp.toLp 2 (fun a => (1/Real.sqrt (L : ℝ))*r a ω)

/-- Euclidean squared norms add coordinate energies, without requiring
independent rows. The empty-row case is also valid. -/
theorem normalized_test_vector_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (L : ℕ) (r : Fin L → Ω → ℝ) (hr : ∀ a, MemLp (r a) 2 P)
    (hmean : ∀ a, (∫ ω, r a ω ∂P) = 0)
    (v : Fin L → ℝ) (hv : ∀ a, (∫ ω, (r a ω)^2 ∂P) ≤ v a) :
    MemLp (normalizedTestVector L r) 2 P ∧
    (∫ ω, normalizedTestVector L r ω ∂P) = 0 ∧
    (∫ ω, ‖normalizedTestVector L r ω‖^2 ∂P) ≤ (1/(L : ℝ))*∑ a,v a := by
  have hV : MemLp (normalizedTestVector L r) 2 P := by
    apply MemLp.of_eval_piLp
    intro a
    exact (hr a).const_mul (1/Real.sqrt (L : ℝ))
  have hn ω : ‖normalizedTestVector L r ω‖^2 = (1/(L : ℝ))*∑ a,(r a ω)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ a, ((1/Real.sqrt (L : ℝ))*r a ω)^2) = _
    simp_rw [mul_pow]
    rw [←Finset.mul_sum,div_pow,one_pow,Real.sq_sqrt (Nat.cast_nonneg L)]
  refine ⟨hV,?_,?_⟩
  · ext a
    rw [eval_integral_piLp (fun a => (hV.eval_piLp a).integrable (by norm_num)) a]
    change (∫ ω, (1/Real.sqrt (L : ℝ))*r a ω ∂P) = 0
    rw [integral_const_mul,hmean a,mul_zero]
  · simp_rw [hn]
    rw [integral_const_mul,integral_finsetSum _ (fun a _ => (hr a).integrable_sq)]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => hv a))
      (one_div_nonneg.mpr (Nat.cast_nonneg L))

noncomputable def weakResidualVector {Ω : Type*} (L N d : ℕ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (σ : ℝ)
    (φ : Fin L → EuclideanSpace ℝ (Fin d) → ℝ) (ψ : Fin L → ℝ → ℝ) (T : ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ) : Ω → EuclideanSpace ℝ (Fin L) :=
  normalizedTestVector L (fun a => empiricalWeakResidual N d K σ (φ a) (ψ a) T X)

/-- The continuous-time latent residual vector, normalized exactly by
1/sqrt(L), is centered L2 with the averaged sigma^2/N budget. Every row uses
the same interacting trajectory and Brownian filtration; no row independence. -/
theorem weak_residual_vector_energy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (L N d : ℕ) (hN : 0 < N) (B : BrownianSystem P (N*d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : Continuous K)
    (σ : ℝ) (ξ : Ω → Fin (N*d) → ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hX : VectorSDESolution P B.F B.W (particleCoordinateDrift N d K)
      (fun i j _ => if i=j then σ else 0) ξ X)
    (φ : Fin L → EuclideanSpace ℝ (Fin d) → ℝ) (hφ : ∀ a, ContDiff ℝ 2 (φ a))
    (G : Fin L → ℝ) (hbound : ∀ a x, ‖gradient (φ a) x‖ ≤ G a)
    (ψ : Fin L → ℝ → ℝ) (hψ : ∀ a, ContDiff ℝ 1 (ψ a)) (T : ℝ) (hT : 0 ≤ T)
    (hψ0 : ∀ a, ψ a 0 = 0) (hψT : ∀ a, ψ a T = 0) :
    MemLp (weakResidualVector L N d K σ φ ψ T X) 2 P ∧
    (∫ ω, weakResidualVector L N d K σ φ ψ T X ω ∂P) = 0 ∧
    (∫ ω, ‖weakResidualVector L N d K σ φ ψ T X ω‖^2 ∂P) ≤
      (σ^2/(N : ℝ))*((∑ a, (G a)^2*(∫ s in 0..T, (ψ a s)^2))/(L : ℝ)) := by
  have hrow a := empirical_weak_residual_energy P N d hN B K hK σ ξ X hX
    (φ a) (hφ a) (G a) (hbound a) (ψ a) (hψ a) T hT (hψ0 a) (hψT a)
  choose M hM hMI hS he hr hm hv using hrow
  obtain ⟨hV,hmean,hboundV⟩ := normalized_test_vector_moments P L _ hr hm _ hv
  refine ⟨hV,hmean,?_⟩
  convert hboundV using 1
  · rfl
  · simp_rw [mul_assoc,←Finset.mul_sum]
    ring

end WMFKIExternalProbe
