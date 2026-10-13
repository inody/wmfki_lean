import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

namespace WMFKI

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω I : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [Fintype I]

/-- 独立標本の重み付き和の分散。原稿では観測軌道で条件付けた後に適用する形。 -/
theorem weighted_independent_variance (X : I → Ω → ℝ) (w : I → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hInd : Pairwise (fun i j => IndepFun (X i) (X j) μ)) :
    variance (fun ω => ∑ i, w i * X i ω) μ = ∑ i, w i ^ 2 * variance (X i) μ := by
  have hv := IndepFun.variance_sum (s := Finset.univ)
    (X := fun i ω => w i * X i ω)
    (fun i _ => (hX i).const_mul (w i))
    (by
      intro i _ j _ hij
      exact (hInd hij).comp (φ := fun x => w i * x) (ψ := fun x => w j * x)
        (by fun_prop) (by fun_prop))
  have heq : (fun ω => ∑ i, w i * X i ω) = ∑ i, (fun ω => w i * X i ω) := by
    funext ω
    simp
  rw [heq, hv]
  simp only [variance_const_mul]

/-- 各時刻P個の新しい独立標本を使うと、分散の重みはΣw²/Pになる。 -/
theorem refreshed_sampling_variance {T P : ℕ} (hP : 0 < P)
    (X : (Fin T × Fin P) → Ω → ℝ) (w : Fin T → ℝ) (C : ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hInd : Pairwise (fun i j => IndepFun (X i) (X j) μ))
    (hvar : ∀ i, variance (X i) μ ≤ C) :
    variance (fun ω => ∑ i : Fin T × Fin P, (w i.1 / P) * X i ω) μ ≤
      C * (∑ t, w t ^ 2) / P := by
  rw [weighted_independent_variance X (fun i => w i.1 / P) hX hInd]
  have hp : (P : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hP)
  calc
    _ ≤ ∑ i : Fin T × Fin P, (w i.1 / P) ^ 2 * C :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hvar i) (sq_nonneg _)
    _ = ∑ t : Fin T, (P : ℝ) * ((w t / P) ^ 2 * C) := by
      simp [Fintype.sum_prod_type]
    _ = C * (∑ t, w t ^ 2) / P := by
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro t _
      field_simp

end WMFKI
