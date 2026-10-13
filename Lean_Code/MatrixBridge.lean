import Lean_Code.Deterministic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Matrix.Normed

namespace WMFKI

open scoped BigOperators

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

noncomputable def matrixMap (A : Matrix m n ℝ) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)

noncomputable def frobenius (A : Matrix m n ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, A i j ^ 2)

@[simp] theorem matrixMap_apply (A : Matrix m n ℝ) (u : EuclideanSpace ℝ n) (i : m) :
    matrixMap A u i = ∑ j, A i j * u j := rfl

theorem matrixMap_norm_le_frobenius (A : Matrix m n ℝ) : ‖matrixMap A‖ ≤ frobenius A := by
  have hn : 0 ≤ ∑ i, ∑ j, A i j ^ 2 := by positivity
  apply (matrixMap A).opNorm_le_bound (Real.sqrt_nonneg _)
  intro u
  have hs : ‖matrixMap A u‖ ^ 2 ≤ (∑ i, ∑ j, A i j ^ 2) * ‖u‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    change (∑ i, (∑ j, A i j * u j) ^ 2) ≤ _
    calc
      _ ≤ ∑ i, (∑ j, A i j ^ 2) * (∑ j, u j ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) u
      _ = _ := (Finset.sum_mul _ _ _).symm
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [frobenius, mul_pow, Real.sq_sqrt hn] using hs

omit [DecidableEq n] in
theorem frobenius_restrict_columns (A : Matrix m n ℝ) (S : Finset n) :
    frobenius (A.submatrix id (fun j : S => (j : n))) ≤ frobenius A := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  change (∑ j : S, A i (j : n) ^ 2) ≤ ∑ j, A i j ^ 2
  rw [Finset.sum_coe_sort S (fun j => A i j ^ 2)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun j _ _ => sq_nonneg _)

theorem matrixMap_restrict_norm_le (A : Matrix m n ℝ) (S : Finset n) :
    ‖matrixMap (A.submatrix id (fun j : S => (j : n)))‖ ≤ frobenius A :=
  (matrixMap_norm_le_frobenius _).trans (frobenius_restrict_columns A S)

@[simp] theorem matrixMap_sub (A C : Matrix m n ℝ) :
    matrixMap (A - C) = matrixMap A - matrixMap C := by
  ext u i
  simp [matrixMap_apply, sub_mul, Finset.sum_sub_distrib]

theorem matrixMap_transpose [DecidableEq m] (A : Matrix m n ℝ) :
    matrixMap A.transpose = (matrixMap A).adjoint := by
  change (Matrix.toEuclideanLin A.transpose).toContinuousLinearMap =
    (Matrix.toEuclideanLin A).toContinuousLinearMap.adjoint
  rw [← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  simp

omit [DecidableEq n] in
/-- 行列のFrobeniusノルムは、全成分を並べたEuclideanベクトルのノルム。 -/
theorem frobenius_eq_vector_norm (A : Matrix m n ℝ) :
    frobenius A = ‖(WithLp.toLp 2 (fun ij : m × n => A ij.1 ij.2) :
      EuclideanSpace ℝ (m × n))‖ := by
  simp [frobenius, EuclideanSpace.norm_eq, Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs]

end WMFKI
