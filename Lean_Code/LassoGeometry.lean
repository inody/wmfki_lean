import Lean_Code.LassoDefinitions
import Mathlib.Tactic

namespace WMFKI

open scoped BigOperators

variable {M : ℕ}

theorem partialL1_nonneg (S : Finset (Fin M)) (u : Coeff M) : 0 ≤ partialL1 S u :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem partialL1_decomp (S : Finset (Fin M)) (u : Coeff M) :
    partialL1 S u + partialL1 Sᶜ u = l1Norm u :=
  Finset.sum_add_sum_compl S (fun i => |u i|)

theorem partialL1_sq_le (S : Finset (Fin M)) (u : Coeff M) :
    partialL1 S u ^ 2 ≤ (S.card : ℝ) * ‖u‖ ^ 2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun i => |u i|)
  have hc' : partialL1 S u ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, u i ^ 2 := by
    simpa [partialL1, sq_abs] using hc
  have hs : (∑ i ∈ S, u i ^ 2) ≤ ‖u‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)
  exact hc'.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))

theorem l1_support_difference (S : Finset (Fin M)) (θ u : Coeff M)
    (hθ : ∀ i ∉ S, θ i = 0) :
    l1Norm θ - l1Norm (θ + u) ≤ partialL1 S u - partialL1 Sᶜ u := by
  have hs : partialL1 S θ ≤ partialL1 S (θ + u) + partialL1 S u := by
    unfold partialL1
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have h := abs_add_le (θ i + u i) (-u i)
    simpa using h
  have hz : partialL1 Sᶜ θ = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [hθ i (Finset.mem_compl.mp hi)]
  have hc : partialL1 Sᶜ (θ + u) = partialL1 Sᶜ u := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [hθ i (Finset.mem_compl.mp hi)]
  have h1 := partialL1_decomp S θ
  have h2 := partialL1_decomp S (θ + u)
  linarith

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem score_inner_bound (B : Coeff M →L[ℝ] F) (ξ : F) (lam : ℝ)
    (hscore : ScoreBound B ξ lam) (u : Coeff M) :
    inner ℝ (B u) ξ ≤ lam / 2 * l1Norm u := by
  rw [← B.adjoint_inner_right u ξ]
  simp only [PiLp.inner_apply, Real.inner_apply]
  rw [l1Norm, partialL1, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hs : |(B.adjoint ξ) i| ≤ lam / 2 := by linarith [hscore i]
  calc
    _ ≤ |(B.adjoint ξ) i| * |u i| := by
      simpa only [abs_mul, mul_comm] using le_abs_self ((B.adjoint ξ) i * u i)
    _ ≤ _ := mul_le_mul_of_nonneg_right hs (abs_nonneg _)

end WMFKI
