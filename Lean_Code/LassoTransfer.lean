import Lean_Code.LassoDeterministic

namespace WMFKI

variable {M : ℕ} {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem coneLowerBound_perturb (A B : Coeff M →L[ℝ] F) (S : Finset (Fin M))
    (γ r : ℝ) (hA : ConeLowerBound A S γ) (hpert : ‖B - A‖ ≤ r) :
    ConeLowerBound B S (γ - r) := by
  intro u hu
  have htri : ‖A u‖ ≤ ‖B u‖ + ‖(B - A) u‖ := by
    calc
      ‖A u‖ = ‖B u - (B - A) u‖ := by simp
      _ ≤ _ := norm_sub_le _ _
  have hop := (B - A).le_opNorm u
  have hmul := mul_le_mul_of_nonneg_right hpert (norm_nonneg u)
  have hlo := hA u hu
  nlinarith

omit [CompleteSpace F] in
theorem columnBound_perturb (A B : Coeff M →L[ℝ] F) (R r : ℝ)
    (hA : ColumnBound A R) (hpert : ‖B - A‖ ≤ r) : ColumnBound B (R + r) := by
  intro i
  let e := EuclideanSpace.single i (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  have hop := (B - A).le_opNorm e
  rw [he, mul_one] at hop
  have htri : ‖B e‖ ≤ ‖A e‖ + ‖(B - A) e‖ := by
    calc
      ‖B e‖ = ‖A e + (B - A) e‖ := by simp
      _ ≤ _ := norm_add_le _ _
  have hcol := hA i
  change ‖A e‖ ≤ R at hcol
  change ‖B e‖ ≤ R + r
  linarith

theorem score_of_column_and_residual (B : Coeff M →L[ℝ] F) (ξ : F)
    (R r lam : ℝ) (hR : 0 ≤ R) (hcol : ColumnBound B R) (hres : ‖ξ‖ ≤ r)
    (hpen : 2 * R * r ≤ lam) : ScoreBound B ξ lam := by
  intro i
  let e := EuclideanSpace.single i (1 : ℝ)
  have heq : (B.adjoint ξ) i = inner ℝ (B e) ξ := by
    simpa [e, EuclideanSpace.inner_single_left] using B.adjoint_inner_right e ξ
  have hcs := abs_real_inner_le_norm (B e) ξ
  have hmul := mul_le_mul (hcol i) hres (norm_nonneg ξ) hR
  rw [heq]
  change ‖B e‖ * ‖ξ‖ ≤ R * r at hmul
  linarith

end WMFKI
