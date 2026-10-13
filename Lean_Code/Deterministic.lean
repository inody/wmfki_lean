import Lean_Code.Definitions
import Mathlib.Tactic

namespace WMFKI

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem lowerBound_perturb (A B : E →L[ℝ] F) (γ r : ℝ)
    (hA : LowerBound A γ) (hpert : ‖B - A‖ ≤ r) : LowerBound B (γ - r) := by
  intro u
  have htri : ‖A u‖ ≤ ‖B u‖ + ‖(B - A) u‖ := by
    calc
      ‖A u‖ = ‖B u - (B - A) u‖ := by simp
      _ ≤ ‖B u‖ + ‖(B - A) u‖ := norm_sub_le _ _
  have hop := (B - A).le_opNorm u
  have hmul := mul_le_mul_of_nonneg_right hpert (norm_nonneg u)
  have hlow := hA u
  nlinarith

/-- 最小二乗残差はデザインの像に直交する。 -/
theorem leastSquares_orthogonal (B : E →L[ℝ] F) (y : F) (θhat : E)
    (hfit : IsLeastSquares B y θhat) (u : E) :
    inner ℝ (B θhat - y) (B u) = 0 := by
  have hquad : ∀ t : ℝ, 0 ≤ ‖B u‖ ^ 2 * (t * t) +
      (2 * inner ℝ (B θhat - y) (B u)) * t + 0 := by
    intro t
    have h := hfit (θhat + t • u)
    have heq : B (θhat + t • u) - y = (B θhat - y) + t • B u := by
      simp only [map_add, map_smul]
      abel
    rw [heq, norm_add_sq_real] at h
    simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
    nlinarith
  have hd := discrim_le_zero hquad
  dsimp [discrim] at hd
  nlinarith [sq_nonneg (inner ℝ (B θhat - y) (B u))]

/-- 直交性に基づく定数1の予測誤差評価。 -/
theorem leastSquares_prediction_sq_bound (B : E →L[ℝ] F) (y : F)
    (θstar θhat : E) (hfit : IsLeastSquares B y θhat) :
    ‖B (θhat - θstar)‖ ^ 2 ≤ ‖y - B θstar‖ ^ 2 := by
  have ho := leastSquares_orthogonal B y θhat hfit (θhat - θstar)
  have ho' : inner ℝ (B (θhat - θstar)) (B θhat - y) = 0 := by
    rw [real_inner_comm]
    exact ho
  have heq : y - B θstar = B (θhat - θstar) - (B θhat - y) := by
    simp only [map_sub]
    abel
  rw [heq, norm_sub_sq_real, ho']
  nlinarith [sq_nonneg ‖B θhat - y‖]

theorem leastSquares_error_bound (B : E →L[ℝ] F) (y : F) (θstar θhat : E)
    (g : ℝ) (hg : 0 < g) (hB : LowerBound B g)
    (hfit : IsLeastSquares B y θhat) :
    g ^ 2 * ‖θhat - θstar‖ ^ 2 ≤ ‖y - B θstar‖ ^ 2 := by
  have hs : (g * ‖θhat - θstar‖) ^ 2 ≤ ‖B (θhat - θstar)‖ ^ 2 :=
    (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr (hB _)
  calc
    g ^ 2 * ‖θhat - θstar‖ ^ 2 = (g * ‖θhat - θstar‖) ^ 2 := by ring
    _ ≤ ‖B (θhat - θstar)‖ ^ 2 := hs
    _ ≤ ‖y - B θstar‖ ^ 2 := leastSquares_prediction_sq_bound B y θstar θhat hfit

end WMFKI
