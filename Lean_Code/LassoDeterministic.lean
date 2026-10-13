import Lean_Code.LassoGeometry
import Mathlib.Tactic

namespace WMFKI

open scoped BigOperators

variable {M : ℕ} {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F]

/-- 最小化条件と随伴スコアから導く基本不等式。 -/
theorem lasso_basic_inequality (B : Coeff M →L[ℝ] F) (y : F)
    (θstar θhat : Coeff M) (S : Finset (Fin M)) (lam : ℝ)
    (hlam : 0 < lam) (hsupport : ∀ i ∉ S, θstar i = 0)
    (hfit : IsLasso B y lam θhat) (hscore : ScoreBound B (y - B θstar) lam) :
    ‖B (θhat - θstar)‖ ^ 2 + lam * partialL1 Sᶜ (θhat - θstar) ≤
      3 * lam * partialL1 S (θhat - θstar) := by
  let u := θhat - θstar
  let ξ := y - B θstar
  have hu : θstar + u = θhat := by dsimp [u]; abel
  have heq : B θhat - y = B u - ξ := by dsimp [u, ξ]; simp only [map_sub]; abel
  have heq' : B θstar - y = -ξ := by dsimp [ξ]; abel
  have hopt := hfit θstar
  dsimp [lassoObjective] at hopt
  rw [heq, heq', norm_neg, norm_sub_sq_real] at hopt
  have hd := l1_support_difference S θstar u hsupport
  rw [hu] at hd
  have hp := mul_le_mul_of_nonneg_left hd hlam.le
  have hc := score_inner_bound B ξ lam hscore u
  have hsplit := partialL1_decomp S u
  change ‖B u‖ ^ 2 + lam * partialL1 Sᶜ u ≤ 3 * lam * partialL1 S u
  nlinarith

theorem lasso_deterministic : LassoDeterministicStatement M F := by
  intro B y θstar θhat S lam g hlam hg hs hfit hscore hconeB
  let u := θhat - θstar
  have hbasic := lasso_basic_inequality B y θstar θhat S lam hlam hs hfit hscore
  have hc : SparseCone S u := by
    apply (mul_le_mul_iff_of_pos_left hlam).mp
    change lam * partialL1 Sᶜ u ≤ lam * (3 * partialL1 S u)
    change ‖B u‖ ^ 2 + lam * partialL1 Sᶜ u ≤ 3 * lam * partialL1 S u at hbasic
    nlinarith [sq_nonneg ‖B u‖]
  refine ⟨hc, ?_⟩
  have hlo : g ^ 2 * ‖u‖ ^ 2 ≤ ‖B u‖ ^ 2 := by
    have hh := (sq_le_sq₀ (by positivity) (norm_nonneg (B u))).mpr (hconeB u hc)
    simpa only [mul_pow] using hh
  have hup : ‖B u‖ ^ 2 ≤ 3 * lam * partialL1 S u := by
    have hn := mul_nonneg hlam.le (partialL1_nonneg Sᶜ u)
    linarith
  have hsquare : (g ^ 2 * ‖u‖ ^ 2) ^ 2 ≤ (3 * lam * partialL1 S u) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity [partialL1_nonneg S u])).mpr (hlo.trans hup)
  have hcs := mul_le_mul_of_nonneg_left (partialL1_sq_le S u)
    (show 0 ≤ 9 * lam ^ 2 by positivity)
  have hprod : (g ^ 4 * ‖u‖ ^ 2) * ‖u‖ ^ 2 ≤
      (9 * (S.card : ℝ) * lam ^ 2) * ‖u‖ ^ 2 := by nlinarith
  by_cases hz : ‖u‖ = 0
  · change ‖u‖ ^ 2 ≤ _
    simp only [hz, zero_pow (by decide : 2 ≠ 0)]
    positivity
  · have hnorm : 0 < ‖u‖ ^ 2 := sq_pos_of_ne_zero hz
    have hcancel := (mul_le_mul_iff_of_pos_right hnorm).mp hprod
    apply (le_div_iff₀ (pow_pos hg 4)).mpr
    change ‖u‖ ^ 2 * g ^ 4 ≤ _
    nlinarith

end WMFKI
