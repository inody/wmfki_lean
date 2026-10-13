import Mathlib.Probability.HasLaw

open MeasureTheory ProbabilityTheory

namespace WMFKIIIDPairs

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- L²正則性を明示した、二つの二次モーメントによる共分散の上界。 -/
theorem covariance_le_common_second_moment {X Y : Ω → ℝ} {C : ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hXC : (∫ ω, X ω ^ 2 ∂P) ≤ C) (hYC : (∫ ω, Y ω ^ 2 ∂P) ≤ C) :
    cov[X, Y; P] ≤ C := by
  have hx : Var[X; P] ≤ C := by
    rw [variance_eq_sub hX]
    change (∫ ω, X ω ^ 2 ∂P) - (∫ ω, X ω ∂P) ^ 2 ≤ C
    nlinarith [sq_nonneg (∫ ω, X ω ∂P)]
  have hy : Var[Y; P] ≤ C := by
    rw [variance_eq_sub hY]
    change (∫ ω, Y ω ^ 2 ∂P) - (∫ ω, Y ω ∂P) ^ 2 ≤ C
    nlinarith [sq_nonneg (∫ ω, Y ω ∂P)]
  have h := variance_nonneg (X - Y) P
  rw [variance_sub hX hY] at h
  linarith

/-- 分散とバイアスの正確な分解。有限性はL²から確保する。 -/
theorem mean_square_error_eq_variance_bias {X : Ω → ℝ} (hX : MemLp X 2 P) (a : ℝ) :
    (∫ ω, (X ω - a) ^ 2 ∂P) = Var[X; P] + ((∫ ω, X ω ∂P) - a) ^ 2 := by
  have hm : (∫ ω, X ω - a ∂P) = (∫ ω, X ω ∂P) - a := by
    rw [integral_sub (hX.integrable (by norm_num)) (integrable_const a)]
    simp
  have h := variance_eq_sub (hX.sub (memLp_const a))
  change Var[fun ω => X ω - a; P] =
    (∫ ω, (X ω - a) ^ 2 ∂P) - (∫ ω, X ω - a ∂P) ^ 2 at h
  rw [variance_sub_const hX.aestronglyMeasurable a, hm] at h
  linarith

/-- 二組のラベルの重複を、四つの一致指示関数で上から数える。 -/
def pairOverlapWeight {N : ℕ} (p q : Fin N × Fin N) : ℝ :=
  (if p.1 = q.1 then 1 else 0) + (if p.1 = q.2 then 1 else 0) +
  (if p.2 = q.1 then 1 else 0) + (if p.2 = q.2 then 1 else 0)

theorem sum_pair_overlap {N : ℕ} (p : Fin N × Fin N) :
    ∑ q, pairOverlapWeight p q = 4 * (N : ℝ) := by
  have hs (i : Fin N) : (∑ j : Fin N, ∑ _k : Fin N, if i = j then (1 : ℝ) else 0) = N := by
    rw [Finset.sum_comm]
    simp
  rw [Fintype.sum_prod_type]
  dsimp only [pairOverlapWeight]
  simp_rw [Finset.sum_add_distrib]
  rw [hs, hs]
  simp
  ring

theorem sum_off_diagonal_constant (N : ℕ) (a : ℝ) :
    (∑ p : Fin N × Fin N, if p.1 = p.2 then 0 else a) =
      (N : ℝ) * ((N : ℝ) - 1) * a := by
  have hi (i : Fin N) : (∑ j : Fin N, if i = j then 0 else a) = (N : ℝ) * a - a := by
    have he (j : Fin N) : (if i = j then 0 else a) = a - (if i = j then a else 0) := by
      split_ifs <;> ring
    simp_rw [he]
    simp [Finset.sum_sub_distrib]
  rw [Fintype.sum_prod_type]
  simp_rw [hi]
  simp
  ring

end WMFKIIIDPairs
