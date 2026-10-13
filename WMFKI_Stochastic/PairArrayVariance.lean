import WMFKI_Stochastic.PairMomentAlgebra

open MeasureTheory ProbabilityTheory

namespace WMFKIIIDPairs
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- N^-2で正規化した全配列の和。対角除外は各項の定義で行う。 -/
noncomputable def pairArrayAverage (N : ℕ) (Z : (Fin N × Fin N) → Ω → ℝ) (ω : Ω) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ p, Z p ω

omit [IsProbabilityMeasure P] in
theorem pair_array_memLp {N : ℕ} {Z : (Fin N × Fin N) → Ω → ℝ}
    (hZ : ∀ p, MemLp (Z p) 2 P) : MemLp (pairArrayAverage N Z) 2 P := by
  exact (memLp_finsetSum Finset.univ (fun p _ => hZ p)).const_mul _

/-- 添字を共有しない項の共分散が消える配列に対する評価。
    iid粒子からこの仮定を導く定理は別モジュールで接続する。 -/
theorem pair_array_variance_bound {N : ℕ} (hN : 0 < N)
    {Z : (Fin N × Fin N) → Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hZ : ∀ p, MemLp (Z p) 2 P)
    (hM : ∀ p, (∫ ω, Z p ω ^ 2 ∂P) ≤ C)
    (hdisj : ∀ p q, p.1 ≠ q.1 → p.1 ≠ q.2 → p.2 ≠ q.1 → p.2 ≠ q.2 →
      cov[Z p, Z q; P] = 0) :
    Var[pairArrayAverage N Z; P] ≤ 4 * C / (N : ℝ) := by
  have hcov (p q : Fin N × Fin N) : cov[Z p, Z q; P] ≤ C * pairOverlapWeight p q := by
    have hb := covariance_le_common_second_moment (hZ p) (hZ q) (hM p) (hM q)
    by_cases hd : p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2
    · rw [hdisj p q hd.1 hd.2.1 hd.2.2.1 hd.2.2.2]
      simp [pairOverlapWeight, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2]
    · have hw : (1 : ℝ) ≤ pairOverlapWeight p q := by
        unfold pairOverlapWeight
        split_ifs <;> norm_num at *
        tauto
      exact hb.trans (by simpa using mul_le_mul_of_nonneg_left hw hC)
  have hrow (p : Fin N × Fin N) : (∑ q, cov[Z p, Z q; P]) ≤ C * (4 * (N : ℝ)) := by
    calc
      _ ≤ ∑ q, C * pairOverlapWeight p q := Finset.sum_le_sum (fun q _ => hcov p q)
      _ = _ := by rw [← Finset.mul_sum, sum_pair_overlap]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  unfold pairArrayAverage
  rw [variance_const_mul, variance_fun_sum hZ]
  calc
    _ ≤ ((N : ℝ)⁻¹ ^ 2) ^ 2 * ∑ _p : Fin N × Fin N, C * (4 * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p _ => hrow p)) (sq_nonneg _)
    _ = 4 * C / (N : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul]
      field_simp

end WMFKIIIDPairs
