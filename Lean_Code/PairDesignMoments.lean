import Lean_Code.SamplingMoments

namespace WMFKI

open MeasureTheory
open scoped BigOperators

/-- 同じ抽出を全行・全辞書成分で共有する行列誤差。 -/
noncomputable def pairDesignError {Y : Type*} {L M T P N : ℕ}
    (h : Y → Fin L → Fin M → Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ)
    (z : Y × ((Fin T × Fin P) → OrderedPair N)) : Matrix (Fin L) (Fin M) ℝ :=
  fun a m => pairRowError L (fun t p => h z.1 a m t p) w z.2

theorem pairDesignError_second_moment {Y : Type*} [MeasurableSpace Y]
    {L M T P N : ℕ} [Fact (2 ≤ N)] (hP : 0 < P) (hL : 0 < L)
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (h : Y → Fin L → Fin M → Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hm : ∀ a m t p, Measurable (fun y => h y a m t p))
    (hh : ∀ a m t p, MemLp (fun y => h y a m t p) 2 μ)
    (hC : ∀ a m t p, (∫ y, h y a m t p ^ 2 ∂μ) ≤ C) :
    (∫ z, frobenius (pairDesignError h w z) ^ 2 ∂
      μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))) ≤
      (M : ℝ) * C * (∑ t, w t ^ 2) / P := by
  let ν := μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))
  have hi (a : Fin L) (m : Fin M) :
      Integrable (fun z => pairDesignError h w z a m ^ 2) ν := by
    have hf := pairRowError_joint_memLp (P := P) μ L (fun y t p => h y a m t p) w (hm a m) (hh a m)
    exact (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have hn (z : Y × ((Fin T × Fin P) → OrderedPair N)) :
      frobenius (pairDesignError h w z) ^ 2 = ∑ a, ∑ m, pairDesignError h w z a m ^ 2 := by
    unfold frobenius
    rw [Real.sq_sqrt (by positivity)]
  simp_rw [hn]
  calc
    _ = ∑ a, ∑ m, ∫ z, pairDesignError h w z a m ^ 2 ∂ν := by
      rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun m _ => hi a m))]
      apply Finset.sum_congr rfl
      intro a _
      exact integral_finsetSum _ (fun m _ => hi a m)
    _ ≤ ∑ _a : Fin L, ∑ _m : Fin M, C * (∑ t, w t ^ 2) / ((L : ℝ) * P) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro m _
      exact pairRowError_joint_second_moment hP hL μ (fun y t p => h y a m t p) w C hC0
        (hm a m) (hh a m) (hC a m)
    _ = _ := by
      have hl : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

/-- 共有抽出なので、Dθは真の相互作用の特徴を直接抽出した誤差に等しい。 -/
theorem pairDesignError_mul_coefficients {Y : Type*} {L M T P N : ℕ}
    (h : Y → Fin L → Fin M → Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ)
    (θ : Fin M → ℝ) (z : Y × ((Fin T × Fin P) → OrderedPair N)) (a : Fin L) :
    (∑ m, pairDesignError h w z a m * θ m) =
      pairRowError L (fun t p => ∑ m, θ m * h z.1 a m t p) w z.2 := by
  unfold pairDesignError pairRowError
  rw [samplingError_linear_combination, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- 合成特徴の二乗平均Cだけを使う方向評価。Mや係数L1ノルムを追加しない。 -/
theorem pairDesignError_direction_second_moment {Y : Type*} [MeasurableSpace Y]
    {L M T P N : ℕ} [Fact (2 ≤ N)] (hP : 0 < P) (hL : 0 < L)
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (h : Y → Fin L → Fin M → Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ)
    (θ : Fin M → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hm : ∀ a t p, Measurable (fun y => ∑ m, θ m * h y a m t p))
    (hh : ∀ a t p, MemLp (fun y => ∑ m, θ m * h y a m t p) 2 μ)
    (hC : ∀ a t p, (∫ y, (∑ m, θ m * h y a m t p) ^ 2 ∂μ) ≤ C) :
    (∫ z, ‖(WithLp.toLp 2 (fun a => ∑ m, pairDesignError h w z a m * θ m) :
      EuclideanSpace ℝ (Fin L))‖ ^ 2 ∂
        μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))) ≤
      C * (∑ t, w t ^ 2) / P := by
  let ν := μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))
  let k := fun y a t p => ∑ m, θ m * h y a m t p
  have hi (a : Fin L) : Integrable (fun z => pairRowError L (k z.1 a) w z.2 ^ 2) ν := by
    have hf := pairRowError_joint_memLp (P := P) μ L (fun y => k y a) w (hm a) (hh a)
    exact (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  simp only [EuclideanSpace.real_norm_sq_eq]
  change (∫ z, (∑ a, (∑ m, pairDesignError h w z a m * θ m) ^ 2) ∂ν) ≤ _
  simp_rw [pairDesignError_mul_coefficients]
  rw [integral_finsetSum _ (fun a _ => hi a)]
  calc
    _ ≤ ∑ _a : Fin L, C * (∑ t, w t ^ 2) / ((L : ℝ) * P) := by
      apply Finset.sum_le_sum
      intro a _
      exact pairRowError_joint_second_moment hP hL μ (fun y => k y a) w C hC0
        (hm a) (hh a) (hC a)
    _ = _ := by
      have hl : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

end WMFKI
