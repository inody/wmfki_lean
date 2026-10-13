import Lean_Code.PairDesignMoments

namespace WMFKI
open MeasureTheory
open scoped BigOperators

/-- 観測ごとの特徴を全有向ペアで評価する、原稿のN⁻²正規化のデザイン。 -/
noncomputable def fullPairDesign {Y : Type*} {L M T N : ℕ}
    (h : Y → Fin L → Fin M → Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ)
    (y : Y) : Matrix (Fin L) (Fin M) ℝ :=
  fun a m => (1 / Real.sqrt L) * ∑ t, w t * ((∑ p, h y a m t p) / (N : ℝ) ^ 2)

/-- 全成分で抽出列を共有する、実際の標本デザインの有限和。 -/
noncomputable def sampledPairDesign {Y : Type*} {L M T P N : ℕ}
    (h : Y → Fin L → Fin M → Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ)
    (z : Y × ((Fin T × Fin P) → OrderedPair N)) : Matrix (Fin L) (Fin M) ℝ :=
  fun a m => pairPrefactor L N * ∑ t, w t * (∑ ν, h z.1 a m t (z.2 (t, ν))) / P

/-- 中心化として定義した誤差と、組み立てた二つの行列の差の一致。 -/
theorem pairDesignError_eq_difference {Y : Type*} {L M T P N : ℕ}
    (hN : 2 ≤ N) (hP : 0 < P)
    (h : Y → Fin L → Fin M → Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ)
    (z : Y × ((Fin T × Fin P) → OrderedPair N)) :
    pairDesignError h w z = sampledPairDesign h w z - fullPairDesign h w z.1 := by
  ext a m
  change pairRowError L (fun t p => h z.1 a m t p) w z.2 = _
  rw [pairRowError, samplingError_eq_sampled_sub_full hP]
  have heq : fullPairDesign h w z.1 a m = pairPrefactor L N *
      ∑ t, w t * populationMean (h z.1 a m t) := by
    unfold fullPairDesign pairPrefactor
    simp_rw [← corrected_pair_average hN, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  change _ = sampledPairDesign h w z a m - fullPairDesign h w z.1 a m
  rw [heq]
  unfold sampledPairDesign
  ring

/-- 行列差の各成分について、通常の条件付き期待値が0。 -/
theorem assembled_design_conditional_centered {Y : Type*} [MeasurableSpace Y]
    {L M T P N : ℕ} [Fact (2 ≤ N)] (hP : 0 < P)
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (h : Y → Fin L → Fin M → Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ)
    (hm : ∀ a m t p, Measurable (fun y => h y a m t p))
    (hh : ∀ a m t p, MemLp (fun y => h y a m t p) 2 μ) (a : Fin L) (m : Fin M) :
    (μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N)))[
      (fun z => (sampledPairDesign h w z - fullPairDesign h w z.1) a m) |
      MeasurableSpace.comap Prod.fst inferInstance]
      =ᵐ[μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))] 0 := by
  simp_rw [← pairDesignError_eq_difference Fact.out hP]
  exact pairRowError_conditional_mean_of_moments μ L
    (fun y t p => h y a m t p) w (hm a m) (hh a m)

/-- 観測特徴の二乗平均から、組み立てたデザイン差のFrobenius評価。 -/
theorem assembled_design_second_moment {Y : Type*} [MeasurableSpace Y]
    {L M T P N : ℕ} [Fact (2 ≤ N)] (hP : 0 < P) (hL : 0 < L)
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (h : Y → Fin L → Fin M → Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hm : ∀ a m t p, Measurable (fun y => h y a m t p))
    (hh : ∀ a m t p, MemLp (fun y => h y a m t p) 2 μ)
    (hC : ∀ a m t p, (∫ y, h y a m t p ^ 2 ∂μ) ≤ C) :
    (∫ z, frobenius (sampledPairDesign h w z - fullPairDesign h w z.1) ^ 2
      ∂μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))) ≤
      (M : ℝ) * C * (∑ t, w t ^ 2) / P := by
  simp_rw [← pairDesignError_eq_difference Fact.out hP]
  exact pairDesignError_second_moment hP hL μ h w C hC0 hm hh hC

/-- 係数方向の評価は合成特徴の二乗平均だけを使い、Mや係数ノルムを増やさない。 -/
theorem assembled_design_direction_second_moment {Y : Type*} [MeasurableSpace Y]
    {L M T P N : ℕ} [Fact (2 ≤ N)] (hP : 0 < P) (hL : 0 < L)
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (h : Y → Fin L → Fin M → Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ)
    (θ : Fin M → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hm : ∀ a t p, Measurable (fun y => ∑ m, θ m * h y a m t p))
    (hh : ∀ a t p, MemLp (fun y => ∑ m, θ m * h y a m t p) 2 μ)
    (hC : ∀ a t p, (∫ y, (∑ m, θ m * h y a m t p) ^ 2 ∂μ) ≤ C) :
    (∫ z, ‖matrixMap (sampledPairDesign h w z - fullPairDesign h w z.1)
      (WithLp.toLp 2 θ)‖ ^ 2
      ∂μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))) ≤
      C * (∑ t, w t ^ 2) / P := by
  simp_rw [← pairDesignError_eq_difference Fact.out hP]
  have heq : ∀ z, matrixMap (pairDesignError (P := P) h w z) (WithLp.toLp 2 θ) =
      WithLp.toLp 2 (fun a => ∑ m, pairDesignError h w z a m * θ m) := by
    intro z
    ext a
    simp [matrixMap_apply]
  simp_rw [heq]
  exact pairDesignError_direction_second_moment hP hL μ h w θ C hC0 hm hh hC

end WMFKI
