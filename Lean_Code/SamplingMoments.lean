import Lean_Code.SamplingIntegrability
import Lean_Code.SamplingConditional

namespace WMFKI

open MeasureTheory
open scoped BigOperators

variable {Y A : Type*} [MeasurableSpace Y] [Fintype A] [Nonempty A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

/-- 特徴の観測二乗平均だけから、抽出と観測の積空間上のQ/P評価を導く。 -/
theorem samplingError_joint_second_moment {T P : ℕ} (hP : 0 < P)
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (h : Y → Fin T → A → ℝ) (w : Fin T → ℝ) (C : ℝ)
    (hm : ∀ t a, Measurable (fun y => h y t a))
    (hh : ∀ t a, MemLp (fun y => h y t a) 2 μ)
    (hC : ∀ t a, (∫ y, h y t a ^ 2 ∂μ) ≤ C) :
    (∫ z, samplingError (h z.1) w z.2 ^ 2 ∂μ.prod (independentDraws (Fin T × Fin P) A)) ≤
      C * (∑ t, w t ^ 2) / P := by
  classical
  have hs (t : Fin T) (a : A) : Integrable (fun y => h y t a ^ 2) μ :=
    (memLp_two_iff_integrable_sq (hm t a).aestronglyMeasurable).mp (hh t a)
  have havg (t : Fin T) : Integrable (fun y => populationMean (fun a => h y t a ^ 2)) μ :=
    (integrable_finsetSum Finset.univ (fun a _ => hs t a)).div_const _
  have hmean (t : Fin T) : (∫ y, populationMean (fun a => h y t a ^ 2) ∂μ) ≤ C := by
    simp only [populationMean]
    rw [integral_div, integral_finsetSum _ (fun a _ => hs t a)]
    calc
      _ ≤ (∑ _a : A, C) / (Fintype.card A : ℝ) :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => hC t a) (by positivity)
      _ = C := by
        have hn : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
        simp [hn]
  have hbound : Integrable (fun y =>
      (∑ t, w t ^ 2 * populationMean (fun a => h y t a ^ 2)) / P) μ :=
    (integrable_finsetSum Finset.univ (fun t _ => (havg t).const_mul (w t ^ 2))).div_const _
  have hj := samplingError_joint_memLp (P := P) μ h w hm hh
  have hi := (memLp_two_iff_integrable_sq hj.aestronglyMeasurable).mp hj
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ y, (∑ t, w t ^ 2 * populationMean (fun a => h y t a ^ 2)) / P ∂μ :=
      integral_mono hi.integral_prod_left hbound
        (fun y => samplingError_second_moment_weighted hP (h y) w)
    _ = (∑ t, w t ^ 2 * ∫ y, populationMean (fun a => h y t a ^ 2) ∂μ) / P := by
      rw [integral_div, integral_finsetSum _ (fun t _ => (havg t).const_mul (w t ^ 2))]
      simp only [integral_const_mul]
    _ ≤ (∑ t, w t ^ 2 * C) / P :=
      div_le_div_of_nonneg_right
        (Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hmean t) (sq_nonneg _))
        (by positivity)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem pairRowError_joint_memLp {T P N : ℕ} [Fact (2 ≤ N)]
    (μ : Measure Y) [IsProbabilityMeasure μ] (L : ℕ)
    (h : Y → Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ)
    (hm : ∀ t a, Measurable (fun y => h y t a))
    (hh : ∀ t a, MemLp (fun y => h y t a) 2 μ) :
    MemLp (fun z => pairRowError L (h z.1) w z.2) 2
      (μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))) :=
  (samplingError_joint_memLp μ h w hm hh).const_mul (pairPrefactor L N)

theorem pairRowError_conditional_mean_of_moments {T P N : ℕ} [Fact (2 ≤ N)]
    (μ : Measure Y) [IsProbabilityMeasure μ] (L : ℕ)
    (h : Y → Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ)
    (hm : ∀ t a, Measurable (fun y => h y t a))
    (hh : ∀ t a, MemLp (fun y => h y t a) 2 μ) :
    condExp (MeasurableSpace.comap Prod.fst inferInstance)
      (μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N)))
      (fun z => pairRowError L (h z.1) w z.2) =ᵐ[
        μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))] 0 :=
  pairRowError_conditional_mean μ L h w
    ((pairRowError_joint_memLp μ L h w hm hh).integrable (by norm_num))

theorem pairRowError_joint_second_moment {T P N L : ℕ} [Fact (2 ≤ N)]
    (hP : 0 < P) (hL : 0 < L) (μ : Measure Y) [IsProbabilityMeasure μ]
    (h : Y → Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hm : ∀ t a, Measurable (fun y => h y t a))
    (hh : ∀ t a, MemLp (fun y => h y t a) 2 μ)
    (hC : ∀ t a, (∫ y, h y t a ^ 2 ∂μ) ≤ C) :
    (∫ z, pairRowError L (h z.1) w z.2 ^ 2 ∂μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))) ≤
      C * (∑ t, w t ^ 2) / ((L : ℝ) * P) := by
  simp only [pairRowError, mul_pow]
  rw [integral_const_mul]
  have hn : 1 ≤ N := by have := Fact.out (p := 2 ≤ N); omega
  calc
    _ ≤ pairPrefactor L N ^ 2 * (C * (∑ t, w t ^ 2) / P) :=
      mul_le_mul_of_nonneg_left (samplingError_joint_second_moment hP μ h w C hm hh hC)
        (sq_nonneg _)
    _ ≤ (1 / (L : ℝ)) * (C * (∑ t, w t ^ 2) / P) :=
      mul_le_mul_of_nonneg_right (pairPrefactor_sq_le hL hn) (by positivity)
    _ = _ := by ring

end WMFKI
