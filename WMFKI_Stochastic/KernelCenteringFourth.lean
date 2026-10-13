import WMFKI_Stochastic.ConditionalFourthSum
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace WMFKIIndependentFourth

/-- 共有変数を残して積分した平均のL4とJensen評価。 -/
theorem parameter_mean_fourth
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B) [IsProbabilityMeasure ν]
    (F : A × B → ℝ) (hF : Measurable F) (hL : MemLp F 4 (μ.prod ν)) :
    MemLp (fun x => ∫ y, F (x,y) ∂ν) 4 μ ∧
    (∫ x, (∫ y, F (x,y) ∂ν)^4 ∂μ) ≤ ∫ z, F z^4 ∂(μ.prod ν) := by
  have hi := hL.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have h4 := l4_integrable_power hL 4 le_rfl
  have hm : Measurable (fun x => ∫ y, F (x,y) ∂ν) := hF.stronglyMeasurable.integral_prod_right'.measurable
  have hb : ∀ᵐ x ∂μ, (∫ y, F (x,y) ∂ν)^4 ≤ ∫ y, F (x,y)^4 ∂ν := by
    filter_upwards [hi.prod_right_ae, h4.prod_right_ae] with x hx hx4
    have hc : ConvexOn ℝ univ (fun z : ℝ => ‖z‖^4) :=
      convexOn_univ_norm.pow (fun z _ => norm_nonneg z) 4
    have hn : Integrable (fun y => ‖F (x,y)‖^4) ν := by
      simpa only [Real.norm_eq_abs, (show Even (4 : ℕ) from by decide).pow_abs] using hx4
    have hj := hc.map_integral_le ((continuous_norm.pow 4).continuousOn) isClosed_univ
      (Filter.Eventually.of_forall (fun _ => mem_univ _)) hx hn
    simpa only [Real.norm_eq_abs, (show Even (4 : ℕ) from by decide).pow_abs] using hj
  have hg4 : Integrable (fun x => (∫ y, F (x,y) ∂ν)^4) μ := by
    apply h4.integral_prod_left.mono' (hm.aestronglyMeasurable.pow 4)
    filter_upwards [hb] with x hx
    change ‖(∫ y, F (x,y) ∂ν)^4‖ ≤ _
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (∫ y, F (x,y) ∂ν)^4)] using hx
  refine ⟨l4_of_integrable_fourth μ hm hg4, ?_⟩
  rw [integral_prod _ h4]
  exact integral_mono_ae hg4 h4.integral_prod_left hb

theorem fourth_sub_le (a b : ℝ) : (a-b)^4 ≤ 8*(a^4+b^4) := by
  have h : (a-b)^2 ≤ 2*(a^2+b^2) := by nlinarith [sq_nonneg (a+b)]
  have hh := pow_le_pow_left₀ (sq_nonneg (a-b)) h 2
  nlinarith [sq_nonneg (a^2-b^2)]

/-- 平均を実際に引いて中心化する。中心化と中心化後のモーメントは結論。 -/
theorem centered_kernel_fourth
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B) [IsProbabilityMeasure ν]
    (F : A × B → ℝ) (hF : Measurable F) (hL : MemLp F 4 (μ.prod ν)) :
    let H := fun z : A × B => F z - ∫ y, F (z.1,y) ∂ν
    Measurable H ∧ MemLp H 4 (μ.prod ν) ∧
    (∀ᵐ x ∂μ, (∫ y, H (x,y) ∂ν) = 0) ∧
    (∫ z, H z^4 ∂(μ.prod ν)) ≤ 16*(∫ z, F z^4 ∂(μ.prod ν)) := by
  dsimp only
  have hm : Measurable (fun x => ∫ y, F (x,y) ∂ν) := hF.stronglyMeasurable.integral_prod_right'.measurable
  obtain ⟨hg,hgB⟩ := parameter_mean_fourth μ ν F hF hL
  have hgp : MemLp (fun z : A × B => ∫ y, F (z.1,y) ∂ν) 4 (μ.prod ν) := hg.comp_fst ν
  have hH := hL.sub hgp
  refine ⟨hF.sub (hm.comp measurable_fst), hH, ?_, ?_⟩
  · filter_upwards [(hL.integrable (by norm_num)).prod_right_ae] with x hx
    rw [integral_sub hx (integrable_const _)]
    simp
  · have h4 := l4_integrable_power hL 4 le_rfl
    have hg4 := l4_integrable_power hgp 4 le_rfl
    calc
      _ ≤ ∫ z, 8*(F z^4 + (∫ y, F (z.1,y) ∂ν)^4) ∂(μ.prod ν) :=
        integral_mono (l4_integrable_power hH 4 le_rfl) ((h4.add hg4).const_mul 8)
          (fun z => fourth_sub_le _ _)
      _ = 8*((∫ z, F z^4 ∂(μ.prod ν)) + (∫ x, (∫ y, F (x,y) ∂ν)^4 ∂μ)) := by
        rw [integral_const_mul, integral_add h4 hg4,
          integral_fun_fst (fun x => (∫ y, F (x,y) ∂ν)^4)]
        simp
      _ ≤ _ := by linarith

end WMFKIIndependentFourth
