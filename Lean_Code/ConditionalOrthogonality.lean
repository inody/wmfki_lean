import Lean_Code.Deterministic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

namespace WMFKI

open MeasureTheory

variable {Ω F : Type*} {m : MeasurableSpace Ω} [m0 : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [IsProbabilityMeasure μ] [CompleteSpace F] in
/-- L2のノルムは実際の二乗平均である。 -/
theorem l2_norm_sq_eq_integral (f : Lp F 2 μ) :
    ‖f‖ ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
  calc
    _ = inner ℝ f f := (real_inner_self_eq_norm_sq f).symm
    _ = ∫ ω, inner ℝ (f ω) (f ω) ∂μ := L2.inner_def f f
    _ = _ := by simp only [real_inner_self_eq_norm_sq]

/-- 条件付き平均0と観測σ代数への可測性から、交差項が消える。 -/
theorem conditional_centered_inner_zero (hm : m ≤ m0) (f g : Lp F 2 μ)
    (hcenter : μ[(fun ω => f ω) | m] =ᵐ[μ] 0)
    (hg : AEStronglyMeasurable[m] g μ) : inner ℝ f g = 0 := by
  have hbridge := MemLp.condExpL2_ae_eq_condExp (𝕜 := ℝ) hm (Lp.memLp f)
  rw [Lp.toLp_coeFn] at hbridge
  have hz : (condExpL2 F ℝ hm f : Lp F 2 μ) = 0 := by
    apply Lp.ext
    exact hbridge.trans (hcenter.trans (Lp.coeFn_zero F 2 μ).symm)
  have hinner := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) hm f g hg
  rw [hz, inner_zero_left] at hinner
  exact hinner.symm

/-- 原稿A.6の直交性による二乗平均の加法性。条件付き平均0自体は別途必要。 -/
theorem conditional_centered_second_moment (hm : m ≤ m0) (f g : Lp F 2 μ)
    (hcenter : μ[(fun ω => f ω) | m] =ᵐ[μ] 0)
    (hg : AEStronglyMeasurable[m] g μ) :
    (∫ ω, ‖g ω - f ω‖ ^ 2 ∂μ) =
      (∫ ω, ‖g ω‖ ^ 2 ∂μ) + ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
  have ho := conditional_centered_inner_zero hm f g hcenter hg
  have hn : ‖g - f‖ ^ 2 = ‖g‖ ^ 2 + ‖f‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm f g, ho]
    ring
  have hi : (∫ ω, ‖g ω - f ω‖ ^ 2 ∂μ) = ∫ ω, ‖(g - f) ω‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub g f] with ω hω
    rw [hω]
    rfl
  rw [hi, ← l2_norm_sq_eq_integral, hn, l2_norm_sq_eq_integral, l2_norm_sq_eq_integral]

end WMFKI
