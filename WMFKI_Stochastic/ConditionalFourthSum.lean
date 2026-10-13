import WMFKI_Stochastic.IndependentFourthSum
import Mathlib.Analysis.Convex.Integral

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace WMFKIIndependentFourth

/-- 可積分な4乗と可測性からL4を復元する。 -/
theorem l4_of_integrable_fourth {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {f : Ω → ℝ} (hf : Measurable f) (hi : Integrable (fun ω => f ω^4) P) : MemLp f 4 P := by
  apply (integrable_norm_rpow_iff hf.aestronglyMeasurable (p := 4) (by norm_num) (by norm_num)).mp
  have he (ω : Ω) : ‖f ω‖ ^ (4 : ℝ≥0∞).toReal = f ω^4 := by
    rw [show (4 : ℝ≥0∞).toReal = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, (show Even (4 : ℕ) from by decide).pow_abs]
  simpa only [he] using hi

/-- 共有変数xを固定すると中心化する核F(x,y)の独立和。
    全体では各項がxを共有するので、無条件の独立性は仮定しない。
    切片のL4は、積空間上のL4とFubiniからa.e.に導く。 -/
theorem conditionally_centered_fourth_sum
    {A B I : Type*} [MeasurableSpace A] [MeasurableSpace B] [Fintype I]
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B) [IsProbabilityMeasure ν]
    (s : Finset I) (F : A × B → ℝ) (hF : Measurable F) (hL : MemLp F 4 (μ.prod ν))
    (hc : ∀ᵐ x ∂μ, (∫ y, F (x,y) ∂ν) = 0) :
    let R := Measure.pi (fun _ : I => ν)
    let S := fun z : A × (I → B) => ∑ i ∈ s, F (z.1,z.2 i)
    MemLp S 4 (μ.prod R) ∧
    (∫ z, S z ^ 4 ∂(μ.prod R)) ≤ 3*(s.card : ℝ)^2*(∫ z, F z^4 ∂(μ.prod ν)) := by
  classical
  dsimp only
  let R := Measure.pi (fun _ : I => ν)
  let S := fun z : A × (I → B) => ∑ i ∈ s, F (z.1,z.2 i)
  have hp (i : I) : MeasurePreserving (fun z : A × (I → B) => (z.1,z.2 i))
      (μ.prod R) (μ.prod ν) := by
    have hid : MeasurePreserving (id : A → A) μ μ := ⟨measurable_id, Measure.map_id⟩
    exact hid.prod (measurePreserving_eval (fun _ : I => ν) i)
  have hS : MemLp S 4 (μ.prod R) :=
    memLp_finsetSum s (fun i _ => hL.comp_measurePreserving (hp i))
  have hS4 : Integrable (fun z => S z^4) (μ.prod R) := l4_integrable_power hS 4 le_rfl
  have hF4 := l4_integrable_power hL 4 le_rfl
  have hX : iIndepFun (fun i (ω : I → B) => ω i) R :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hLaw (i : I) : HasLaw (fun ω : I → B => ω i) ν R :=
    (measurePreserving_eval (fun _ : I => ν) i).hasLaw
  have hb : ∀ᵐ x ∂μ, (∫ ω, (∑ i ∈ s, F (x,ω i))^4 ∂R) ≤
      3*(s.card : ℝ)^2*(∫ y, F (x,y)^4 ∂ν) := by
    filter_upwards [hF4.prod_right_ae, hc] with x hx hx0
    have hf : Measurable (fun y => F (x,y)) := hF.comp measurable_prodMk_left
    exact (iid_centered_kernel_fourth_bound ν s hX (fun i => measurable_pi_apply i) hLaw
      (fun y => F (x,y)) hf (l4_of_integrable_fourth ν hf hx) hx0).2
  refine ⟨hS, ?_⟩
  change (∫ z, S z^4 ∂(μ.prod R)) ≤ _
  rw [integral_prod _ hS4]
  calc
    _ ≤ ∫ x, 3*(s.card : ℝ)^2*(∫ y, F (x,y)^4 ∂ν) ∂μ :=
      integral_mono_ae hS4.integral_prod_left (hF4.integral_prod_left.const_mul _) hb
    _ = _ := by rw [integral_const_mul, integral_prod _ hF4]

end WMFKIIndependentFourth
