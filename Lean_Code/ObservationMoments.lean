import Lean_Code.FeatureMoments

namespace WMFKI
open MeasureTheory

/-- 三角不等式だけで成り立つ二乗ノルム評価。 -/
theorem norm_add_sq_le_twice {F : Type*} [NormedAddCommGroup F] (x e : F) :
    ‖x + e‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖e‖ ^ 2 := by
  have hs := (sq_le_sq₀ (norm_nonneg (x + e)) (by positivity)).mpr (norm_add_le x e)
  nlinarith [sq_nonneg (‖x‖ - ‖e‖)]

/-- 潜在位置と観測誤差から観測二乗平均を供給する。平均0・独立性は不要。 -/
theorem observation_second_moment {Ω F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (μ : Measure Ω) (X e : Ω → F) (hX : Measurable X) (he : Measurable e)
    (hiX : Integrable (fun ω => ‖X ω‖ ^ 2) μ)
    (hie : Integrable (fun ω => ‖e ω‖ ^ 2) μ)
    (RX Re : ℝ) (hRX : (∫ ω, ‖X ω‖ ^ 2 ∂μ) ≤ RX)
    (hRe : (∫ ω, ‖e ω‖ ^ 2 ∂μ) ≤ Re) :
    Measurable (fun ω => X ω + e ω) ∧
    Integrable (fun ω => ‖X ω + e ω‖ ^ 2) μ ∧
    (∫ ω, ‖X ω + e ω‖ ^ 2 ∂μ) ≤ 2 * RX + 2 * Re := by
  have hm : Measurable (fun ω => X ω + e ω) := hX.add he
  have hb : Integrable (fun ω => 2 * ‖X ω‖ ^ 2 + 2 * ‖e ω‖ ^ 2) μ :=
    (hiX.const_mul 2).add (hie.const_mul 2)
  have hi : Integrable (fun ω => ‖X ω + e ω‖ ^ 2) μ := by
    apply hb.mono' (hm.norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact norm_add_sq_le_twice _ _
  refine ⟨hm, hi, ?_⟩
  calc
    _ ≤ ∫ ω, 2 * ‖X ω‖ ^ 2 + 2 * ‖e ω‖ ^ 2 ∂μ :=
      integral_mono hi hb (fun ω => norm_add_sq_le_twice _ _)
    _ = 2 * (∫ ω, ‖X ω‖ ^ 2 ∂μ) + 2 * ∫ ω, ‖e ω‖ ^ 2 ∂μ := by
      rw [integral_add (hiX.const_mul 2) (hie.const_mul 2)]
      simp only [integral_const_mul]
    _ ≤ _ := by linarith

end WMFKI
