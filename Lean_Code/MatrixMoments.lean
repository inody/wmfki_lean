import Lean_Code.MatrixBridge

namespace WMFKI

open MeasureTheory

/-- Frobenius二乗平均から作用素ノルム二乗平均への移行。可積分性も導く。 -/
theorem matrixMap_secondMoment_transfer {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq n] (μ : Measure Ω) (A : Ω → Matrix m n ℝ)
    (hm : Measurable (fun ω => ‖matrixMap (A ω)‖ ^ 2))
    (hi : Integrable (fun ω => frobenius (A ω) ^ 2) μ) :
    Integrable (fun ω => ‖matrixMap (A ω)‖ ^ 2) μ ∧
    (∫ ω, ‖matrixMap (A ω)‖ ^ 2 ∂μ) ≤ ∫ ω, frobenius (A ω) ^ 2 ∂μ := by
  have hb (ω : Ω) : ‖matrixMap (A ω)‖ ^ 2 ≤ frobenius (A ω) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr
      (matrixMap_norm_le_frobenius (A ω))
  have hio : Integrable (fun ω => ‖matrixMap (A ω)‖ ^ 2) μ := by
    apply hi.mono' hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖matrixMap (A ω)‖)] using hb ω
  exact ⟨hio, integral_mono hio hi hb⟩

end WMFKI
