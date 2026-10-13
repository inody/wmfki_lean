import Chapter7ItoCommonIntegrand
import Chapter11PositiveTimeIntegral

open MeasureTheory Set Filter
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete
namespace WMFKIExternalProbe

/-- Null-set changes on one common event and irrelevant nonpositive times
preserve the actual stochastic-integral certificate. -/
theorem ito_integrand_positive_common_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (X Y : ClosedTime T → Ω → ℝ) (H G : Ω × ℝ → ℝ)
    (h : ItoCovarianceFormula P F X H Y)
    (he : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → (r : EReal) < T → H (ω,r) = G (ω,r)) :
    ItoCovarianceFormula P F X G Y := by
  classical
  let J := fun z : Ω × ℝ => if 0 < z.2 ∧ (z.2 : EReal) < T then G z else H z
  have hJ : ItoCovarianceFormula P F X J Y := by
    apply Asakura.Chapter7.ito_integrand_common_ae P F X Y H J h
    filter_upwards [he] with ω hω
    intro r
    by_cases hr : 0 < r ∧ (r : EReal) < T
    · simpa only [J,hr,and_self,ite_true] using hω r hr.1 hr.2
    · simp only [J,hr,ite_false]
  apply hJ.congr_on_positive_time_domain P F X Y J G
  intro ω r hr hrT
  simp only [J,hr,hrT,and_self,ite_true]

end WMFKIExternalProbe
