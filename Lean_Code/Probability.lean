import Lean_Code.Definitions
import Mathlib.Tactic

namespace WMFKI

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem secondMoment_good_event (f : Ω → ℝ) (V ε : ℝ)
    (_hf : Measurable f) (hi : Integrable f μ) (hn : ∀ ω, 0 ≤ f ω)
    (hV : 0 ≤ V) (hε : 0 < ε) (hm : (∫ ω, f ω ∂μ) ≤ V) :
    μ.real {ω | V / ε < f ω} ≤ ε := by
  by_cases hz : V = 0
  · subst V
    have heq : (∫ ω, f ω ∂μ) = 0 := le_antisymm hm (integral_nonneg hn)
    have hae := (integral_eq_zero_iff_of_nonneg hn hi).mp heq
    have hz : μ {ω | f ω ≠ 0} = 0 := by
      change ∀ᵐ ω ∂μ, f ω = 0 at hae
      exact ae_iff.mp hae
    have hnull : μ {ω | 0 < f ω} = 0 :=
      measure_mono_null (show {ω | 0 < f ω} ⊆ {ω | f ω ≠ 0} from
        fun _ h => ne_of_gt h) hz
    simpa [measureReal_def, hnull] using hε.le
  · have hp : 0 < V / ε := div_pos (lt_of_le_of_ne hV (Ne.symm hz)) hε
    have hmkv := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall hn) hi (V / ε)
    have hge : μ.real {ω | V / ε ≤ f ω} ≤ ε := by
      have hm' := hmkv.trans hm
      have hc : V / ε * ε = V := div_mul_cancel₀ V hε.ne'
      nlinarith
    have ht : μ.real {ω | V / ε < f ω} ≤ μ.real {ω | V / ε ≤ f ω} := by
      apply measureReal_mono ?_ (by finiteness)
      intro ω h
      change V / ε ≤ f ω
      exact le_of_lt h
    exact ht.trans hge

theorem good_event_intersection (s t : Set Ω) (δ ε : ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hδ : μ.real sᶜ ≤ δ) (hε : μ.real tᶜ ≤ ε) :
    1 - δ - ε ≤ μ.real (s ∩ t) := by
  have hu := measureReal_union_le (μ := μ) sᶜ tᶜ
  have htotal := measureReal_add_measureReal_compl (μ := μ) (hs.inter ht)
  rw [Set.compl_inter] at htotal
  simp only [probReal_univ] at htotal
  linarith

end WMFKI
