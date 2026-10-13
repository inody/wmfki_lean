import WMFKI_Stochastic.MeanFieldFiniteHorizon

open MeasureTheory Set

namespace WMFKIMeanFieldAdapted
variable {Ω E : Type*} [m : MeasurableSpace Ω] [MetricSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- 完備化された部分sigma代数上では、ambient可測な零集合変更が可測性を保つ。 -/
theorem measurable_of_ae_eq_complete_subsigma (P : Measure Ω) (F : MeasurableSpace Ω)
    (hF : F ≤ m) (hnull : ∀ s, MeasurableSet[m] s → P s = 0 → MeasurableSet[F] s)
    {f g : Ω → E} (hf : Measurable[m] f) (hg : Measurable[F] g) (he : f =ᵐ[P] g) :
    Measurable[F] f := by
  let D := {ω | f ω ≠ g ω}
  have hgm : Measurable[m] g := hg.mono hF le_rfl
  have hDm : MeasurableSet[m] D := (measurableSet_eq_fun hf hgm).compl
  have hDz : P D = 0 := ae_iff.mp he
  have hDF : MeasurableSet[F] D := hnull D hDm hDz
  intro s hs
  have hsmall : MeasurableSet[F] ((f ⁻¹' s) ∩ D) :=
    hnull _ ((hf hs).inter hDm) (measure_mono_null inter_subset_right hDz)
  have heq : f ⁻¹' s = ((g ⁻¹' s) \ D) ∪ ((f ⁻¹' s) ∩ D) := by
    ext ω
    by_cases h : f ω = g ω <;> simp [D,h]
  rw [heq]
  exact ((hg hs).diff hDF).union hsmall

/-- 実時刻の有限区間での適合性。端点時刻のsigma代数を明示する。 -/
def AdaptedOn (F : ℝ → MeasurableSpace Ω) (T : ℝ) (X : ℝ → Ω → E) : Prop :=
  ∀ t ∈ Icc 0 T, Measurable[F t] (X t)

end WMFKIMeanFieldAdapted
