import WMFKI_Stochastic.IndependentBrownianFamilyProbe
import BrownianExists

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace WMFKIExternalProbe

/-- A finite independent Brownian family is itself constructed from the audited
scalar Brownian existence theorem, rather than postulated as an input package. -/
theorem exists_independent_brownian_family (n : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω),
      IsProbabilityMeasure P ∧ ∃ W : Fin n → ℝ≥0 → Ω → ℝ,
        (∀ i, IsBrownianReal (W i) P) ∧
        (∀ i t, Measurable (W i t)) ∧
        iIndepFun (fun i ω t => W i t ω) P := by
  obtain ⟨Ω,m,P,hP,W,hm,hc,hW,_⟩ := Asakura.brownian_motion_exists
  let := m
  let := hP
  let Q : Measure (Fin n → Ω) := Measure.pi (fun _ => P)
  let V : Fin n → ℝ≥0 → (Fin n → Ω) → ℝ := fun i t ω => W t (ω i)
  have hV i : IsBrownianReal (V i) Q := by
    refine ⟨⟨fun S => ?_⟩, Filter.Eventually.of_forall (fun ω => hc (ω i))⟩
    exact (hW.hasLaw S).comp (measurePreserving_eval (fun _ : Fin n => P) i).hasLaw
  have hVm i t : Measurable (V i t) := (hm t).comp (measurable_pi_apply i)
  have hp : Measurable (fun ω t => W t ω) := Measurable.of_eval hm
  have hVi : iIndepFun (fun i ω t => V i t ω) Q :=
    iIndepFun_pi (fun _ => hp.aemeasurable)
  exact ⟨Fin n → Ω,inferInstance,Q,inferInstance,V,hV,hVm,hVi⟩

end WMFKIExternalProbe
#print axioms WMFKIExternalProbe.exists_independent_brownian_family
