import WMFKI_Stochastic.ActualDesignCoupling
import WMFKI_Stochastic.IIDPairMatrix

open MeasureTheory ProbabilityTheory
open WMFKISynchronousModel WMFKIMeanFieldCopies
namespace WMFKIPopulationDesign
variable {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω]

def arrayInput {N : ℕ} (i : Fin N) (z : (Fin N → A) × (Fin N → Ω)) : A × Ω := (z.1 i,z.2 i)

/-- 独立なのは原始入力であって、相互作用粒子ではない。 -/
theorem array_inputs_independent (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P] (N : ℕ) :
    iIndepFun (arrayInput (A := A) (Ω := Ω) (N := N)) (arrayMeasure π P (Fin N)) := by
  exact independent_family_pullback (join_arrays_preserving π P)
    (fun i : Fin N => fun z : Fin N → A × Ω => z i) (fun i => measurable_pi_apply i)
    (iIndepFun_pi (fun _ => measurable_id.aemeasurable))

theorem array_input_preserving (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P] {N : ℕ} (i : Fin N) :
    MeasurePreserving (arrayInput i) (arrayMeasure π P (Fin N)) (π.prod P) := joined_coordinate_preserving π P i

/-- 対角は除外する。i=jにこの積法則を適用することはできない。 -/
theorem array_pair_preserving (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P] {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    MeasurePreserving (fun z => (arrayInput i z,arrayInput j z)) (arrayMeasure π P (Fin N))
      ((π.prod P).prod (π.prod P)) := by
  refine ⟨(array_input_preserving π P i).measurable.prodMk (array_input_preserving π P j).measurable,?_⟩
  exact (WMFKIIIDPairs.iid_pair_hasLaw (array_inputs_independent π P N)
    (fun k => (array_input_preserving π P k).hasLaw) hij).map_eq

end WMFKIPopulationDesign
