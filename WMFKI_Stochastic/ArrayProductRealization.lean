import WMFKI_Stochastic.NonlinearCopiesFromInputs

open MeasureTheory ProbabilityTheory
namespace WMFKISynchronousModel

variable {A Ω I : Type*} [MeasurableSpace A] [MeasurableSpace Ω]

def joinArrays (z : (I → A) × (I → Ω)) (i : I) : A × Ω := (z.1 i,z.2 i)

noncomputable abbrev arrayMeasure (π : Measure A) (P : Measure Ω) (I : Type*) [Fintype I] :=
  (Measure.pi (fun _ : I => π)).prod (Measure.pi (fun _ : I => P))

/-- 配列の分離は実際の測度保存写像。 -/
theorem split_arrays_preserving [Fintype I] (π : Measure A) (P : Measure Ω)
    [SigmaFinite π] [SigmaFinite P] :
    MeasurePreserving (fun x : I → A × Ω => ((fun i => (x i).1),(fun i => (x i).2)))
      (Measure.pi (fun _ : I => π.prod P)) (arrayMeasure π P I) :=
  measurePreserving_arrowProdEquivProdArrow A Ω I (fun _ => π) (fun _ => P)

/-- コピーに元と同じ初期値・Brownian標本を渡す結合写像。 -/
theorem join_arrays_preserving [Fintype I] (π : Measure A) (P : Measure Ω)
    [SigmaFinite π] [SigmaFinite P] :
    MeasurePreserving (joinArrays : (I → A) × (I → Ω) → I → A × Ω)
      (arrayMeasure π P I) (Measure.pi (fun _ : I => π.prod P)) :=
  MeasurePreserving.symm (MeasurableEquiv.arrowProdEquivProdArrow A Ω I)
    (measurePreserving_arrowProdEquivProdArrow A Ω I (fun _ => π) (fun _ => P))

theorem joined_coordinate_preserving [Fintype I] (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P] (i : I) :
    MeasurePreserving (fun z : (I → A) × (I → Ω) => (z.1 i,z.2 i)) (arrayMeasure π P I) (π.prod P) :=
  (measurePreserving_eval (fun _ : I => π.prod P) i).comp (join_arrays_preserving π P)

/-- ベクトル全体同士の独立性。座標ペアの独立性から推論しない。 -/
theorem initial_array_independent_drivers [Fintype I] (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P]
    {D : Type*} [MeasurableSpace D] (W : (I → Ω) → D) (hW : Measurable W) :
    IndepFun (Prod.fst : (I → A) × (I → Ω) → I → A) (fun z => W z.2) (arrayMeasure π P I) :=
  indepFun_prod measurable_id hW

end WMFKISynchronousModel
