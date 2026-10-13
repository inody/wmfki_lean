import WMFKI_Stochastic.RealizedFluctuationFourth

open MeasureTheory Set
open WMFKISynchronousModel WMFKIMeanFieldPicard
open scoped NNReal
namespace WMFKIRealizedFluctuation
variable {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω] {d : ℕ}
  {π : Measure A} {P : Measure Ω} [IsProbabilityMeasure π] [IsProbabilityMeasure P]
  {T R : ℝ} {ξ : A → EuclideanSpace ℝ (Fin d)}
  {D Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d)}
  {K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}

omit [IsProbabilityMeasure π] [IsProbabilityMeasure P] in
/-- 一コピーの定数配列への制限により、母集団過程の時間共同可測性を得る。 -/
theorem base_jointly_measurable (h : ArrayNonlinearFamily π P T K ξ D Y R) :
    StronglyMeasurable (fun z : ℝ × (A × Ω) => Y z.1 z.2) := by
  have hm : Measurable (fun z : ℝ × (A × Ω) => (z.1,((fun _ : Fin 1 => z.2.1),(fun _ : Fin 1 => z.2.2)))) := by
    fun_prop
  exact (h.joint 1 (0 : Fin 1)).comp_measurable hm

/-- 平均場積分も実際の核の積分として扱い、時間と標本の共同強可測性を証明。 -/
theorem array_fluctuation_jointly_measurable {L : ℝ≥0} (hK : LipschitzWith L K)
    (h : ArrayNonlinearFamily π P T K ξ D Y R) (N : ℕ) (i : Fin N) :
    StronglyMeasurable (fun z : ℝ × ((Fin N → A) × (Fin N → Ω)) => arrayFluctuation π P K Y i z.1 z.2) := by
  have hy := base_jointly_measurable h
  have hc (j : Fin N) := (h.joint N j).measurable
  have hk := hK.continuous.measurable
  have hp : Measurable (fun u : ℝ × ((Fin N → A) × (Fin N → Ω)) =>
      WMFKIExternalProbe.particleDrift K (fun j => arrayCopy Y j u.1 u.2) i) := by
    unfold WMFKIExternalProbe.particleDrift
    apply (measurable_const_smul ((N : ℝ)⁻¹)).comp
    apply Finset.measurable_sum
    intro j _
    by_cases he : i = j
    · simp only [he,ite_true]
      exact measurable_const
    · simp only [he,ite_false]
      exact hk.comp ((hc i).sub (hc j))
  have hf : Measurable (fun z : (ℝ × ((Fin N → A) × (Fin N → Ω))) × (A × Ω) =>
      K (arrayCopy Y i z.1.1 z.1.2 - Y z.1.1 z.2)) :=
    hk.comp (((hc i).comp measurable_fst).sub
      (hy.measurable.comp (measurable_fst.fst.prodMk measurable_snd)))
  have hm : StronglyMeasurable (fun u : ℝ × ((Fin N → A) × (Fin N → Ω)) =>
      ∫ y, K (arrayCopy Y i u.1 u.2-y) ∂((π.prod P).map (Y u.1))) := by
    have raw := hf.stronglyMeasurable.integral_prod_right' (ν := π.prod P)
    convert raw using 1
    funext u
    exact (law_drift_map hK (hy.measurable.comp (measurable_const.prodMk measurable_id)) _).symm
  exact hp.stronglyMeasurable.sub hm

end WMFKIRealizedFluctuation
