import WMFKI_Stochastic.FiniteMeasureFourthIntegral

open MeasureTheory Set
open WMFKISynchronousModel WMFKIIndependentFourth
open scoped NNReal
namespace WMFKIRealizedFluctuation
variable {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω] {d N : ℕ}

noncomputable def fluctuationTimeEnvelope (π : Measure A) (P : Measure Ω) (T : ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d)) (i : Fin N)
    (z : (Fin N → A) × (Fin N → Ω)) : ℝ :=
  ∫ s in (0 : ℝ)..T, ‖arrayFluctuation π P K Y i s z‖

theorem fluctuation_time_nonneg (π : Measure A) (P : Measure Ω) {T : ℝ} (hT : 0 ≤ T)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d)) (i : Fin N)
    (z : (Fin N → A) × (Fin N → Ω)) : 0 ≤ fluctuationTimeEnvelope π P T K Y i z :=
  intervalIntegral.integral_nonneg hT (fun _ _ => norm_nonneg _)

/-- 実際の揺らぎの全時間積分のL4。Fubini前に積空間での可積分性を証明する。 -/
theorem fluctuation_time_fourth (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P] {T R C : ℝ} (hT : 0 ≤ T)
    {ξ : A → EuclideanSpace ℝ (Fin d)} {D Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d)}
    {L : ℝ≥0} {K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hK : LipschitzWith L K) (h : ArrayNonlinearFamily π P T K ξ D Y R)
    (hF : UniformFluctuationFourth π P T K Y C) (hN : 0 < N) (i : Fin N) :
    MemLp (fluctuationTimeEnvelope π P T K Y i) 4 (arrayMeasure π P (Fin N)) ∧
    (∫ z, (fluctuationTimeEnvelope π P T K Y i z)^4 ∂arrayMeasure π P (Fin N)) ≤ T^4*C/(N : ℝ)^2 ∧
    (∀ᵐ z ∂arrayMeasure π P (Fin N), IntervalIntegrable
      (fun s => ‖arrayFluctuation π P K Y i s z‖) volume 0 T) := by
  let μ := volume.restrict (Ioc (0 : ℝ) T)
  have hm : StronglyMeasurable (fun z : ℝ × ((Fin N → A) × (Fin N → Ω)) =>
      ‖arrayFluctuation π P K Y i z.1 z.2‖) := (array_fluctuation_jointly_measurable hK h N i).norm
  have hf : ∀ᵐ s ∂μ,
      MemLp (fun z => ‖arrayFluctuation π P K Y i s z‖) 4 (arrayMeasure π P (Fin N)) ∧
      (∫ z, ‖arrayFluctuation π P K Y i s z‖^4 ∂arrayMeasure π P (Fin N)) ≤ C/(N : ℝ)^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact ⟨(hF.2 N hN i s ⟨hs.1.le,hs.2⟩).1.norm,(hF.2 N hN i s ⟨hs.1.le,hs.2⟩).2⟩
  have hμ : μ.real univ = T := by
    simp [μ,measureReal_def,Real.volume_Ioc,ENNReal.toReal_ofReal hT]
  obtain ⟨hE,hB⟩ := finite_integral_fourth_moment μ (arrayMeasure π P (Fin N)) _ hm (C/(N : ℝ)^2) hf
  have he : (fun z => ∫ s, ‖arrayFluctuation π P K Y i s z‖ ∂μ) = fluctuationTimeEnvelope π P T K Y i := by
    funext z
    rw [fluctuationTimeEnvelope,intervalIntegral.integral_of_le hT]
  rw [he] at hE
  refine ⟨hE,?_,?_⟩
  · simpa only [← he,hμ,mul_div_assoc] using hB
  · have h4 := product_fourth_integrable μ (arrayMeasure π P (Fin N)) _ hm (C/(N : ℝ)^2) hf
    filter_upwards [h4.prod_left_ae] with z hz
    have hLp := l4_of_integrable_fourth μ (hm.measurable.comp (measurable_id.prodMk measurable_const)) hz
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr (hLp.integrable (by norm_num))

end WMFKIRealizedFluctuation
