import WMFKI_Stochastic.InputArrayLaws

open MeasureTheory Set
open WMFKIFeatureCoupling WMFKIExternalProbe
open scoped NNReal
namespace WMFKIPopulationDesign
variable {Z : Type*} [MeasurableSpace Z] {d : ℕ}

noncomputable def inputPairFeature (ψ : ℝ → ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Y : ℝ → Z → EuclideanSpace ℝ (Fin d)) (z : ℝ × (Z × Z)) : ℝ :=
  weakPairFeature ψ φ K z.1 (Y z.1 z.2.1) (Y z.1 z.2.2)

noncomputable def timePairKernel (T : ℝ) (ψ : ℝ → ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Y : ℝ → Z → EuclideanSpace ℝ (Fin d)) (z : Z × Z) : ℝ :=
  ∫ s in (0 : ℝ)..T, inputPairFeature ψ φ K Y (s,z)

theorem input_pair_feature_measurable (ψ : ℝ → ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Y : ℝ → Z → EuclideanSpace ℝ (Fin d)) (hψ : Measurable ψ)
    {G H J : ℝ} (hφ : C3TestBounds d φ G H J) {D : ℝ≥0} (hK : LipschitzWith D K)
    (hY : StronglyMeasurable (fun z : ℝ × Z => Y z.1 z.2)) :
    StronglyMeasurable (inputPairFeature ψ φ K Y) := by
  exact weak_pair_feature_jointly_measurable ψ φ K hψ hφ hK
    (fun t (z : Z × Z) => Y t z.1) (fun t (z : Z × Z) => Y t z.2)
    (hY.comp_measurable (measurable_fst.prodMk measurable_snd.fst))
    (hY.comp_measurable (measurable_fst.prodMk measurable_snd.snd))

/-- 入力の対での成長評価。時間方向の独立性は不要。 -/
theorem input_pair_feature_second (ρ : Measure Z) [IsProbabilityMeasure ρ]
    (ψ : ℝ → ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hKm : Measurable K)
    (Y : ℝ → Z → EuclideanSpace ℝ (Fin d))
    (B G H J C R : ℝ) (hC : 0 ≤ C) (hφ : C3TestBounds d φ G H J)
    (hK : ∀ x, ‖K x‖ ≤ C*(1+‖x‖)) (t : ℝ) (hψ : |ψ t| ≤ B)
    (hYm : Measurable (Y t)) (hY : MemLp (Y t) 2 ρ) (hb : (∫ z, ‖Y t z‖^2 ∂ρ) ≤ R) :
    MemLp (fun z => inputPairFeature ψ φ K Y (t,z)) 2 (ρ.prod ρ) ∧
    (∫ z, (inputPairFeature ψ φ K Y (t,z))^2 ∂ρ.prod ρ) ≤ featureSecondConstant B G C R := by
  have hl := hY.comp_measurePreserving (measurePreserving_fst (μ := ρ) (ν := ρ))
  have hr := hY.comp_measurePreserving (measurePreserving_snd (μ := ρ) (ν := ρ))
  have hbl : (∫ z : Z × Z, ‖Y t z.1‖^2 ∂ρ.prod ρ) ≤ R := by
    exact ((measurePreserving_fst (μ := ρ) (ν := ρ)).hasLaw.integral_comp (hYm.norm.pow_const 2).aestronglyMeasurable).trans_le hb
  have hbr : (∫ z : Z × Z, ‖Y t z.2‖^2 ∂ρ.prod ρ) ≤ R := by
    exact ((measurePreserving_snd (μ := ρ) (ν := ρ)).hasLaw.integral_comp (hYm.norm.pow_const 2).aestronglyMeasurable).trans_le hb
  exact weak_pair_feature_second (ρ.prod ρ) ψ φ K hKm B G H J C R hC hφ hK t hψ
    (fun z => Y t z.1) (fun z => Y t z.2) (hYm.comp measurable_fst) (hYm.comp measurable_snd) hl hr hbl hbr

/-- 実際の時間積分核の可測性・L2・モーメント・Fubini前提・a.e.時間可積分性を同時に構成。 -/
theorem time_pair_kernel_moments (ρ : Measure Z) [IsProbabilityMeasure ρ]
    (T : ℝ) (hT : 0 ≤ T) (ψ : ℝ → ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Y : ℝ → Z → EuclideanSpace ℝ (Fin d)) (hψm : Measurable ψ)
    {D : ℝ≥0} (hKL : LipschitzWith D K) (B G H J C R : ℝ) (hC : 0 ≤ C)
    (hφ : C3TestBounds d φ G H J) (hψ : ∀ t ∈ Icc 0 T, |ψ t| ≤ B)
    (hK : ∀ x, ‖K x‖ ≤ C*(1+‖x‖))
    (hYm : StronglyMeasurable (fun z : ℝ × Z => Y z.1 z.2))
    (hY : ∀ t ∈ Icc 0 T, MemLp (Y t) 2 ρ ∧ (∫ z, ‖Y t z‖^2 ∂ρ) ≤ R) :
    Measurable (timePairKernel T ψ φ K Y) ∧ MemLp (timePairKernel T ψ φ K Y) 2 (ρ.prod ρ) ∧
    (∫ z, (timePairKernel T ψ φ K Y z)^2 ∂ρ.prod ρ) ≤ T^2*featureSecondConstant B G C R ∧
    Integrable (inputPairFeature ψ φ K Y) ((volume.restrict (Ioc (0 : ℝ) T)).prod (ρ.prod ρ)) ∧
    (∀ᵐ z ∂ρ.prod ρ, IntervalIntegrable (fun s => inputPairFeature ψ φ K Y (s,z)) volume 0 T) := by
  let μ := volume.restrict (Ioc (0 : ℝ) T)
  have hm := input_pair_feature_measurable ψ φ K Y hψm hφ hKL hYm
  have hf : ∀ᵐ s ∂μ, MemLp (fun z => inputPairFeature ψ φ K Y (s,z)) 2 (ρ.prod ρ) ∧
      (∫ z, (inputPairFeature ψ φ K Y (s,z))^2 ∂ρ.prod ρ) ≤ featureSecondConstant B G C R := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact input_pair_feature_second ρ ψ φ K hKL.continuous.measurable Y B G H J C R hC hφ hK s
      (hψ s ⟨hs.1.le,hs.2⟩) (hYm.measurable.comp (measurable_const.prodMk measurable_id))
      (hY s ⟨hs.1.le,hs.2⟩).1 (hY s ⟨hs.1.le,hs.2⟩).2
  obtain ⟨hi,hl,hb⟩ := finite_integral_second_moment μ (ρ.prod ρ) _ hm _ hf
  have he : (fun z => ∫ s, inputPairFeature ψ φ K Y (s,z) ∂μ) = timePairKernel T ψ φ K Y := by
    funext z
    rw [timePairKernel,intervalIntegral.integral_of_le hT]
  have hμ : μ.real univ = T := by simp [μ,measureReal_def,Real.volume_Ioc,ENNReal.toReal_ofReal hT]
  refine ⟨?_,?_,?_,hi,?_⟩
  · rw [← he]
    exact (hm.integral_prod_left' (μ := μ)).measurable
  · simpa only [he] using hl
  · simpa only [timePairKernel,intervalIntegral.integral_of_le hT,hμ] using hb
  · filter_upwards [hi.prod_left_ae] with z hz
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr hz

end WMFKIPopulationDesign
