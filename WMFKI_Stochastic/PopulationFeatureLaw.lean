import WMFKI_Stochastic.TimePairKernel

open MeasureTheory Set
open WMFKIFeatureCoupling WMFKIExternalProbe
open scoped NNReal
namespace WMFKIPopulationDesign
variable {Z : Type*} [MeasurableSpace Z] {d : ℕ}

theorem state_pair_preserving (ρ : Measure Z) [IsProbabilityMeasure ρ]
    (Y : Z → EuclideanSpace ℝ (Fin d)) (hY : Measurable Y) :
    MeasurePreserving (Prod.map Y Y) (ρ.prod ρ) ((ρ.map Y).prod (ρ.map Y)) := by
  have h : MeasurePreserving Y ρ (ρ.map Y) := ⟨hY,rfl⟩
  exact h.prod h

/-- 法則側の積分も可積分であることを証明し、実際のmu_t×mu_t積分へ移す。 -/
theorem instantaneous_feature_law (ρ : Measure Z) [IsProbabilityMeasure ρ]
    (ψ : ℝ → ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hKm : Measurable K)
    (Y : ℝ → Z → EuclideanSpace ℝ (Fin d)) {G H J : ℝ} (hφ : C3TestBounds d φ G H J)
    (t : ℝ) (hY : Measurable (Y t))
    (hi : Integrable (fun z => inputPairFeature ψ φ K Y (t,z)) (ρ.prod ρ)) :
    Integrable (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      weakPairFeature ψ φ K t q.1 q.2) ((ρ.map (Y t)).prod (ρ.map (Y t))) ∧
    (∫ z, inputPairFeature ψ φ K Y (t,z) ∂ρ.prod ρ) =
      ∫ q, weakPairFeature ψ φ K t q.1 q.2 ∂((ρ.map (Y t)).prod (ρ.map (Y t))) := by
  have hm : Measurable (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => weakPairFeature ψ φ K t q.1 q.2) :=
    measurable_const.mul (((gradient_measurable_of_c3 hφ).comp measurable_fst).inner
      (hKm.comp (measurable_fst.sub measurable_snd)))
  have hp := state_pair_preserving ρ (Y t) hY
  exact ⟨(hp.integrable_comp hm.aestronglyMeasurable).mp hi,hp.hasLaw.integral_comp hm.aestronglyMeasurable⟩

/-- 時間と入力対のFubiniを、真の積空間可積分性の下で行う。 -/
theorem time_pair_kernel_mean (ρ : Measure Z) [IsProbabilityMeasure ρ]
    (T : ℝ) (hT : 0 ≤ T) (ψ : ℝ → ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hKm : Measurable K)
    (Y : ℝ → Z → EuclideanSpace ℝ (Fin d)) {G H J : ℝ} (hφ : C3TestBounds d φ G H J)
    (hY : StronglyMeasurable (fun z : ℝ × Z => Y z.1 z.2))
    (hi : Integrable (inputPairFeature ψ φ K Y) ((volume.restrict (Ioc (0 : ℝ) T)).prod (ρ.prod ρ))) :
    IntervalIntegrable (fun s => ∫ q, weakPairFeature ψ φ K s q.1 q.2 ∂((ρ.map (Y s)).prod (ρ.map (Y s)))) volume 0 T ∧
    (∫ z, timePairKernel T ψ φ K Y z ∂ρ.prod ρ) =
      ∫ s in (0 : ℝ)..T, ∫ q, weakPairFeature ψ φ K s q.1 q.2 ∂((ρ.map (Y s)).prod (ρ.map (Y s))) := by
  have he : (fun s => ∫ z, inputPairFeature ψ φ K Y (s,z) ∂ρ.prod ρ) =ᵐ[volume.restrict (Ioc (0 : ℝ) T)]
      fun s => ∫ q, weakPairFeature ψ φ K s q.1 q.2 ∂((ρ.map (Y s)).prod (ρ.map (Y s))) := by
    filter_upwards [hi.prod_right_ae] with s hs
    exact (instantaneous_feature_law ρ ψ φ K hKm Y hφ s
      (hY.measurable.comp (measurable_const.prodMk measurable_id)) hs).2
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr (hi.integral_prod_left.congr he),?_⟩
  simp_rw [timePairKernel,intervalIntegral.integral_of_le hT]
  rw [← integral_prod_symm _ hi,integral_prod _ hi]
  exact integral_congr_ae he

/-- 原稿の実際の母集団参照行列。mu_tは構成解のmap法則。 -/
noncomputable def populationFeatureDesign (ρ : Measure Z) (T : ℝ) (nr nc : ℕ)
    (ψ : Fin nr → ℝ → ℝ) (φ : Fin nr → EuclideanSpace ℝ (Fin d) → ℝ)
    (atom : Fin nc → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Y : ℝ → Z → EuclideanSpace ℝ (Fin d)) : Matrix (Fin nr) (Fin nc) ℝ :=
  fun a m => (Real.sqrt (nr : ℝ))⁻¹ * ∫ s in (0 : ℝ)..T,
    ∫ q, weakPairFeature (ψ a) (φ a) (atom m) s q.1 q.2 ∂((ρ.map (Y s)).prod (ρ.map (Y s)))

theorem population_design_identification (ρ : Measure Z) [IsProbabilityMeasure ρ]
    (T : ℝ) (hT : 0 ≤ T) (nr nc : ℕ)
    (ψ : Fin nr → ℝ → ℝ) (φ : Fin nr → EuclideanSpace ℝ (Fin d) → ℝ)
    (atom : Fin nc → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Y : ℝ → Z → EuclideanSpace ℝ (Fin d)) (hAtom : ∀ m, Measurable (atom m))
    {G H J : ℝ} (hφ : ∀ a, C3TestBounds d (φ a) G H J)
    (hY : StronglyMeasurable (fun z : ℝ × Z => Y z.1 z.2))
    (hi : ∀ a m, Integrable (inputPairFeature (ψ a) (φ a) (atom m) Y)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (ρ.prod ρ))) :
    WMFKIIIDPairs.populationPairMatrix ρ nr nc (fun a m => timePairKernel T (ψ a) (φ a) (atom m) Y) =
      populationFeatureDesign ρ T nr nc ψ φ atom Y := by
  funext a m
  unfold WMFKIIIDPairs.populationPairMatrix populationFeatureDesign
  rw [(time_pair_kernel_mean ρ T hT (ψ a) (φ a) (atom m) (hAtom m) Y (hφ a) hY (hi a m)).2]

end WMFKIPopulationDesign
