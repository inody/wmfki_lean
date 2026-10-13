import WMFKI_Stochastic.PopulationFeatureLaw

open MeasureTheory ProbabilityTheory Set
open WMFKIFeatureCoupling WMFKISynchronousModel WMFKIIIDPairs
open scoped BigOperators
namespace WMFKIPopulationDesign
variable {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω] {d : ℕ}

/-- 非対角の入力対にだけ積法則を適用し、可積分性を確保した後で和と時間積分を交換。 -/
theorem copy_average_identification (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P] (N : ℕ) (T : ℝ)
    (ψ : ℝ → ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d))
    (hi : ∀ᵐ z ∂(π.prod P).prod (π.prod P), IntervalIntegrable
      (fun s => inputPairFeature ψ φ K Y (s,z)) volume 0 T) :
    continuousPairAverage N T (fun t i j z => weakPairFeature ψ φ K t (arrayCopy Y i t z) (arrayCopy Y j t z)) =ᵐ[arrayMeasure π P (Fin N)]
      iidPairStatistic arrayInput (timePairKernel T ψ φ K Y) := by
  have ha : ∀ᵐ z ∂arrayMeasure π P (Fin N), ∀ p : Fin N × Fin N,
      IntervalIntegrable (fun s => if p.1=p.2 then 0 else
        inputPairFeature ψ φ K Y (s,(arrayInput p.1 z,arrayInput p.2 z))) volume 0 T := by
    apply ae_all_iff.mpr
    intro p
    by_cases hp : p.1=p.2
    · simp only [hp,ite_true]
      exact ae_of_all _ (fun _ => intervalIntegrable_const)
    · simp only [hp,ite_false]
      exact (array_pair_preserving π P p.1 p.2 hp).quasiMeasurePreserving.ae hi
  filter_upwards [ha] with z hz
  change (∫ s in (0 : ℝ)..T, (N : ℝ)⁻¹^2*∑ i,∑ j,if i=j then 0 else
    inputPairFeature ψ φ K Y (s,(arrayInput i z,arrayInput j z))) =
    (N : ℝ)⁻¹^2*∑ p : Fin N × Fin N, if p.1=p.2 then 0 else
      ∫ s in (0 : ℝ)..T, inputPairFeature ψ φ K Y (s,(arrayInput p.1 z,arrayInput p.2 z))
  rw [intervalIntegral.integral_const_mul]
  have he (s : ℝ) : (∑ i,∑ j,if i=j then 0 else inputPairFeature ψ φ K Y (s,(arrayInput i z,arrayInput j z))) =
      ∑ p : Fin N × Fin N, if p.1=p.2 then 0 else inputPairFeature ψ φ K Y (s,(arrayInput p.1 z,arrayInput p.2 z)) :=
    (Fintype.sum_prod_type (fun p : Fin N × Fin N => if p.1=p.2 then (0 : ℝ) else
      inputPairFeature ψ φ K Y (s,(arrayInput p.1 z,arrayInput p.2 z)))).symm
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum (fun p _ => hz p)]
  apply congrArg (fun q : ℝ => (N : ℝ)⁻¹^2*q)
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.1=p.2 <;> simp [hp]

/-- 原稿形式の実際のコピー設計と、静的P2の入力対統計を行列として同定。 -/
theorem copy_design_identification (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P] (N nr nc : ℕ) (T : ℝ)
    (ψ : Fin nr → ℝ → ℝ) (φ : Fin nr → EuclideanSpace ℝ (Fin d) → ℝ)
    (atom : Fin nc → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d))
    (hi : ∀ a m, ∀ᵐ z ∂(π.prod P).prod (π.prod P), IntervalIntegrable
      (fun s => inputPairFeature (ψ a) (φ a) (atom m) Y (s,z)) volume 0 T) :
    continuousFeatureDesign N nr nc T ψ φ atom (arrayCopy Y) =ᵐ[arrayMeasure π P (Fin N)]
      iidPairMatrix nr nc arrayInput (fun a m => timePairKernel T (ψ a) (φ a) (atom m) Y) := by
  have ha := ae_all_iff.mpr (fun a => ae_all_iff.mpr (fun m =>
    copy_average_identification π P N T (ψ a) (φ a) (atom m) Y (hi a m)))
  filter_upwards [ha] with z hz
  funext a m
  exact congrArg (fun q : ℝ => (Real.sqrt (nr : ℝ))⁻¹*q) (hz a m)

end WMFKIPopulationDesign
