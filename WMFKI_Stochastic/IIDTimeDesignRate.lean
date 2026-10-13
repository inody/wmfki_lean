import WMFKI_Stochastic.CopyDesignIdentification

open MeasureTheory Set
open WMFKIFeatureCoupling WMFKIExternalProbe WMFKISynchronousModel WMFKIIIDPairs
open scoped NNReal
namespace WMFKIPopulationDesign
variable {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω] {d : ℕ}

/-- 静的P2を、実際に可測性・L2を証明した時間積分核へ適用する。 -/
theorem iid_time_design_rate (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P]
    (N nr nc : ℕ) (hN : 0 < N) (hnr : 0 < nr) (T : ℝ) (hT : 0 ≤ T)
    (ψ : Fin nr → ℝ → ℝ) (φ : Fin nr → EuclideanSpace ℝ (Fin d) → ℝ)
    (atom : Fin nc → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d))
    (B G H J C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) {D : ℝ≥0}
    (hφ : ∀ a, C3TestBounds d (φ a) G H J) (hψm : ∀ a, Measurable (ψ a))
    (hψ : ∀ a t, t ∈ Icc 0 T → |ψ a t| ≤ B)
    (hAtom : ∀ m x, ‖atom m x‖ ≤ C*(1+‖x‖)) (hAL : ∀ m, LipschitzWith D (atom m))
    (hYm : StronglyMeasurable (fun z : ℝ × (A × Ω) => Y z.1 z.2))
    (hY : ∀ t ∈ Icc 0 T, MemLp (Y t) 2 (π.prod P) ∧ (∫ z, ‖Y t z‖^2 ∂π.prod P) ≤ R) :
    let A := fun z => continuousFeatureDesign N nr nc T ψ φ atom (arrayCopy Y) z-
      populationFeatureDesign (π.prod P) T nr nc ψ φ atom Y
    MemLp (fun z => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => A z am.1 am.2) :
      EuclideanSpace ℝ (Fin nr × Fin nc))) 2 (arrayMeasure π P (Fin N)) ∧
    (∫ z, WMFKI.frobenius (A z)^2 ∂arrayMeasure π P (Fin N)) ≤
      5*(nc : ℝ)*T^2*featureSecondConstant B G C R/(N : ℝ) := by
  have hk a m := time_pair_kernel_moments (π.prod P) T hT (ψ a) (φ a) (atom m) Y (hψm a)
    (hAL m) B G H J C R hC (hφ a) (hψ a) (hAtom m) hYm hY
  have hp := population_design_identification (π.prod P) T hT nr nc ψ φ atom Y
    (fun m => (hAL m).continuous.measurable) hφ hYm (fun a m => (hk a m).2.2.2.1)
  have hc := copy_design_identification π P N nr nc T ψ φ atom Y (fun a m => (hk a m).2.2.2.2)
  have hpos : 0 ≤ T^2*featureSecondConstant B G C R :=
    mul_nonneg (sq_nonneg _) (feature_second_constant_nonneg _ _ _ _ hR)
  obtain ⟨hl,hb⟩ := iid_pair_matrix_frobenius_rate (arrayMeasure π P (Fin N)) (π.prod P) N nr nc hN hnr
    arrayInput (array_inputs_independent π P N) (fun i => (array_input_preserving π P i).measurable)
    (fun i => (array_input_preserving π P i).hasLaw)
    (fun a m => timePairKernel T (ψ a) (φ a) (atom m) Y)
    (fun a m => (hk a m).1) (fun a m => (hk a m).2.1)
    (T^2*featureSecondConstant B G C R) hpos (fun a m => (hk a m).2.2.1)
  rw [hp] at hl hb
  refine ⟨MemLp.ae_eq ?_ hl,?_⟩
  · filter_upwards [hc] with z hz
    rw [hz]
  · calc
      _ = ∫ z, WMFKI.frobenius (iidPairMatrix nr nc arrayInput
          (fun a m => timePairKernel T (ψ a) (φ a) (atom m) Y) z-
          populationFeatureDesign (π.prod P) T nr nc ψ φ atom Y)^2 ∂arrayMeasure π P (Fin N) := by
        apply integral_congr_ae
        filter_upwards [hc] with z hz
        rw [hz]
      _ ≤ 5*(nc : ℝ)*(T^2*featureSecondConstant B G C R)/(N : ℝ) := hb
      _ = _ := by ring

end WMFKIPopulationDesign
