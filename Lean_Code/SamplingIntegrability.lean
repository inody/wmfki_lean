import Lean_Code.PairSampling
import Mathlib.MeasureTheory.Integral.Prod

namespace WMFKI

open MeasureTheory

variable {Y A : Type*} [MeasurableSpace Y] [Fintype A]
  [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- 有限な抽出空間では、各切片の可測性・可積分性から積空間の可積分性が従う。 -/
theorem integrable_finite_fibers {Z : Type*} [Fintype Z] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] (μ : Measure Y) (ν : Measure Z)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (f : Y × Z → ℝ)
    (hm : ∀ z, Measurable (fun y => f (y, z)))
    (hi : ∀ z, Integrable (fun y => f (y, z)) μ) : Integrable f (μ.prod ν) := by
  apply (integrable_prod_iff' (measurable_from_prod_countable_left hm).aestronglyMeasurable).mpr
  exact ⟨Filter.Eventually.of_forall hi, Integrable.of_finite⟩

omit [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem samplingError_observable {T P : ℕ} (h : Y → Fin T → A → ℝ) (w : Fin T → ℝ)
    (hm : ∀ t a, Measurable (fun y => h y t a)) (ω : (Fin T × Fin P) → A) :
    Measurable (fun y => samplingError (h y) w ω) := by
  unfold samplingError populationMean
  fun_prop

omit [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem samplingError_observation_memLp {T P : ℕ} (μ : Measure Y)
    (h : Y → Fin T → A → ℝ) (w : Fin T → ℝ)
    (hh : ∀ t a, MemLp (fun y => h y t a) 2 μ) (ω : (Fin T × Fin P) → A) :
    MemLp (fun y => samplingError (h y) w ω) 2 μ := by
  classical
  have hmean (t : Fin T) : MemLp (fun y => populationMean (h y t)) 2 μ := by
    have hs := memLp_finsetSum Finset.univ (fun a _ => hh t a)
    simpa only [populationMean, div_eq_mul_inv, mul_comm] using
      hs.const_mul ((Fintype.card A : ℝ)⁻¹)
  exact memLp_finsetSum Finset.univ fun i _ =>
    ((hh i.1 (ω i)).sub (hmean i.1)).const_mul (w i.1 / P)

theorem samplingError_joint_memLp {T P : ℕ} (μ : Measure Y) [IsProbabilityMeasure μ]
    (h : Y → Fin T → A → ℝ) (w : Fin T → ℝ)
    (hm : ∀ t a, Measurable (fun y => h y t a))
    (hh : ∀ t a, MemLp (fun y => h y t a) 2 μ) :
    MemLp (fun z => samplingError (h z.1) w z.2) 2
      (μ.prod (independentDraws (Fin T × Fin P) A)) := by
  have hobs := samplingError_observable (P := P) h w hm
  have hj : Measurable (fun z : Y × ((Fin T × Fin P) → A) =>
      samplingError (h z.1) w z.2) := measurable_from_prod_countable_left hobs
  apply (memLp_two_iff_integrable_sq hj.aestronglyMeasurable).mpr
  apply integrable_finite_fibers μ _ _
  · intro ω
    exact (hobs ω).pow_const 2
  · intro ω
    exact (memLp_two_iff_integrable_sq (hobs ω).aestronglyMeasurable).mp
      (samplingError_observation_memLp μ h w hh ω)

end WMFKI
