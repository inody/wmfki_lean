import Lean_Code.PairSampling
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod

namespace WMFKI

open MeasureTheory

/-- 積空間で各観測値を固定した平均0から、観測σ代数での条件付き平均0を導く。 -/
theorem product_conditional_centered {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure Y) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Y × Z → ℝ) (hi : Integrable f (μ.prod ν))
    (hc : ∀ y, (∫ z, f (y, z) ∂ν) = 0) :
    (μ.prod ν)[f | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ.prod ν] 0 := by
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq measurable_fst.comap_le hi
  · intro s _ _
    exact integrable_zero _ _ _
  · intro s hs _
    obtain ⟨t, ht, rfl⟩ := hs
    have hset : (Prod.fst ⁻¹' t : Set (Y × Z)) = t ×ˢ Set.univ := by ext x; simp
    rw [hset, ← Measure.restrict_prod_eq_prod_univ]
    have hir : Integrable f ((μ.restrict t).prod ν) := by
      rw [Measure.restrict_prod_eq_prod_univ]
      exact hi.restrict
    simpa only [Pi.zero_apply, hc, integral_zero] using (integral_prod f hir).symm
  · exact stronglyMeasurable_const.aestronglyMeasurable

/-- 実際の一様ペア抽出に対する条件付き中心化。観測の法は任意。 -/
theorem pairRowError_conditional_mean {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T P N : ℕ} [Fact (2 ≤ N)]
    (L : ℕ) (h : Y → Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ)
    (hi : Integrable (fun z => pairRowError L (h z.1) w z.2)
      (μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N)))) :
    condExp (MeasurableSpace.comap Prod.fst inferInstance)
      (μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N)))
      (fun z => pairRowError L (h z.1) w z.2) =ᵐ[
          μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))] 0 :=
  product_conditional_centered μ _ _ hi (fun y => pairRowError_mean L (h y) w)

end WMFKI
