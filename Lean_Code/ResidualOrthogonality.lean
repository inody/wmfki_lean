import Lean_Code.ConditionalOrthogonality
import Mathlib.MeasureTheory.Integral.Prod

namespace WMFKI
open MeasureTheory

/-- L2の同値類ではなく通常の関数を入力にする、既存の条件付き直交性の接続。 -/
theorem conditional_centered_second_moment_fun {Ω F : Type*}
    {m : MeasurableSpace Ω} [m0 : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (hm : m ≤ m0) (f g : Ω → F) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hcenter : μ[f | m] =ᵐ[μ] 0) (hgm : AEStronglyMeasurable[m] g μ) :
    (∫ ω, ‖g ω - f ω‖ ^ 2 ∂μ) =
      (∫ ω, ‖g ω‖ ^ 2 ∂μ) + ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
  have hc : μ[(fun ω => hf.toLp f ω) | m] =ᵐ[μ] 0 :=
    (condExp_congr_ae hf.coeFn_toLp).trans hcenter
  have hgm' : AEStronglyMeasurable[m] (hg.toLp g) μ := hgm.congr hg.coeFn_toLp.symm
  have ho := conditional_centered_second_moment hm (hf.toLp f) (hg.toLp g) hc hgm'
  have hleft : (∫ ω, ‖hg.toLp g ω - hf.toLp f ω‖ ^ 2 ∂μ) =
      ∫ ω, ‖g ω - f ω‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp, hf.coeFn_toLp] with ω hgw hfw
    rw [hgw, hfw]
  have hgint : (∫ ω, ‖hg.toLp g ω‖ ^ 2 ∂μ) = ∫ ω, ‖g ω‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with ω hω
    rw [hω]
  have hfint : (∫ ω, ‖hf.toLp f ω‖ ^ 2 ∂μ) = ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with ω hω
    rw [hω]
  rwa [hleft, hgint, hfint] at ho

/-- 観測可測な有限ベクトルと、条件付き中心化された誤差の二乗平均加法性。 -/
theorem finite_observation_pythagoras {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L : ℕ} (g : Ω → Fin L → ℝ) (f : Ω × Ξ → Fin L → ℝ)
    (hgm : ∀ a, Measurable (fun y => g y a)) (hg : ∀ a, MemLp (fun y => g y a) 2 μ)
    (hf : ∀ a, MemLp (fun z => f z a) 2 (μ.prod ν))
    (hc : ∀ a, (μ.prod ν)[(fun z => f z a) |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ.prod ν] 0) :
    (∫ z, ‖(WithLp.toLp 2 (fun a => g z.1 a - f z a) : EuclideanSpace ℝ (Fin L))‖ ^ 2
      ∂μ.prod ν) =
      (∫ y, ‖(WithLp.toLp 2 (g y) : EuclideanSpace ℝ (Fin L))‖ ^ 2 ∂μ) +
      ∫ z, ‖(WithLp.toLp 2 (f z) : EuclideanSpace ℝ (Fin L))‖ ^ 2 ∂μ.prod ν := by
  have hgprod (a : Fin L) : MemLp (fun z : Ω × Ξ => g z.1 a) 2 (μ.prod ν) :=
    (hg a).comp_measurePreserving measurePreserving_fst
  have heq (a : Fin L) : (∫ z, (g z.1 a - f z a) ^ 2 ∂μ.prod ν) =
      (∫ y, g y a ^ 2 ∂μ) + ∫ z, f z a ^ 2 ∂μ.prod ν := by
    have hmeas : StronglyMeasurable[MeasurableSpace.comap Prod.fst inferInstance]
        (fun z : Ω × Ξ => g z.1 a) :=
      (hgm a).stronglyMeasurable.comp_measurable (comap_measurable Prod.fst)
    have hh := conditional_centered_second_moment_fun measurable_fst.comap_le
      (fun z => f z a) (fun z => g z.1 a) (hf a) (hgprod a) (hc a)
      hmeas.aestronglyMeasurable
    simp only [Real.norm_eq_abs, sq_abs] at hh
    have hfst : (∫ z, g z.1 a ^ 2 ∂μ.prod ν) = ∫ y, g y a ^ 2 ∂μ := by
      simpa using (integral_fun_fst (μ := μ) (ν := ν) (fun y => g y a ^ 2))
    rwa [hfst] at hh
  have hs (a : Fin L) : Integrable (fun z => (g z.1 a - f z a) ^ 2) (μ.prod ν) :=
    ((hgprod a).sub (hf a)).integrable_sq
  simp only [EuclideanSpace.real_norm_sq_eq]
  change (∫ z, ∑ a, (g z.1 a - f z a) ^ 2 ∂μ.prod ν) =
    (∫ y, ∑ a, g y a ^ 2 ∂μ) + ∫ z, ∑ a, f z a ^ 2 ∂μ.prod ν
  rw [integral_finsetSum _ (fun a _ => hs a),
    integral_finsetSum _ (fun a _ => (hg a).integrable_sq),
    integral_finsetSum _ (fun a _ => (hf a).integrable_sq)]
  simp_rw [heq]
  exact Finset.sum_add_distrib

end WMFKI
