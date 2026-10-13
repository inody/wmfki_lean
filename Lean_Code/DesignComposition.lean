import Lean_Code.SamplingRegularity

namespace WMFKI
open MeasureTheory

/-- 条件付き中心化により全行列のFrobenius二乗平均を加法的に分解する。 -/
theorem matrix_observation_pythagoras {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L M : ℕ} (A : Ω → Matrix (Fin L) (Fin M) ℝ)
    (D : Ω × Ξ → Matrix (Fin L) (Fin M) ℝ) (C : Matrix (Fin L) (Fin M) ℝ)
    (hm : ∀ a m, Measurable (fun y => A y a m))
    (hh : ∀ a m, MemLp (fun y => A y a m) 2 μ)
    (hd : ∀ a m, MemLp (fun z => D z a m) 2 (μ.prod ν))
    (hc : ∀ a m, (μ.prod ν)[(fun z => D z a m) |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ.prod ν] 0) :
    (∫ z, frobenius (A z.1 + D z - C) ^ 2 ∂μ.prod ν) =
      (∫ y, frobenius (A y - C) ^ 2 ∂μ) + ∫ z, frobenius (D z) ^ 2 ∂μ.prod ν := by
  have hf (a : Fin L) (m : Fin M) : MemLp (fun y => A y a m - C a m) 2 μ :=
    (hh a m).sub (memLp_const _)
  have hs (a : Fin L) (m : Fin M) :
      MemLp (fun z : Ω × Ξ => A z.1 a m + D z a m - C a m) 2 (μ.prod ν) :=
    (((hh a m).comp_measurePreserving measurePreserving_fst).add (hd a m)).sub (memLp_const _)
  have heq (a : Fin L) (m : Fin M) :
      (∫ z, (A z.1 a m + D z a m - C a m) ^ 2 ∂μ.prod ν) =
      (∫ y, (A y a m - C a m) ^ 2 ∂μ) + ∫ z, D z a m ^ 2 ∂μ.prod ν := by
    have hg : MemLp (fun z : Ω × Ξ => C a m - A z.1 a m) 2 (μ.prod ν) :=
      ((memLp_const _).sub (hh a m)).comp_measurePreserving measurePreserving_fst
    have hgm : StronglyMeasurable[MeasurableSpace.comap Prod.fst inferInstance]
        (fun z : Ω × Ξ => C a m - A z.1 a m) :=
      (measurable_const.sub (hm a m)).stronglyMeasurable.comp_measurable (comap_measurable Prod.fst)
    have ho := conditional_centered_second_moment_fun measurable_fst.comap_le
      (fun z => D z a m) (fun z => C a m - A z.1 a m) (hd a m) hg (hc a m)
      hgm.aestronglyMeasurable
    simp only [Real.norm_eq_abs, sq_abs] at ho
    have hl : (∫ z, (C a m - A z.1 a m - D z a m) ^ 2 ∂μ.prod ν) =
        ∫ z, (A z.1 a m + D z a m - C a m) ^ 2 ∂μ.prod ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring
    have hr : (∫ z, (C a m - A z.1 a m) ^ 2 ∂μ.prod ν) =
        ∫ y, (A y a m - C a m) ^ 2 ∂μ := by
      calc
        _ = ∫ y, (C a m - A y a m) ^ 2 ∂μ := by
          simpa using (integral_fun_fst (μ := μ) (ν := ν) (fun y => (C a m - A y a m) ^ 2))
        _ = _ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun y => by ring
    rwa [hl, hr] at ho
  simp_rw [frobenius_sq_sum]
  change (∫ z, ∑ a, ∑ m, (A z.1 a m + D z a m - C a m) ^ 2 ∂μ.prod ν) =
    (∫ y, ∑ a, ∑ m, (A y a m - C a m) ^ 2 ∂μ) +
      ∫ z, ∑ a, ∑ m, D z a m ^ 2 ∂μ.prod ν
  have his (a : Fin L) (m : Fin M) := (hs a m).integrable_sq
  have hif (a : Fin L) (m : Fin M) := (hf a m).integrable_sq
  have hid (a : Fin L) (m : Fin M) := (hd a m).integrable_sq
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun m _ => his a m)),
    integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun m _ => hif a m)),
    integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun m _ => hid a m))]
  simp_rw [integral_finsetSum _ (fun m _ => his _ m),
    integral_finsetSum _ (fun m _ => hif _ m), integral_finsetSum _ (fun m _ => hid _ m), heq]
  simp only [Finset.sum_add_distrib]

/-- 原稿4.9(iii)の分解。参照行列には任意の決定論的行列を取れる。 -/
theorem sampledDesign_second_moment_identity {Ω : Type*} [MeasurableSpace Ω]
    {L M T P N : ℕ} [Fact (2 ≤ N)] (hP : 0 < P)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Fin L → Fin M → Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ)
    (C : Matrix (Fin L) (Fin M) ℝ)
    (hm : ∀ a m t p, Measurable (fun y => h y a m t p))
    (hh : ∀ a m t p, MemLp (fun y => h y a m t p) 2 μ) :
    (∫ z, frobenius (sampledPairDesign (P := P) h w z - C) ^ 2
      ∂μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))) =
      (∫ y, frobenius (fullPairDesign h w y - C) ^ 2 ∂μ) +
      ∫ z, frobenius (sampledPairDesign h w z - fullPairDesign h w z.1) ^ 2
        ∂μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N)) := by
  have hd (a : Fin L) (m : Fin M) :
      MemLp (fun z => (sampledPairDesign (P := P) h w z - fullPairDesign h w z.1) a m) 2
        (μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))) := by
    simp_rw [← pairDesignError_eq_difference Fact.out hP]
    exact pairRowError_joint_memLp μ L (fun y t p => h y a m t p) w (hm a m) (hh a m)
  have hi := matrix_observation_pythagoras μ (independentDraws (Fin T × Fin P) (OrderedPair N))
    (fullPairDesign h w) (fun z => sampledPairDesign h w z - fullPairDesign h w z.1) C
    (fullPairDesign_entry_measurable h w hm) (fullPairDesign_entry_memLp μ h w hh) hd
    (assembled_design_conditional_centered hP μ h w hm hh)
  have heq (z : Ω × ((Fin T × Fin P) → OrderedPair N)) :
      fullPairDesign h w z.1 + (sampledPairDesign h w z - fullPairDesign h w z.1) - C =
        sampledPairDesign h w z - C := by abel
  simpa only [heq] using hi

/-- 全ペアのFrobenius上界とペア誤差から、回帰で使う作用素誤差を供給する。 -/
theorem sampledDesign_operator_moments {Ω : Type*} [MeasurableSpace Ω]
    {L M T P N : ℕ} [Fact (2 ≤ N)] (hP : 0 < P) (hL : 0 < L)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Fin L → Fin M → Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ)
    (C : Matrix (Fin L) (Fin M) ℝ)
    (hm : ∀ a m t p, Measurable (fun y => h y a m t p))
    (hh : ∀ a m t p, MemLp (fun y => h y a m t p) 2 μ)
    (D0 CA : ℝ) (hCA0 : 0 ≤ CA)
    (hD : (∫ y, frobenius (fullPairDesign h w y - C) ^ 2 ∂μ) ≤ D0)
    (hCA : ∀ a m t p, (∫ y, h y a m t p ^ 2 ∂μ) ≤ CA) :
    Measurable (fun z => ‖matrixMap (sampledPairDesign (P := P) h w z) - matrixMap C‖ ^ 2) ∧
    Integrable (fun z => ‖matrixMap (sampledPairDesign h w z) - matrixMap C‖ ^ 2)
      (μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))) ∧
    (∫ z, ‖matrixMap (sampledPairDesign h w z) - matrixMap C‖ ^ 2
      ∂μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))) ≤
      D0 + M * CA * (∑ t, w t ^ 2) / P := by
  have hs := sampledPairDesign_entry_regular hP μ h w hm hh
  have hr := matrix_operator_moment_regular
    (μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N)))
    (fun z => sampledPairDesign h w z - C)
    (fun a m => (hs a m).1.sub measurable_const)
    (fun a m => (hs a m).2.sub (memLp_const _))
  simp_rw [matrixMap_sub] at hr
  refine ⟨hr.1, hr.2.1, hr.2.2.trans ?_⟩
  rw [sampledDesign_second_moment_identity hP μ h w C hm hh]
  exact add_le_add hD (assembled_design_second_moment hP hL μ h w CA hCA0 hm hh hCA)

end WMFKI
