import Lean_Code.DesignComposition
import Lean_Code.EstimatorRecovery

namespace WMFKI
open MeasureTheory

noncomputable def designSamplingBudget {T : ℕ} (M P : ℕ) (w : Fin T → ℝ) (D0 CA : ℝ) : ℝ :=
  D0 + M * CA * (∑ t, w t ^ 2) / P

noncomputable def residualSamplingBudget {T : ℕ} (P : ℕ) (w : Fin T → ℝ) (V0 CK : ℝ) : ℝ :=
  V0 + CK * (∑ t, w t ^ 2) / P

/-- 実際の標本行列・応答に構成済み擬似逆を適用する。既知supportへの制限は後の系で行う。 -/
theorem sampled_moorePenrose_recovery {Ω : Type*} [MeasurableSpace Ω]
    {L M T P N : ℕ} [Fact (2 ≤ N)] (hP : 0 < P) (hL : 0 < L)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Fin L → Fin M → Fin T → OrderedPair N → ℝ)
    (w : Fin T → ℝ) (b : Ω → Fin L → ℝ) (θ : Fin M → ℝ)
    (A : Matrix (Fin L) (Fin M) ℝ)
    (hm : ∀ a m t p, Measurable (fun y => h y a m t p))
    (hh : ∀ a m t p, MemLp (fun y => h y a m t p) 2 μ)
    (hbm : ∀ a, Measurable (fun y => b y a)) (hb : ∀ a, MemLp (fun y => b y a) 2 μ)
    (D0 V0 CA CK γ δ ε : ℝ) (hCA0 : 0 ≤ CA) (hCK0 : 0 ≤ CK)
    (hD : (∫ y, frobenius (fullPairDesign h w y - A) ^ 2 ∂μ) ≤ D0)
    (hV : (∫ y, ‖fullRegressionResidual h w b θ y‖ ^ 2 ∂μ) ≤ V0)
    (hCA : ∀ a m t p, (∫ y, h y a m t p ^ 2 ∂μ) ≤ CA)
    (hCK : ∀ a t p, (∫ y, (∑ m, θ m * h y a m t p) ^ 2 ∂μ) ≤ CK)
    (hγ : 0 < γ) (hδ : 0 < δ) (hε : 0 < ε) (hprob : δ + ε < 1)
    (hA : LowerBound (matrixMap A) γ)
    (hsmall : designSamplingBudget M P w D0 CA ≤ δ * γ ^ 2 / 4) :
    ∃ G : Set (Ω × ((Fin T × Fin P) → OrderedPair N)), MeasurableSet G ∧
      1 - δ - ε ≤ (μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))).real G ∧
      ∀ z ∈ G, ‖moorePenrose (matrixMap (sampledPairDesign h w z)) (WithLp.toLp 2 (b z.1)) -
        WithLp.toLp 2 θ‖ ^ 2 ≤ 4 * residualSamplingBudget P w V0 CK / (ε * γ ^ 2) := by
  have hdes := sampledDesign_operator_moments hP hL μ h w A hm hh D0 CA hCA0 hD hCA
  have hres := sampledResidual_norm_sq_regular hP μ h w b θ hm hh hbm hb
  have hrv := sampledResidual_second_moment_bound hP hL μ h w b θ hm hh hbm hb V0 CK hCK0 hV hCK
  simp_rw [sampledResidual_eq_regression] at hres hrv
  have hv0 : 0 ≤ V0 := (integral_nonneg (fun y => sq_nonneg ‖fullRegressionResidual h w b θ y‖)).trans hV
  have hv : 0 ≤ residualSamplingBudget P w V0 CK := by unfold residualSamplingBudget; positivity
  exact oracle_moorePenrose_recovery
    (μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N)))
    (fun z => matrixMap (sampledPairDesign h w z)) (matrixMap A)
    (fun z => WithLp.toLp 2 (b z.1)) (WithLp.toLp 2 θ)
    γ δ ε (designSamplingBudget M P w D0 CA) (residualSamplingBudget P w V0 CK)
    hγ hδ hε hprob hv hA hdes.1 hres.1 hdes.2.1 hres.2 hdes.2.2 hrv hsmall

/-- 生の標本行列に正のペナルティのLASSOを適用し、定数144の評価へ接続する。 -/
theorem sampled_lasso_recovery {Ω : Type*} [MeasurableSpace Ω]
    {L M T P N : ℕ} [Fact (2 ≤ N)] (hP : 0 < P) (hL : 0 < L)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Fin L → Fin M → Fin T → OrderedPair N → ℝ)
    (w : Fin T → ℝ) (b : Ω → Fin L → ℝ) (θ : Fin M → ℝ)
    (A : Matrix (Fin L) (Fin M) ℝ) (S : Finset (Fin M))
    (hm : ∀ a m t p, Measurable (fun y => h y a m t p))
    (hh : ∀ a m t p, MemLp (fun y => h y a m t p) 2 μ)
    (hbm : ∀ a, Measurable (fun y => b y a)) (hb : ∀ a, MemLp (fun y => b y a) 2 μ)
    (D0 V0 CA CK γ R δ ε lam : ℝ) (hCA0 : 0 ≤ CA) (hCK0 : 0 ≤ CK)
    (hD : (∫ y, frobenius (fullPairDesign h w y - A) ^ 2 ∂μ) ≤ D0)
    (hV : (∫ y, ‖fullRegressionResidual h w b θ y‖ ^ 2 ∂μ) ≤ V0)
    (hCA : ∀ a m t p, (∫ y, h y a m t p ^ 2 ∂μ) ≤ CA)
    (hCK : ∀ a t p, (∫ y, (∑ m, θ m * h y a m t p) ^ 2 ∂μ) ≤ CK)
    (hγ : 0 < γ) (hR : 0 ≤ R) (hδ : 0 < δ) (hε : 0 < ε) (hprob : δ + ε < 1)
    (hlam : 0 < lam) (hsupp : ∀ i ∉ S, θ i = 0)
    (hA : ConeLowerBound (matrixMap A) S γ) (hcol : ColumnBound (matrixMap A) R)
    (hsmall : designSamplingBudget M P w D0 CA ≤ δ * γ ^ 2 / 4)
    (hpen : 2 * (R + γ / 2) * Real.sqrt (residualSamplingBudget P w V0 CK / ε) ≤ lam) :
    ∃ G : Set (Ω × ((Fin T × Fin P) → OrderedPair N)), MeasurableSet G ∧
      1 - δ - ε ≤ (μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))).real G ∧
      ∀ z ∈ G,
        SparseCone S (lassoEstimator (matrixMap (sampledPairDesign h w z))
          (WithLp.toLp 2 (b z.1)) lam hlam - WithLp.toLp 2 θ) ∧
        ‖lassoEstimator (matrixMap (sampledPairDesign h w z))
          (WithLp.toLp 2 (b z.1)) lam hlam - WithLp.toLp 2 θ‖ ^ 2 ≤
            144 * (S.card : ℝ) * lam ^ 2 / γ ^ 4 := by
  have hdes := sampledDesign_operator_moments hP hL μ h w A hm hh D0 CA hCA0 hD hCA
  have hres := sampledResidual_norm_sq_regular hP μ h w b θ hm hh hbm hb
  have hrv := sampledResidual_second_moment_bound hP hL μ h w b θ hm hh hbm hb V0 CK hCK0 hV hCK
  simp_rw [sampledResidual_eq_regression] at hres hrv
  have hv0 : 0 ≤ V0 := (integral_nonneg (fun y => sq_nonneg ‖fullRegressionResidual h w b θ y‖)).trans hV
  have hv : 0 ≤ residualSamplingBudget P w V0 CK := by unfold residualSamplingBudget; positivity
  exact lasso_estimator_recovery
    (μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N)))
    (fun z => matrixMap (sampledPairDesign h w z)) (matrixMap A)
    (fun z => WithLp.toLp 2 (b z.1)) (WithLp.toLp 2 θ) S
    γ R δ ε (designSamplingBudget M P w D0 CA) (residualSamplingBudget P w V0 CK) lam
    hγ hR hδ hε hprob hv hlam hsupp hA hcol hdes.1 hres.1 hdes.2.1 hres.2 hdes.2.2 hrv hsmall hpen

/-- 既知の列を選ぶ。残りの辞書列に下界を要求しない。 -/
def selectPairFeatures {Ω : Type*} {L M s T N : ℕ}
    (h : Ω → Fin L → Fin M → Fin T → OrderedPair N → ℝ) (e : Fin s → Fin M) :=
  fun y a j t p => h y a (e j) t p

theorem frobenius_select_sq_le {L M s : ℕ} (A : Matrix (Fin L) (Fin M) ℝ)
    (e : Fin s → Fin M) (he : Function.Injective e) :
    frobenius (A.submatrix id e) ^ 2 ≤ frobenius A ^ 2 := by
  simp_rw [frobenius_sq_sum]
  apply Finset.sum_le_sum
  intro a _
  change (∑ j, A a (e j) ^ 2) ≤ ∑ m, A a m ^ 2
  calc
    _ = ∑ m ∈ Finset.univ.image e, A a m ^ 2 :=
      (Finset.sum_image (f := fun m => A a m ^ 2) (s := Finset.univ)
        (fun i _ j _ h => he h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun m _ _ => sq_nonneg _)

theorem full_design_selected_second_moment_le {Ω : Type*} [MeasurableSpace Ω]
    {L M s T N : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Fin L → Fin M → Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ)
    (A : Matrix (Fin L) (Fin M) ℝ) (e : Fin s → Fin M) (he : Function.Injective e)
    (hm : ∀ a m t p, Measurable (fun y => h y a m t p))
    (hh : ∀ a m t p, MemLp (fun y => h y a m t p) 2 μ) :
    (∫ y, frobenius (fullPairDesign (selectPairFeatures h e) w y - A.submatrix id e) ^ 2 ∂μ) ≤
      ∫ y, frobenius (fullPairDesign h w y - A) ^ 2 ∂μ := by
  have hmA := fullPairDesign_entry_measurable h w hm
  have hhA := fullPairDesign_entry_memLp μ h w hh
  have hf := frobenius_sq_regular μ (fun y => fullPairDesign h w y - A)
    (fun a m => (hmA a m).sub measurable_const) (fun a m => (hhA a m).sub (memLp_const _))
  have hs := frobenius_sq_regular μ (fun y => (fullPairDesign h w y - A).submatrix id e)
    (fun a j => (hmA a (e j)).sub measurable_const)
    (fun a j => (hhA a (e j)).sub (memLp_const _))
  have heq (y : Ω) : fullPairDesign (selectPairFeatures h e) w y - A.submatrix id e =
      (fullPairDesign h w y - A).submatrix id e := rfl
  simp_rw [heq]
  exact integral_mono hs.2 hf.2 (fun y => frobenius_select_sq_le _ e he)

/-- 原稿の既知support版。参照行列の下界は選択した列にだけ要求する。 -/
theorem sampled_oracle_recovery {Ω : Type*} [MeasurableSpace Ω]
    {L M s T P N : ℕ} [Fact (2 ≤ N)] (hP : 0 < P) (hL : 0 < L)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Fin L → Fin M → Fin T → OrderedPair N → ℝ)
    (w : Fin T → ℝ) (b : Ω → Fin L → ℝ) (θS : Fin s → ℝ)
    (A : Matrix (Fin L) (Fin M) ℝ) (e : Fin s → Fin M) (he : Function.Injective e)
    (hm : ∀ a m t p, Measurable (fun y => h y a m t p))
    (hh : ∀ a m t p, MemLp (fun y => h y a m t p) 2 μ)
    (hbm : ∀ a, Measurable (fun y => b y a)) (hb : ∀ a, MemLp (fun y => b y a) 2 μ)
    (D0 V0 CA CK γ δ ε : ℝ) (hCA0 : 0 ≤ CA) (hCK0 : 0 ≤ CK)
    (hD : (∫ y, frobenius (fullPairDesign h w y - A) ^ 2 ∂μ) ≤ D0)
    (hV : (∫ y, ‖fullRegressionResidual (selectPairFeatures h e) w b θS y‖ ^ 2 ∂μ) ≤ V0)
    (hCA : ∀ a m t p, (∫ y, h y a m t p ^ 2 ∂μ) ≤ CA)
    (hCK : ∀ a t p, (∫ y, (∑ j, θS j * h y a (e j) t p) ^ 2 ∂μ) ≤ CK)
    (hγ : 0 < γ) (hδ : 0 < δ) (hε : 0 < ε) (hprob : δ + ε < 1)
    (hA : LowerBound (matrixMap (A.submatrix id e)) γ)
    (hsmall : designSamplingBudget M P w D0 CA ≤ δ * γ ^ 2 / 4) :
    ∃ G : Set (Ω × ((Fin T × Fin P) → OrderedPair N)), MeasurableSet G ∧
      1 - δ - ε ≤ (μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))).real G ∧
      ∀ z ∈ G, ‖moorePenrose (matrixMap ((sampledPairDesign h w z).submatrix id e))
        (WithLp.toLp 2 (b z.1)) - WithLp.toLp 2 θS‖ ^ 2 ≤
        4 * residualSamplingBudget P w V0 CK / (ε * γ ^ 2) := by
  have hDsel := (full_design_selected_second_moment_le μ h w A e he hm hh).trans hD
  have hcard : (s : ℝ) ≤ M := by
    have hn : s ≤ M := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e he
    exact_mod_cast hn
  have hbud : designSamplingBudget s P w D0 CA ≤ designSamplingBudget M P w D0 CA := by
    unfold designSamplingBudget
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hCA0) (by positivity)
  exact sampled_moorePenrose_recovery hP hL μ (selectPairFeatures h e) w b θS (A.submatrix id e)
    (fun a j => hm a (e j)) (fun a j => hh a (e j)) hbm hb
    D0 V0 CA CK γ δ ε hCA0 hCK0 hDsel hV (fun a j => hCA a (e j)) hCK
    hγ hδ hε hprob hA (hbud.trans hsmall)

end WMFKI
