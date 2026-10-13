import Lean_Code.ObservedFeatures
import Lean_Code.ResidualOrthogonality

namespace WMFKI
open MeasureTheory

noncomputable def fullRegressionResidual {Ω : Type*} {L M T N : ℕ}
    (h : Ω → Fin L → Fin M → Fin T → OrderedPair N → ℝ)
    (w : Fin T → ℝ) (b : Ω → Fin L → ℝ) (θ : Fin M → ℝ) (ω : Ω) :
    EuclideanSpace ℝ (Fin L) :=
  WithLp.toLp 2 (fun a => b ω a - ∑ m, fullPairDesign h w ω a m * θ m)

noncomputable def sampledRegressionResidual {Ω : Type*} {L M T P N : ℕ}
    (h : Ω → Fin L → Fin M → Fin T → OrderedPair N → ℝ)
    (w : Fin T → ℝ) (b : Ω → Fin L → ℝ) (θ : Fin M → ℝ)
    (z : Ω × ((Fin T × Fin P) → OrderedPair N)) : EuclideanSpace ℝ (Fin L) :=
  WithLp.toLp 2 (fun a => b z.1 a - ∑ m, sampledPairDesign h w z a m * θ m)

/-- デザイン差が実際の回帰残差へ入る符号も含めた恒等式。 -/
theorem sampledResidual_decomposition {Ω : Type*} {L M T P N : ℕ}
    (h : Ω → Fin L → Fin M → Fin T → OrderedPair N → ℝ)
    (w : Fin T → ℝ) (b : Ω → Fin L → ℝ) (θ : Fin M → ℝ)
    (z : Ω × ((Fin T × Fin P) → OrderedPair N)) :
    sampledRegressionResidual h w b θ z = fullRegressionResidual h w b θ z.1 -
      matrixMap (sampledPairDesign h w z - fullPairDesign h w z.1) (WithLp.toLp 2 θ) := by
  ext a
  simp [fullRegressionResidual, sampledRegressionResidual, matrixMap_apply]

theorem fullPairDesign_entry_measurable {Ω : Type*} [MeasurableSpace Ω] {L M T N : ℕ}
    (h : Ω → Fin L → Fin M → Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ)
    (hm : ∀ a m t p, Measurable (fun ω => h ω a m t p)) (a : Fin L) (m : Fin M) :
    Measurable (fun ω => fullPairDesign h w ω a m) := by
  unfold fullPairDesign
  fun_prop

theorem fullPairDesign_entry_memLp {Ω : Type*} [MeasurableSpace Ω] {L M T N : ℕ}
    (μ : Measure Ω) (h : Ω → Fin L → Fin M → Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ)
    (hh : ∀ a m t p, MemLp (fun ω => h ω a m t p) 2 μ) (a : Fin L) (m : Fin M) :
    MemLp (fun ω => fullPairDesign h w ω a m) 2 μ := by
  unfold fullPairDesign
  simp_rw [div_eq_inv_mul]
  apply MemLp.const_mul
  apply memLp_finsetSum
  intro t _
  apply MemLp.const_mul
  apply MemLp.const_mul
  exact memLp_finsetSum _ (fun p _ => hh a m t p)

/-- 全ペア残差は観測の関数であり、そのL2性を応答と特徴から構成する。 -/
theorem fullResidual_entry_regular {Ω : Type*} [MeasurableSpace Ω] {L M T N : ℕ}
    (μ : Measure Ω) (h : Ω → Fin L → Fin M → Fin T → OrderedPair N → ℝ)
    (w : Fin T → ℝ) (b : Ω → Fin L → ℝ) (θ : Fin M → ℝ)
    (hm : ∀ a m t p, Measurable (fun ω => h ω a m t p))
    (hh : ∀ a m t p, MemLp (fun ω => h ω a m t p) 2 μ)
    (hbm : ∀ a, Measurable (fun ω => b ω a)) (hb : ∀ a, MemLp (fun ω => b ω a) 2 μ)
    (a : Fin L) :
    Measurable (fun ω => fullRegressionResidual h w b θ ω a) ∧
    MemLp (fun ω => fullRegressionResidual h w b θ ω a) 2 μ := by
  have hmA := fullPairDesign_entry_measurable h w hm
  constructor
  · change Measurable (fun ω => b ω a - ∑ m, fullPairDesign h w ω a m * θ m)
    fun_prop
  · change MemLp (fun ω => b ω a - ∑ m, fullPairDesign h w ω a m * θ m) 2 μ
    exact (hb a).sub (memLp_finsetSum _ (fun m _ =>
      (fullPairDesign_entry_memLp μ h w hh a m).mul_const (θ m)))

/-- 全ペア残差とペア誤差を独立とはせず、条件付き直交性で二乗平均を分解する。 -/
theorem sampledResidual_second_moment_identity {Ω : Type*} [MeasurableSpace Ω]
    {L M T P N : ℕ} [Fact (2 ≤ N)] (hP : 0 < P)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Fin L → Fin M → Fin T → OrderedPair N → ℝ)
    (w : Fin T → ℝ) (b : Ω → Fin L → ℝ) (θ : Fin M → ℝ)
    (hm : ∀ a m t p, Measurable (fun ω => h ω a m t p))
    (hh : ∀ a m t p, MemLp (fun ω => h ω a m t p) 2 μ)
    (hbm : ∀ a, Measurable (fun ω => b ω a)) (hb : ∀ a, MemLp (fun ω => b ω a) 2 μ) :
    (∫ z, ‖sampledRegressionResidual (P := P) h w b θ z‖ ^ 2
      ∂μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))) =
      (∫ ω, ‖fullRegressionResidual h w b θ ω‖ ^ 2 ∂μ) +
      ∫ z, ‖matrixMap (sampledPairDesign h w z - fullPairDesign h w z.1) (WithLp.toLp 2 θ)‖ ^ 2
        ∂μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N)) := by
  let k := fun ω a t p => ∑ m, θ m * h ω a m t p
  let f := fun (z : Ω × ((Fin T × Fin P) → OrderedPair N)) a =>
    pairRowError L (k z.1 a) w z.2
  have hkm (a : Fin L) (t : Fin T) (p : OrderedPair N) :
      Measurable (fun ω => k ω a t p) := by dsimp [k]; fun_prop
  have hkh (a : Fin L) (t : Fin T) (p : OrderedPair N) :
      MemLp (fun ω => k ω a t p) 2 μ :=
    memLp_finsetSum _ (fun m _ => (hh a m t p).const_mul (θ m))
  have hf (a : Fin L) : MemLp (fun z => f z a) 2
      (μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))) :=
    pairRowError_joint_memLp μ L (fun ω => k ω a) w (hkm a) (hkh a)
  have hc (a : Fin L) := pairRowError_conditional_mean_of_moments (P := P)
    μ L (fun ω => k ω a) w (hkm a) (hkh a)
  have hfull := fullResidual_entry_regular μ h w b θ hm hh hbm hb
  have heq (z : Ω × ((Fin T × Fin P) → OrderedPair N)) :
      matrixMap (sampledPairDesign h w z - fullPairDesign h w z.1) (WithLp.toLp 2 θ) =
      WithLp.toLp 2 (f z) := by
    rw [← pairDesignError_eq_difference Fact.out hP]
    ext a
    change (∑ m, pairDesignError h w z a m * θ m) = _
    exact pairDesignError_mul_coefficients h w θ z a
  have hpy := finite_observation_pythagoras μ (independentDraws (Fin T × Fin P) (OrderedPair N))
    (fun ω a => fullRegressionResidual h w b θ ω a) f
    (fun a => (hfull a).1) (fun a => (hfull a).2) hf hc
  have hres (z : Ω × ((Fin T × Fin P) → OrderedPair N)) :
      sampledRegressionResidual h w b θ z =
      WithLp.toLp 2 (fun a => fullRegressionResidual h w b θ z.1 a - f z a) := by
    rw [sampledResidual_decomposition, heq]
    rfl
  simpa only [hres, heq, WithLp.toLp_ofLp] using hpy

/-- 全ペア残差の評価に、真の係数方向のQ/P項だけを追加する。 -/
theorem sampledResidual_second_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    {L M T P N : ℕ} [Fact (2 ≤ N)] (hP : 0 < P) (hL : 0 < L)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Fin L → Fin M → Fin T → OrderedPair N → ℝ)
    (w : Fin T → ℝ) (b : Ω → Fin L → ℝ) (θ : Fin M → ℝ)
    (hm : ∀ a m t p, Measurable (fun ω => h ω a m t p))
    (hh : ∀ a m t p, MemLp (fun ω => h ω a m t p) 2 μ)
    (hbm : ∀ a, Measurable (fun ω => b ω a)) (hb : ∀ a, MemLp (fun ω => b ω a) 2 μ)
    (V C : ℝ) (hC0 : 0 ≤ C)
    (hV : (∫ ω, ‖fullRegressionResidual h w b θ ω‖ ^ 2 ∂μ) ≤ V)
    (hC : ∀ a t p, (∫ ω, (∑ m, θ m * h ω a m t p) ^ 2 ∂μ) ≤ C) :
    (∫ z, ‖sampledRegressionResidual (P := P) h w b θ z‖ ^ 2
      ∂μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))) ≤
      V + C * (∑ t, w t ^ 2) / P := by
  rw [sampledResidual_second_moment_identity hP μ h w b θ hm hh hbm hb]
  apply add_le_add hV
  apply assembled_design_direction_second_moment hP hL μ h w θ C hC0
  · intro a t p
    fun_prop
  · intro a t p
    exact memLp_finsetSum _ (fun m _ => (hh a m t p).const_mul (θ m))
  · exact hC

/-- 観測位置・辞書・真の相互作用から、標本回帰残差の評価へ直接接続する。 -/
theorem observed_residual_second_moment_bound {Ω F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] [SecondCountableTopology F]
    {N T P L M : ℕ} [Fact (2 ≤ N)] (hP : 0 < P) (hL : 0 < L)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → Fin N → Fin T → F) (ψ : Fin L → Fin T → ℝ)
    (g : Fin L → F → F) (Φ : Fin M → F → F) (w : Fin T → ℝ)
    (b : Ω → Fin L → ℝ) (θ : Fin M → ℝ) (κ : F → F)
    (hκ : ∀ z, ∑ m, θ m • Φ m z = κ z)
    (hY : ∀ i t, Measurable (fun ω => Y ω i t))
    (hiY : ∀ i t, Integrable (fun ω => ‖Y ω i t‖ ^ 2) μ)
    (R : ℝ) (hR0 : 0 ≤ R) (hR : ∀ i t, (∫ ω, ‖Y ω i t‖ ^ 2 ∂μ) ≤ R)
    (hg : ∀ a, Continuous (g a)) (hΦ : ∀ m, Continuous (Φ m)) (hκm : Continuous κ)
    (B G K KT : ℝ) (hB : 0 ≤ B) (hG : 0 ≤ G) (hK : 0 ≤ K) (hKT : 0 ≤ KT)
    (hψ : ∀ a t, |ψ a t| ≤ B) (hgb : ∀ a x, ‖g a x‖ ≤ G)
    (hΦb : ∀ m z, ‖Φ m z‖ ≤ K * (1 + ‖z‖))
    (hκb : ∀ z, ‖κ z‖ ≤ KT * (1 + ‖z‖))
    (hbm : ∀ a, Measurable (fun ω => b ω a)) (hb : ∀ a, MemLp (fun ω => b ω a) 2 μ)
    (V : ℝ) (hV : (∫ ω, ‖fullRegressionResidual (observedPairFeature Y ψ g Φ) w b θ ω‖ ^ 2 ∂μ) ≤ V) :
    (∫ z, ‖sampledRegressionResidual (P := P) (observedPairFeature Y ψ g Φ) w b θ z‖ ^ 2
      ∂μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))) ≤
      V + featureMomentBound B G KT R * (∑ t, w t ^ 2) / P := by
  have hh := observedPairFeature_moments μ Y ψ g Φ hY hiY R hR hg hΦ
    B G K hB hG hK hψ hgb hΦb
  apply sampledResidual_second_moment_bound hP hL μ _ w b θ
    (observedPairFeature_measurable Y ψ g Φ hY hg hΦ)
    (fun a m t p => (hh a m t p).1) hbm hb V (featureMomentBound B G KT R)
    (by unfold featureMomentBound; positivity) hV
  intro a t p
  simp_rw [observedPairFeature_realizable Y ψ g Φ θ κ hκ]
  exact (pairFeature_second_moment μ _ _ (hY _ _) (hY _ _) (hiY _ _) (hiY _ _)
    R (hR _ _) (hR _ _) (g a) κ (hg a) hκm (ψ a t) B G KT
    hB hG hKT (hψ a t) (hgb a) hκb).2

end WMFKI
