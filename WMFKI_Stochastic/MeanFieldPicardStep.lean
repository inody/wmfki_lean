import WMFKI_Stochastic.MeanFieldWeight
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

open MeasureTheory Set
open scoped NNReal

namespace WMFKIMeanFieldPicard
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- 未知の解ではなく、Picard作用素への入力過程の解析的クラス。 -/
structure WeightedPaths (W : Ω → ℝ) (a : ℝ) (Y : ℝ → Ω → E) : Prop where
  measurable : ∀ t, Measurable (Y t)
  continuous : ∀ ω, Continuous (fun t => Y t ω)
  bound : ∀ t ω, ‖Y t ω‖ ≤ a*W ω

variable [NormedSpace ℝ E] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : Ω → ℝ} {K : E → E} {L : ℝ≥0} {Y Z : ℝ → Ω → E} {a : ℝ}

omit [NormedSpace ℝ E] [IsProbabilityMeasure P] in
theorem weighted_paths_memLp (hW : InputWeight P W) (hY : WeightedPaths W a Y) (t : ℝ) :
    MemLp (Y t) 4 P := weighted_section_memLp hW (hY.measurable t) a (hY.bound t)

theorem measurable_along_drift (hW : InputWeight P W) (hK : LipschitzWith L K)
    (hY : WeightedPaths W a Y) (t : ℝ) : Measurable (fun ω => lawDrift P K (Y t) (Y t ω)) :=
  (law_drift_lipschitz hK ((weighted_paths_memLp hW hY t).integrable (by norm_num))).continuous.measurable.comp
    (hY.measurable t)

/-- 定数でなく確率変数包絡による優収束。核は非有界でよい。 -/
theorem continuous_along_drift (hW : InputWeight P W) (hK : LipschitzWith L K)
    (hY : WeightedPaths W a Y) (ω : Ω) : Continuous (fun t => lawDrift P K (Y t) (Y t ω)) := by
  unfold lawDrift
  apply continuous_of_dominated (bound := fun ω' => ‖K 0‖+(L : ℝ)*a*W ω+(L : ℝ)*a*W ω')
  · intro t
    exact (hK.continuous.measurable.comp (measurable_const.sub (hY.measurable t))).aestronglyMeasurable
  · intro t
    apply ae_of_all
    intro ω'
    have h := lipschitz_kernel_growth hK (Y t ω) (Y t ω')
    have h1 := mul_le_mul_of_nonneg_left (hY.bound t ω) L.coe_nonneg
    have h2 := mul_le_mul_of_nonneg_left (hY.bound t ω') L.coe_nonneg
    nlinarith
  · exact (integrable_const _).add ((hW.memLp.integrable (by norm_num)).const_mul ((L : ℝ)*a))
  · exact ae_of_all _ (fun ω' => hK.continuous.comp ((hY.continuous ω).sub (hY.continuous ω')))

theorem jointly_measurable_drift (hW : InputWeight P W) (hK : LipschitzWith L K)
    (hY : WeightedPaths W a Y) :
    StronglyMeasurable (fun z : ℝ × Ω => lawDrift P K (Y z.1) (Y z.1 z.2)) :=
  stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (fun ω => continuous_along_drift hW hK hY ω)
    (fun t => (measurable_along_drift hW hK hY t).stronglyMeasurable)

noncomputable def timeClip (T t : ℝ) : ℝ := min T (max 0 t)

theorem time_clip_bounds {T : ℝ} (hT : 0 ≤ T) (t : ℝ) :
    0 ≤ timeClip T t ∧ timeClip T t ≤ T :=
  ⟨le_min hT (le_max_left _ _), min_le_left _ _⟩

theorem time_clip_eq {T t : ℝ} (ht : t ∈ Icc 0 T) : timeClip T t = t := by
  simp only [timeClip, max_eq_right ht.1, min_eq_right ht.2]

/-- Zは初期値と加法駆動を合わせた既知入力。 -/
noncomputable def picardStep (P : Measure Ω) (K : E → E) (T : ℝ)
    (Z Y : ℝ → Ω → E) (t : ℝ) (ω : Ω) : E :=
  Z t ω + ∫ s in (0 : ℝ)..timeClip T t, lawDrift P K (Y s) (Y s ω)

/-- 有界核を仮定せず、実際のPicard一段を構成し、包絡を導く。 -/
theorem picard_step_weighted (hW : InputWeight P W) (hK : LipschitzWith L K)
    {T : ℝ} (hT : 0 ≤ T) (hZ : WeightedPaths W 1 Z) (hY : WeightedPaths W a Y) (ha : 0 ≤ a) :
    WeightedPaths W (1+T*(‖K 0‖+3*(L : ℝ)*a)) (picardStep P K T Z Y) := by
  constructor
  · intro t
    have hm : Measurable (fun ω => ∫ s in (0 : ℝ)..timeClip T t, lawDrift P K (Y s) (Y s ω)) := by
      simp_rw [intervalIntegral.integral_of_le (time_clip_bounds hT t).1]
      exact ((jointly_measurable_drift hW hK hY).integral_prod_left
        (μ := volume.restrict (Ioc 0 (timeClip T t)))).measurable
    exact (hZ.measurable t).add hm
  · intro ω
    have hp : Continuous (fun u => ∫ s in (0 : ℝ)..u, lawDrift P K (Y s) (Y s ω)) :=
      intervalIntegral.continuous_primitive (fun _ _ =>
        (continuous_along_drift hW hK hY ω).intervalIntegrable _ _) 0
    exact (hZ.continuous ω).add (hp.comp (continuous_const.min (continuous_const.max continuous_id)))
  · intro t ω
    have hwi : 0 ≤ W ω := (by norm_num : (0 : ℝ) ≤ 1).trans (hW.one_le ω)
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := timeClip T t) (fun s _ =>
        weighted_drift_growth hW hK (hY.measurable s) ha (hY.bound s) ω)
    rw [sub_zero,abs_of_nonneg (time_clip_bounds hT t).1] at hb
    have ht := mul_le_mul_of_nonneg_left (time_clip_bounds hT t).2
      (show 0 ≤ (‖K 0‖+3*(L : ℝ)*a)*W ω by positivity)
    have hn := norm_add_le (Z t ω) (∫ s in (0 : ℝ)..timeClip T t, lawDrift P K (Y s) (Y s ω))
    have hz := hZ.bound t ω
    change ‖Z t ω + _‖ ≤ _
    nlinarith

/-- Picard一段の重み付き差分評価。駆動は同じZなので正確に相殺される。 -/
theorem picard_step_difference (hW : InputWeight P W) (hK : LipschitzWith L K)
    {T : ℝ} (hT : 0 ≤ T) {Y' : ℝ → Ω → E} {a' : ℝ}
    (hY : WeightedPaths W a Y) (hY' : WeightedPaths W a' Y') (Z : ℝ → Ω → E)
    (t : ℝ) (g : ℝ → ℝ) (hg : IntervalIntegrable g volume 0 (timeClip T t))
    (hgn : ∀ s ∈ Icc 0 (timeClip T t), 0 ≤ g s)
    (hb : ∀ s ∈ Icc 0 (timeClip T t), ∀ ω, ‖Y s ω-Y' s ω‖ ≤ g s*W ω) (ω : Ω) :
    ‖picardStep P K T Z Y t ω-picardStep P K T Z Y' t ω‖ ≤
      (3*(L : ℝ)*W ω)*(∫ s in (0 : ℝ)..timeClip T t, g s) := by
  have he : picardStep P K T Z Y t ω-picardStep P K T Z Y' t ω =
      ∫ s in (0 : ℝ)..timeClip T t, (lawDrift P K (Y s) (Y s ω)-lawDrift P K (Y' s) (Y' s ω)) := by
    rw [intervalIntegral.integral_sub
      ((continuous_along_drift hW hK hY ω).intervalIntegrable _ _)
      ((continuous_along_drift hW hK hY' ω).intervalIntegrable _ _)]
    unfold picardStep
    abel
  rw [he, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.norm_integral_le_of_norm_le (time_clip_bounds hT t).1 _ (hg.const_mul _)
  apply ae_of_all
  intro s hs
  have hs' : s ∈ Icc 0 (timeClip T t) := ⟨hs.1.le,hs.2⟩
  have h := weighted_drift_difference hW hK
    ((weighted_paths_memLp hW hY s).integrable (by norm_num))
    ((weighted_paths_memLp hW hY' s).integrable (by norm_num)) (hgn s hs') (hb s hs') ω
  convert h using 1
  ring

end WMFKIMeanFieldPicard
