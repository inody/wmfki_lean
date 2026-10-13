import WMFKI_Stochastic.MeanFieldPicardLimit

open MeasureTheory Set
open scoped NNReal

namespace WMFKIMeanFieldPicard
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {P : Measure Ω} [IsProbabilityMeasure P]

omit [NormedSpace ℝ E] [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- a.s.連続の原始入力を一つの可測零集合上で変更する。
    変更後だけが全標本で連続。原始入力に全標本連続性を要求しない。 -/
theorem exists_weighted_input_modification (T : ℝ) (hT : 0 ≤ T)
    (Z : ℝ → Ω → E) (hZm : ∀ t, Measurable (Z t))
    (hZc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Icc 0 T))
    (R : Ω → ℝ) (hRm : Measurable R) (hR : MemLp R 4 P)
    (hb : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, ‖Z t ω‖ ≤ R ω) :
    ∃ W : Ω → ℝ, ∃ Z' : ℝ → Ω → E,
      InputWeight P W ∧ WeightedPaths W 1 Z' ∧
      (∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, Z' t ω = Z t ω) := by
  classical
  let good : Ω → Prop := fun ω => ContinuousOn (fun t => Z t ω) (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, ‖Z t ω‖ ≤ R ω
  have hg : ∀ᵐ ω ∂P, good ω := hZc.and hb
  obtain ⟨s,hsub,hsm,hs0⟩ := exists_measurable_superset_of_null (ae_iff.mp hg)
  have hs : ∀ᵐ ω ∂P, ω ∉ s := by
    simp only [ae_iff,not_not]
    change P s = 0
    exact hs0
  have hgood (ω : Ω) (hω : ω ∉ s) : good ω := by
    by_contra h
    exact hω (hsub h)
  let W := normalizedWeight P R
  let Z' := fun t ω => if ω ∈ s then (0 : E) else Z (timeClip T t) ω
  obtain ⟨hW,hRW⟩ := normalized_weight R hRm hR
  refine ⟨W,Z',hW,?_,?_⟩
  · constructor
    · intro t
      exact Measurable.ite hsm measurable_const (hZm (timeClip T t))
    · intro ω
      by_cases hω : ω ∈ s
      · simpa only [Z',ite_eq_left hω] using (continuous_const : Continuous (fun _ : ℝ => (0 : E)))
      · simpa only [Z',ite_eq_right hω,Function.comp_def,timeClip,id_eq] using (hgood ω hω).1.comp_continuous
          (continuous_const.min (continuous_const.max continuous_id)) (fun t => time_clip_bounds hT t)
    · intro t ω
      dsimp only [Z']
      split_ifs with hω
      · simp only [norm_zero,one_mul]
        exact (by norm_num : (0 : ℝ) ≤ 1).trans (hW.one_le ω)
      · simpa only [one_mul] using ((hgood ω hω).2 (timeClip T t) (time_clip_bounds hT t)).trans (hRW ω)
  · filter_upwards [hs] with ω hω t ht
    simp only [Z',ite_eq_right hω,time_clip_eq ht]

omit [CompleteSpace E] [NormedSpace ℝ E] [IsProbabilityMeasure P] in
theorem weighted_paths_fourth {W : Ω → ℝ} (hW : InputWeight P W)
    {a : ℝ} {Y : ℝ → Ω → E} (hY : WeightedPaths W a Y) (t : ℝ) :
    MemLp (Y t) 4 P ∧ (∫ ω, ‖Y t ω‖^4 ∂P) ≤ a^4*(∫ ω, W ω^4 ∂P) := by
  have hL := weighted_paths_memLp hW hY t
  have hi : Integrable (fun ω => W ω^4) P := by
    simpa only [Real.norm_eq_abs, (show Even (4 : ℕ) from by decide).pow_abs] using
      hW.memLp.integrable_norm_pow (p := 4) (by decide)
  refine ⟨hL, ?_⟩
  rw [← integral_const_mul]
  apply integral_mono (hL.integrable_norm_pow (p := 4) (by decide)) (hi.const_mul _)
  intro ω
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hY.bound t ω) 4

/-- a.s.連続の原始入力から、有限区間の平均場積分方程式の解を構成する。
    この定理はフィルトレーションへの適合性や一意性をまだ主張しない。 -/
theorem exists_mean_field_finite_horizon (T : ℝ) (hT : 0 ≤ T)
    (Z : ℝ → Ω → E) (hZm : ∀ t, Measurable (Z t))
    (hZc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Icc 0 T))
    (R : Ω → ℝ) (hRm : Measurable R) (hR : MemLp R 4 P)
    (hb : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, ‖Z t ω‖ ≤ R ω)
    {L : ℝ≥0} (K : E → E) (hK : LipschitzWith L K) :
    ∃ Y : ℝ → Ω → E, (∀ t, Measurable (Y t)) ∧
      (∀ ω, Continuous (fun t => Y t ω)) ∧ (∀ t, MemLp (Y t) 4 P) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t, (∫ ω, ‖Y t ω‖^4 ∂P) ≤ C) ∧
      (∀ ω, Continuous (fun t => ∫ y, K (Y t ω-y) ∂(P.map (Y t)))) ∧
      (∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, Y t ω = Z t ω +
        ∫ u in (0 : ℝ)..t, ∫ y, K (Y u ω-y) ∂(P.map (Y u))) := by
  obtain ⟨W,Z',hW,hZ',he⟩ := exists_weighted_input_modification T hT Z hZm hZc R hRm hR hb
  let Y := picardLimit P K T Z'
  have hw := picard_limit_weighted hW hK hT hZ'
  have hf := weighted_paths_fourth hW hw
  refine ⟨Y,hw.measurable,hw.continuous,(fun t => (hf t).1),?_,?_,?_⟩
  · refine ⟨(1+∑' n, factorialBound (‖K 0‖+3*(L : ℝ)) (3*(L : ℝ)) T n)^4 *
      (∫ ω, W ω^4 ∂P), ?_, fun t => (hf t).2⟩
    exact mul_nonneg (by positivity) (integral_nonneg (fun _ => by positivity))
  · intro ω
    have hd : (fun t => ∫ y, K (Y t ω-y) ∂(P.map (Y t))) =
        (fun t => lawDrift P K (Y t) (Y t ω)) := by
      funext t
      exact (law_drift_map hK (hw.measurable t) _).symm
    rw [hd]
    exact continuous_along_drift hW hK hw ω
  · filter_upwards [he] with ω hω t ht
    have h := picard_limit_mean_field_equation hW hK hT hZ' t ht ω
    rw [hω t ht] at h
    exact h

/-- 初期値と加法駆動を持つ実際の式。B(0)=0もa.s.で十分。 -/
theorem exists_mean_field_additive (T : ℝ) (hT : 0 ≤ T) (ξ : Ω → E) (hξ : Measurable ξ)
    (B : ℝ → Ω → E) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ᵐ ω ∂P, ContinuousOn (fun t => B t ω) (Icc 0 T))
    (hB0 : ∀ᵐ ω ∂P, B 0 ω = 0)
    (R : Ω → ℝ) (hRm : Measurable R) (hR : MemLp R 4 P)
    (hb : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, ‖ξ ω+B t ω‖ ≤ R ω)
    {L : ℝ≥0} (K : E → E) (hK : LipschitzWith L K) :
    ∃ Y : ℝ → Ω → E, (∀ t, Measurable (Y t)) ∧
      (∀ ω, Continuous (fun t => Y t ω)) ∧ (∀ t, MemLp (Y t) 4 P) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t, (∫ ω, ‖Y t ω‖^4 ∂P) ≤ C) ∧
      (∀ ω, Continuous (fun t => ∫ y, K (Y t ω-y) ∂(P.map (Y t)))) ∧
      (∀ᵐ ω ∂P, Y 0 ω = ξ ω ∧ ∀ t ∈ Icc 0 T,
        Y t ω = ξ ω + (∫ u in (0 : ℝ)..t, ∫ y, K (Y u ω-y) ∂(P.map (Y u))) + B t ω) := by
  have hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => ξ ω+B t ω) (Icc 0 T) :=
    hBc.mono (fun ω hω => continuousOn_const.add hω)
  obtain ⟨Y,hm,hc,hL,hM,hd,he⟩ := exists_mean_field_finite_horizon T hT
    (fun t ω => ξ ω+B t ω) (fun t => hξ.add (hBm t)) hc R hRm hR hb K hK
  refine ⟨Y,hm,hc,hL,hM,hd,?_⟩
  filter_upwards [he,hB0] with ω hω h0
  refine ⟨?_,?_⟩
  · have h := hω 0 ⟨le_rfl,hT⟩
    simpa only [h0,add_zero,intervalIntegral.integral_same] using h
  · intro t ht
    rw [hω t ht]
    abel

end WMFKIMeanFieldPicard
