import WMFKI_Stochastic.MeanFieldSynchronousUniqueness

open MeasureTheory Set
open WMFKIMeanFieldPicard
open scoped NNReal

namespace WMFKIMeanFieldAdapted
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {P : Measure Ω} [IsProbabilityMeasure P] {K : E → E} {L : ℝ≥0} {T : ℝ}
  {X Y Z : ℝ → Ω → E}

/-- 有限区間の可測断面、a.s.連続経路、L4経路包絡という解クラス。
    方程式・適合性・一意性をこの構造体の入力に隠さない。 -/
structure FiniteL4Paths (P : Measure Ω) (T : ℝ) (X : ℝ → Ω → E) : Prop where
  measurable : ∀ t ∈ Icc 0 T, Measurable (X t)
  continuous : ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Icc 0 T)
  envelope : ∃ R : Ω → ℝ, Measurable R ∧ MemLp R 4 P ∧
    (∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, ‖X t ω‖ ≤ R ω)

omit [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure P] in
theorem finite_l4_paths_of_global_envelope (hm : ∀ t, Measurable (X t))
    (hc : ∀ ω, Continuous (fun t => X t ω))
    (he : ∃ R : Ω → ℝ, Measurable R ∧ MemLp R 4 P ∧ ∀ t ω, ‖X t ω‖ ≤ R ω) :
    FiniteL4Paths P T X := by
  obtain ⟨R,hRm,hRL,hRb⟩ := he
  exact ⟨fun t _ => hm t,ae_of_all _ (fun ω => (hc ω).continuousOn),
    ⟨R,hRm,hRL,ae_of_all _ (fun ω t _ => hRb t ω)⟩⟩

omit [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
/-- 有限区間だけのa.s.正則性から、以前の重み付き全経路クラスへ移す。 -/
theorem FiniteL4Paths.weighted_modification (hX : FiniteL4Paths P T X) (hT : 0 ≤ T) :
    ∃ W : Ω → ℝ, ∃ X' : ℝ → Ω → E, InputWeight P W ∧ WeightedPaths W 1 X' ∧
      (∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, X' t ω = X t ω) := by
  obtain ⟨R,hRm,hRL,hRb⟩ := hX.envelope
  let V := fun t => X (timeClip T t)
  have hm (t : ℝ) : Measurable (V t) := hX.measurable _ (time_clip_bounds hT t)
  have hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => V t ω) (Icc 0 T) := by
    filter_upwards [hX.continuous] with ω hω
    exact (hω.comp_continuous (continuous_const.min (continuous_const.max continuous_id))
      (fun t => time_clip_bounds hT t)).continuousOn
  have hb : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, ‖V t ω‖ ≤ R ω :=
    hRb.mono (fun ω hω t _ => hω _ (time_clip_bounds hT t))
  obtain ⟨W,X',hW,hX',he⟩ := exists_weighted_input_modification T hT V hm hc R hRm hRL hb
  refine ⟨W,X',hW,hX',?_⟩
  filter_upwards [he] with ω hω t ht
  simpa only [V,time_clip_eq ht] using hω t ht

omit [NormedSpace ℝ E] [IsProbabilityMeasure P] in
/-- 経路包絡から各時刻の実際のL4を導く。 -/
theorem FiniteL4Paths.memLp (hX : FiniteL4Paths P T X) (t : ℝ) (ht : t ∈ Icc 0 T) :
    MemLp (X t) 4 P := by
  obtain ⟨R,_,hR,hb⟩ := hX.envelope
  apply hR.mono (hX.measurable t ht).aestronglyMeasurable
  filter_upwards [hb] with ω hω
  exact (hω t ht).trans (le_abs_self (R ω))

omit [NormedSpace ℝ E] [IsProbabilityMeasure P] in
/-- 経路包絡は時間一様の第4モーメントを供給する。 -/
theorem FiniteL4Paths.uniform_fourth (hX : FiniteL4Paths P T X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, (∫ ω, ‖X t ω‖^4 ∂P) ≤ C := by
  obtain ⟨R,_,hR,hb⟩ := hX.envelope
  refine ⟨∫ ω, ‖R ω‖^4 ∂P,integral_nonneg (fun _ => by positivity),?_⟩
  intro t ht
  apply integral_mono_ae ((hX.memLp t ht).integrable_norm_pow (p := 4) (by decide))
    (hR.integrable_norm_pow (p := 4) (by decide))
  filter_upwards [hb] with ω hω
  exact pow_le_pow_left₀ (norm_nonneg _) ((hω t ht).trans (le_abs_self (R ω))) 4

omit [NormedSpace ℝ E] in
/-- 実際の時間周辺法則mu_t=P.map(X_t)に、確率性と一様第4モーメントを移す。 -/
theorem FiniteL4Paths.marginal_fourth (hX : FiniteL4Paths P T X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T,
      IsProbabilityMeasure (P.map (X t)) ∧ MemLp (id : E → E) 4 (P.map (X t)) ∧
      (∫ x, ‖x‖^4 ∂(P.map (X t))) ≤ C := by
  obtain ⟨C,hC,hb⟩ := hX.uniform_fourth
  refine ⟨C,hC,fun t ht => ?_⟩
  have hm : AEMeasurable (X t) P := (hX.measurable t ht).aemeasurable
  refine ⟨(Measure.isProbabilityMeasure_map_iff hm).mpr inferInstance,?_,?_⟩
  · exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable hm).mpr (hX.memLp t ht)
  · have hc : Continuous (fun x : E => ‖x‖^4) := continuous_norm.pow 4
    rw [integral_map hm hc.aestronglyMeasurable]
    exact hb t ht

/-- 比較する候補解の法則積分と時間積分も実際に可積分である。 -/
theorem FiniteL4Paths.drift_integrable (hX : FiniteL4Paths P T X) (hT : 0 ≤ T)
    (hK : LipschitzWith L K) :
    (∀ t ∈ Icc 0 T, ∀ x, Integrable (fun y => K (x-y)) (P.map (X t))) ∧
    (∀ᵐ ω ∂P, IntervalIntegrable (fun s => lawDrift P K (X s) (X s ω)) volume 0 T) := by
  refine ⟨fun t ht x => law_kernel_map_integrable hK (hX.measurable t ht)
    ((hX.memLp t ht).integrable (by norm_num)) x,?_⟩
  obtain ⟨W,X',hW,hX',he⟩ := hX.weighted_modification hT
  filter_upwards [he] with ω hω
  have heq : EqOn (fun s => lawDrift P K (X s) (X s ω))
      (fun s => lawDrift P K (X' s) (X' s ω)) (Icc 0 T) := by
    intro s hs
    unfold lawDrift
    apply integral_congr_ae
    filter_upwards [he] with ω' hω'
    rw [hω s hs,hω' s hs]
  have hc := (continuous_along_drift hW hK hX' ω).continuousOn.congr heq
  exact hc.intervalIntegrable_of_Icc hT

/-- a.s.連続とL4経路包絡を持つ有限区間の解の一意性。
    二つの解を同じ確率空間・同じ初期値および駆動Zで比較する。 -/
theorem finite_l4_mean_field_unique (hT : 0 ≤ T) (hK : LipschitzWith L K)
    (hX : FiniteL4Paths P T X) (hY : FiniteL4Paths P T Y)
    (heX : MeanFieldEquation P K T Z X) (heY : MeanFieldEquation P K T Z Y) :
    ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, X t ω = Y t ω := by
  obtain ⟨U,X',hU,hX',hXX⟩ := hX.weighted_modification hT
  obtain ⟨V,Y',hV,hY',hYY⟩ := hY.weighted_modification hT
  obtain ⟨hW,hUW⟩ := normalized_weight (fun ω => U ω+V ω)
    (hU.measurable.add hV.measurable) (hU.memLp.add hV.memLp)
  let W := normalizedWeight P (fun ω => U ω+V ω)
  have hx : WeightedPaths W 1 X' := by
    refine ⟨hX'.measurable,hX'.continuous,?_⟩
    intro t ω
    have hb := hX'.bound t ω
    have hv := hV.one_le ω
    have hw := hUW ω
    change ‖X' t ω‖ ≤ 1*W ω
    change U ω+V ω ≤ W ω at hw
    linarith
  have hy : WeightedPaths W 1 Y' := by
    refine ⟨hY'.measurable,hY'.continuous,?_⟩
    intro t ω
    have hb := hY'.bound t ω
    have hu := hU.one_le ω
    have hw := hUW ω
    change ‖Y' t ω‖ ≤ 1*W ω
    change U ω+V ω ≤ W ω at hw
    linarith
  have heq := weighted_mean_field_unique hW hK hx hy
    (mean_field_equation_congr hXX heX) (mean_field_equation_congr hYY heY)
  filter_upwards [heq,hXX,hYY] with ω he hxx hyy t ht
  rw [← hxx t ht,← hyy t ht]
  exact he t ht

omit [IsProbabilityMeasure P] in
/-- 母集団法則による実際の方程式から、一意性定理の自然結合表示へ移す。 -/
theorem mean_field_equation_of_law_integral (hK : LipschitzWith L K)
    (hm : ∀ t ∈ Icc 0 T, Measurable (X t))
    (he : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, X t ω = Z t ω +
      ∫ s in (0 : ℝ)..t, ∫ y, K (X s ω-y) ∂(P.map (X s))) :
    MeanFieldEquation P K T Z X := by
  filter_upwards [he] with ω hω t ht
  rw [hω t ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hsT : s ∈ Icc 0 T := by rw [uIcc_of_le ht.1] at hs; exact ⟨hs.1,hs.2.trans ht.2⟩
  exact (law_drift_map hK (hm s hsT) _).symm

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure P] in
/-- 区間を短くしても同じ過程・同じ法則・同じ駆動の方程式を保持する。 -/
theorem MeanFieldEquation.restrict (h : MeanFieldEquation P K T Z X) {S : ℝ} (hST : S ≤ T) :
    MeanFieldEquation P K S Z X :=
  h.mono (fun _ hω t ht => hω t ⟨ht.1,ht.2.trans hST⟩)

omit [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure P] in
theorem FiniteL4Paths.restrict (h : FiniteL4Paths P T X) {S : ℝ} (hST : S ≤ T) :
    FiniteL4Paths P S X := by
  have hsub : Icc (0 : ℝ) S ⊆ Icc 0 T := fun _ ht => ⟨ht.1,ht.2.trans hST⟩
  obtain ⟨R,hm,hL,hb⟩ := h.envelope
  exact ⟨fun t ht => h.measurable t (hsub ht),h.continuous.mono (fun _ hc => hc.mono hsub),
    ⟨R,hm,hL,hb.mono (fun _ he t ht => he t (hsub ht))⟩⟩

/-- 異なる終端時刻で構成した同じ駆動の解は、重なる区間で一致する。 -/
theorem finite_horizon_consistency {S : ℝ} (hS : 0 ≤ S) (hST : S ≤ T) (hK : LipschitzWith L K)
    (hX : FiniteL4Paths P S X) (hY : FiniteL4Paths P T Y)
    (heX : MeanFieldEquation P K S Z X) (heY : MeanFieldEquation P K T Z Y) :
    ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 S, X t ω = Y t ω :=
  finite_l4_mean_field_unique hS hK hX (hY.restrict hST) heX (heY.restrict hST)

end WMFKIMeanFieldAdapted
