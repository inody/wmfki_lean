import WMFKI_Stochastic.MeanFieldCompletedMeasurable

open MeasureTheory Set Filter Topology
open WMFKIMeanFieldPicard
open scoped NNReal

namespace WMFKIMeanFieldAdapted
variable {Ω E : Type*} [m : MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {W : Ω → ℝ} {K : E → E} {L : ℝ≥0} {T a : ℝ}
  {Y Z : ℝ → Ω → E} {F : ℝ → MeasurableSpace Ω}

/-- 時刻t以前のドリフトの時間積分はF_tで可測。確率積分ではなくBochner時間積分。 -/
theorem measurable_past_drift_integral (hW : InputWeight P W) (hK : LipschitzWith L K)
    (hY : WeightedPaths W a Y) (hA : AdaptedOn F T Y) (hF : Monotone F)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    Measurable[F t] (fun ω => ∫ s in (0 : ℝ)..t, lawDrift P K (Y s) (Y s ω)) := by
  let D := fun s ω => lawDrift P K (Y s) (Y s ω)
  have hd (s : ℝ) : Measurable[F t] (D (timeClip t s)) := by
    have hs := time_clip_bounds ht.1 s
    have hsT : timeClip t s ∈ Icc 0 T := ⟨hs.1,hs.2.trans ht.2⟩
    have hm := (hA (timeClip t s) hsT).mono (hF hs.2) le_rfl
    exact (law_drift_lipschitz hK
      ((weighted_paths_memLp hW hY (timeClip t s)).integrable (by norm_num))).continuous.measurable.comp hm
  have hc (ω : Ω) : Continuous (fun s => D (timeClip t s) ω) :=
    (continuous_along_drift hW hK hY ω).comp (continuous_const.min (continuous_const.max continuous_id))
  have he : (fun ω => ∫ s in (0 : ℝ)..t, D (timeClip t s) ω) =
      (fun ω => ∫ s in (0 : ℝ)..t, D s ω) := by
    funext ω
    apply intervalIntegral.integral_congr
    intro s hs
    change D (timeClip t s) ω = D s ω
    rw [time_clip_eq (by simpa only [uIcc_of_le ht.1] using hs)]
  rw [← he]
  let : MeasurableSpace Ω := F t
  have hj : StronglyMeasurable (fun z : ℝ × Ω => D (timeClip t z.1) z.2) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hc
      (fun s => (hd s).stronglyMeasurable)
  simp_rw [intervalIntegral.integral_of_le ht.1]
  exact (hj.integral_prod_left (μ := volume.restrict (Ioc 0 t))).measurable

/-- Picard一段が適合性を保つ。 -/
theorem picard_step_adapted (hW : InputWeight P W) (hK : LipschitzWith L K)
    (hY : WeightedPaths W a Y) (hYA : AdaptedOn F T Y) (hZA : AdaptedOn F T Z)
    (hF : Monotone F) : AdaptedOn F T (picardStep P K T Z Y) := by
  intro t ht
  have he : picardStep P K T Z Y t = fun ω => Z t ω +
      ∫ s in (0 : ℝ)..t, lawDrift P K (Y s) (Y s ω) := by
    funext ω
    rw [picardStep,time_clip_eq ht]
  rw [he]
  exact (hZA t ht).add (measurable_past_drift_integral hW hK hY hYA hF t ht)

/-- 全有限反復の適合性。 -/
theorem picard_iter_adapted (hW : InputWeight P W) (hK : LipschitzWith L K) (hT : 0 ≤ T)
    (hZ : WeightedPaths W 1 Z) (hZA : AdaptedOn F T Z) (hF : Monotone F) (n : ℕ) :
    AdaptedOn F T (picardIter P K T Z n) := by
  induction n with
  | zero => exact hZA
  | succ n ih => exact picard_step_adapted hW hK (picard_iter_weighted hW hK hT hZ n) ih hZA hF

variable [CompleteSpace E]

/-- 点ごとの極限が各時刻のsigma代数で可測。未来の情報を追加しない。 -/
theorem picard_limit_adapted (hW : InputWeight P W) (hK : LipschitzWith L K) (hT : 0 ≤ T)
    (hZ : WeightedPaths W 1 Z) (hZA : AdaptedOn F T Z) (hF : Monotone F) :
    AdaptedOn F T (picardLimit P K T Z) := by
  intro t ht
  have ha (n : ℕ) : Measurable[F t] (picardIter P K T Z n t) :=
    picard_iter_adapted hW hK hT hZ hZA hF n t ht
  have hc (ω : Ω) := picard_limit_tendsto hW hK hT hZ t ω
  let : MeasurableSpace Ω := F t
  exact measurable_of_tendsto_metrizable ha (tendsto_pi_nhds.mpr hc)

/-- 原始a.s.連続入力に対する適合した有限時間平均場解。 -/
theorem exists_adapted_mean_field (T : ℝ) (hT : 0 ≤ T)
    (F : ℝ → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t s, MeasurableSet[m] s → P s = 0 → MeasurableSet[F t] s)
    (Z : ℝ → Ω → E) (hZm : ∀ t, Measurable (Z t)) (hZA : AdaptedOn F T Z)
    (hZc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Icc 0 T))
    (R : Ω → ℝ) (hRm : Measurable R) (hR : MemLp R 4 P)
    (hb : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, ‖Z t ω‖ ≤ R ω)
    (K : E → E) {L : ℝ≥0} (hK : LipschitzWith L K) :
    ∃ Y : ℝ → Ω → E, AdaptedOn F T Y ∧ (∀ t, Measurable (Y t)) ∧
      (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∃ H : Ω → ℝ, Measurable H ∧ MemLp H 4 P ∧ ∀ t ω, ‖Y t ω‖ ≤ H ω) ∧
      (∀ t, MemLp (Y t) 4 P) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t, (∫ ω, ‖Y t ω‖^4 ∂P) ≤ C) ∧
      (∀ ω, Continuous (fun t => ∫ y, K (Y t ω-y) ∂(P.map (Y t)))) ∧
      (∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, Y t ω = Z t ω +
        ∫ s in (0 : ℝ)..t, ∫ y, K (Y s ω-y) ∂(P.map (Y s))) := by
  obtain ⟨W,Z',hW,hZ',he⟩ := exists_weighted_input_modification T hT Z hZm hZc R hRm hR hb
  have hZ'A : AdaptedOn F T Z' := by
    intro t ht
    exact measurable_of_ae_eq_complete_subsigma P (F t) (hle t) (hnull t)
      (hZ'.measurable t) (hZA t ht) (he.mono (fun ω hω => hω t ht))
  let Y := picardLimit P K T Z'
  let c := 1+∑' n, factorialBound (‖K 0‖+3*(L : ℝ)) (3*(L : ℝ)) T n
  have hw := picard_limit_weighted hW hK hT hZ'
  have hfour := weighted_paths_fourth hW hw
  refine ⟨Y,picard_limit_adapted hW hK hT hZ' hZ'A hF,hw.measurable,hw.continuous,
    ⟨fun ω => c*W ω,measurable_const.mul hW.measurable,hW.memLp.const_mul c,hw.bound⟩,
    fun t => (hfour t).1,?_,?_,?_⟩
  · refine ⟨c^4*(∫ ω, W ω^4 ∂P),?_,fun t => (hfour t).2⟩
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

end WMFKIMeanFieldAdapted
