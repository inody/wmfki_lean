import WMFKI_Stochastic.MeanFieldPullback

open MeasureTheory Set Filter Topology
open WMFKIMeanFieldPicard WMFKIMeanFieldAdapted
open scoped NNReal

namespace WMFKIMeanFieldCopies
variable {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {P : Measure Ω} {Q : Measure Ω'}
  [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : Ω' → Ω}
  {W : Ω → ℝ} {K : E → E} {L : ℝ≥0} {T a : ℝ} {X Z : ℝ → Ω → E}

omit [IsProbabilityMeasure Q] in
/-- Picard一段は測度保存写像との合成に可換。各ドリフトは実際に可積分。 -/
theorem picard_step_pullback (hφ : MeasurePreserving φ Q P) (hW : InputWeight P W)
    (hK : LipschitzWith L K) (hX : WeightedPaths W a X) (Z : ℝ → Ω → E) (t : ℝ) (ω : Ω') :
    picardStep Q K T (fun t z => Z t (φ z)) (fun t z => X t (φ z)) t ω =
      picardStep P K T Z X t (φ ω) := by
  unfold picardStep
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  exact (law_drift_pullback hφ hK ((weighted_paths_memLp hW hX s).integrable (by norm_num)) _).2

omit [IsProbabilityMeasure Q] in
/-- 全反復を明示的に移送する。移送先で別の未知解を選んでいない。 -/
theorem picard_iter_pullback (hφ : MeasurePreserving φ Q P) (hW : InputWeight P W)
    (hK : LipschitzWith L K) (hT : 0 ≤ T) (hZ : WeightedPaths W 1 Z) (n : ℕ) (t : ℝ) (ω : Ω') :
    picardIter Q K T (fun t z => Z t (φ z)) n t ω = picardIter P K T Z n t (φ ω) := by
  induction n generalizing t ω with
  | zero => rfl
  | succ n ih =>
    have he : picardIter Q K T (fun t z => Z t (φ z)) n =
        (fun t z => picardIter P K T Z n t (φ z)) := by funext s z; exact ih s z
    simp only [picardIter,he]
    exact picard_step_pullback hφ hW hK (picard_iter_weighted hW hK hT hZ n) Z t ω

variable [CompleteSpace E]

/-- 構成した極限そのものを移す。選択公理による異なる解の同一視だけには依存しない。 -/
theorem picard_limit_pullback (hφ : MeasurePreserving φ Q P) (hW : InputWeight P W)
    (hK : LipschitzWith L K) (hT : 0 ≤ T) (hZ : WeightedPaths W 1 Z) (t : ℝ) (ω : Ω') :
    picardLimit Q K T (fun t z => Z t (φ z)) t ω = picardLimit P K T Z t (φ ω) := by
  have hQ := picard_limit_tendsto (input_weight_pullback hφ hW) hK hT (weighted_paths_pullback hφ hZ) t ω
  have hP := picard_limit_tendsto hW hK hT hZ t (φ ω)
  have he : (fun n => picardIter Q K T (fun t z => Z t (φ z)) n t ω) =
      (fun n => picardIter P K T Z n t (φ ω)) := funext (fun n => picard_iter_pullback hφ hW hK hT hZ n t ω)
  rw [he] at hQ
  exact tendsto_nhds_unique hQ hP

end WMFKIMeanFieldCopies
