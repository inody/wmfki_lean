import WMFKI_Stochastic.MeanFieldWellPosedness
import Mathlib.Probability.HasLaw

open MeasureTheory ProbabilityTheory Set
open WMFKIMeanFieldPicard WMFKIMeanFieldAdapted
open scoped NNReal

namespace WMFKIMeanFieldCopies
variable {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {P : Measure Ω} {Q : Measure Ω'}
  [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {φ : Ω' → Ω}

omit [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
/-- 座標評価など、非単射でもよい測度保存写像による法則の移送。 -/
theorem pullback_hasLaw (hφ : MeasurePreserving φ Q P) {X : Ω → E} (hm : Measurable X) :
    HasLaw (fun ω => X (φ ω)) (P.map X) Q :=
  (hasLaw_map hm.aemeasurable).comp hφ.hasLaw

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure Q] in
/-- ドリフトの自然結合表示を移す。核の可積分性も結論に保持する。 -/
theorem law_drift_pullback (hφ : MeasurePreserving φ Q P) {K : E → E} {L : ℝ≥0}
    (hK : LipschitzWith L K) {X : Ω → E} (hX : Integrable X P) (x : E) :
    Integrable (fun ω => K (x-X (φ ω))) Q ∧
      lawDrift Q K (fun ω => X (φ ω)) x = lawDrift P K X x := by
  have hk := law_kernel_integrable hK hX x
  exact ⟨hφ.hasLaw.integrable_fun_comp hk,hφ.hasLaw.integral_comp hk.aestronglyMeasurable⟩

omit [IsProbabilityMeasure P] [IsProbabilityMeasure Q] in
/-- 入力重みの平均条件も、同じ分布を使って保つ。 -/
theorem input_weight_pullback (hφ : MeasurePreserving φ Q P) {W : Ω → ℝ} (hW : InputWeight P W) :
    InputWeight Q (fun ω => W (φ ω)) := by
  refine ⟨hW.measurable.comp hφ.measurable,hW.memLp.comp_measurePreserving hφ,
    fun ω => hW.one_le (φ ω),?_⟩
  intro ω
  have he : (∫ z, W (φ z) ∂Q) = ∫ z, W z ∂P := hφ.hasLaw.integral_comp hW.measurable.aestronglyMeasurable
  rw [he]
  exact hW.mean_le (φ ω)

omit [NormedSpace ℝ E] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  [BorelSpace E] [SecondCountableTopology E] in
theorem weighted_paths_pullback (hφ : MeasurePreserving φ Q P) {W : Ω → ℝ} {a : ℝ}
    {X : ℝ → Ω → E} (hX : WeightedPaths W a X) :
    WeightedPaths (fun ω => W (φ ω)) a (fun t ω => X t (φ ω)) :=
  ⟨fun t => (hX.measurable t).comp hφ.measurable,fun ω => hX.continuous (φ ω),fun t ω => hX.bound t (φ ω)⟩

omit [NormedSpace ℝ E] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  [BorelSpace E] [SecondCountableTopology E] in
/-- a.s.連続性と全時刻共通のL4包絡を一つの共通事象ごと移す。 -/
theorem finite_l4_paths_pullback (hφ : MeasurePreserving φ Q P) {T : ℝ} {X : ℝ → Ω → E}
    (hX : FiniteL4Paths P T X) : FiniteL4Paths Q T (fun t ω => X t (φ ω)) := by
  obtain ⟨R,hm,hL,hb⟩ := hX.envelope
  exact ⟨fun t ht => (hX.measurable t ht).comp hφ.measurable,
    hφ.quasiMeasurePreserving.ae hX.continuous,
    ⟨fun ω => R (φ ω),hm.comp hφ.measurable,hL.comp_measurePreserving hφ,hφ.quasiMeasurePreserving.ae hb⟩⟩

omit [IsProbabilityMeasure Q] in
/-- 平均場方程式を、移送先自身の法則ドリフトによる方程式として移す。 -/
theorem mean_field_equation_pullback (hφ : MeasurePreserving φ Q P) {T : ℝ}
    {K : E → E} {L : ℝ≥0} (hK : LipschitzWith L K) {X Z : ℝ → Ω → E}
    (hX : FiniteL4Paths P T X) (he : MeanFieldEquation P K T Z X) :
    MeanFieldEquation Q K T (fun t ω => Z t (φ ω)) (fun t ω => X t (φ ω)) := by
  have he' := hφ.quasiMeasurePreserving.ae he
  filter_upwards [he'] with ω hω t ht
  rw [hω t ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hsT : s ∈ Icc 0 T := by rw [uIcc_of_le ht.1] at hs; exact ⟨hs.1,hs.2.trans ht.2⟩
  exact (law_drift_pullback hφ hK ((hX.memLp s hsT).integrable (by norm_num)) (X s (φ ω))).2.symm

end WMFKIMeanFieldCopies
