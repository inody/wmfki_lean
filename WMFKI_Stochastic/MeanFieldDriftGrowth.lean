import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped NNReal

namespace WMFKIMeanFieldPicard
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Measure Ω} [IsProbabilityMeasure P] {K : E → E} {L : ℝ≥0}

/-- 実際の法則ドリフト。未知の近似誤差は定義に含めない。 -/
noncomputable def lawDrift (P : Measure Ω) (K : E → E) (X : Ω → E) (x : E) : E :=
  ∫ ω, K (x-X ω) ∂P

omit [NormedSpace ℝ E] in
theorem lipschitz_kernel_growth (hK : LipschitzWith L K) (x y : E) :
    ‖K (x-y)‖ ≤ ‖K 0‖+(L : ℝ)*‖x‖+(L : ℝ)*‖y‖ := by
  have h := hK.norm_sub_le (x-y) 0
  have ht := norm_add_le (K (x-y)-K 0) (K 0)
  simp only [sub_zero,sub_add_cancel] at h ht
  have hb := mul_le_mul_of_nonneg_left (norm_sub_le x y) L.coe_nonneg
  nlinarith

omit [NormedSpace ℝ E] in
/-- 線形成長核の可積分性を先に証明する。 -/
theorem law_kernel_integrable (hK : LipschitzWith L K) {X : Ω → E}
    (hX : Integrable X P) (x : E) : Integrable (fun ω => K (x-X ω)) P := by
  have he : Integrable (fun ω => ‖K 0‖+(L : ℝ)*‖x‖+(L : ℝ)*‖X ω‖) P :=
    (integrable_const _).add (hX.norm.const_mul _)
  apply he.mono' (hK.continuous.comp_aestronglyMeasurable
    (aestronglyMeasurable_const.sub hX.aestronglyMeasurable))
  exact ae_of_all _ (fun ω => lipschitz_kernel_growth hK x (X ω))

theorem law_drift_growth (hK : LipschitzWith L K) {X : Ω → E}
    (hX : Integrable X P) (x : E) :
    ‖lawDrift P K X x‖ ≤ ‖K 0‖+(L : ℝ)*‖x‖+(L : ℝ)*(∫ ω, ‖X ω‖ ∂P) := by
  have hk := law_kernel_integrable hK hX x
  have he : Integrable (fun ω => ‖K 0‖+(L : ℝ)*‖x‖+(L : ℝ)*‖X ω‖) P :=
    (integrable_const _).add (hX.norm.const_mul _)
  calc
    _ ≤ ∫ ω, ‖K (x-X ω)‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ‖K 0‖+(L : ℝ)*‖x‖+(L : ℝ)*‖X ω‖ ∂P :=
      integral_mono hk.norm he (fun ω => lipschitz_kernel_growth hK x (X ω))
    _ = _ := by rw [integral_add (integrable_const _) (hX.norm.const_mul _), integral_const_mul]; simp

/-- 共通確率空間の結合を用いた法則ドリフトのLipschitz評価。 -/
theorem law_drift_coupled_bound (hK : LipschitzWith L K) {X Y : Ω → E}
    (hX : Integrable X P) (hY : Integrable Y P) (x y : E) :
    ‖lawDrift P K X x - lawDrift P K Y y‖ ≤
      (L : ℝ)*‖x-y‖+(L : ℝ)*(∫ ω, ‖X ω-Y ω‖ ∂P) := by
  have hkx := law_kernel_integrable hK hX x
  have hky := law_kernel_integrable hK hY y
  have hd : Integrable (fun ω => ‖X ω-Y ω‖) P := (hX.sub hY).norm
  have he : Integrable (fun ω => (L : ℝ)*‖x-y‖+(L : ℝ)*‖X ω-Y ω‖) P :=
    (integrable_const _).add (hd.const_mul _)
  unfold lawDrift
  rw [← integral_sub hkx hky]
  calc
    _ ≤ ∫ ω, ‖K (x-X ω)-K (y-Y ω)‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (L : ℝ)*‖x-y‖+(L : ℝ)*‖X ω-Y ω‖ ∂P := by
      apply integral_mono (hkx.sub hky).norm he
      intro ω
      apply (hK.norm_sub_le (x-X ω) (y-Y ω)).trans
      have ha : (x-X ω)-(y-Y ω) = (x-y)-(X ω-Y ω) := by abel
      rw [ha]
      have hb := mul_le_mul_of_nonneg_left (norm_sub_le (x-y) (X ω-Y ω)) L.coe_nonneg
      simpa only [mul_add] using hb
    _ = _ := by rw [integral_add (integrable_const _) (hd.const_mul _)]; simp [integral_const_mul]

theorem law_drift_lipschitz (hK : LipschitzWith L K) {X : Ω → E} (hX : Integrable X P) :
    LipschitzWith L (lawDrift P K X) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm,sub_self,norm_zero,integral_zero,mul_zero,add_zero] using
    law_drift_coupled_bound hK hX hX x y

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [IsProbabilityMeasure P] in
/-- 法則による積分表示。可積分性は上の補題で別途確保する。 -/
theorem law_drift_map (hK : LipschitzWith L K) {X : Ω → E}
    (hX : Measurable X) (x : E) :
    lawDrift P K X x = ∫ y, K (x-y) ∂(P.map X) := by
  rw [lawDrift, integral_map hX.aemeasurable]
  exact (hK.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable

omit [NormedSpace ℝ E] in
/-- 法則側のBochner積分にも、実際の可積分性を明示する。 -/
theorem law_kernel_map_integrable (hK : LipschitzWith L K) {X : Ω → E}
    (hm : Measurable X) (hX : Integrable X P) (x : E) :
    Integrable (fun y => K (x-y)) (P.map X) :=
  (integrable_map_measure
    (hK.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable hm.aemeasurable).mpr
    (law_kernel_integrable hK hX x)

end WMFKIMeanFieldPicard
