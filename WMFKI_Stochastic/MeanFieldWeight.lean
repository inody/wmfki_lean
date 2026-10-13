import WMFKI_Stochastic.MeanFieldDriftGrowth

open MeasureTheory

namespace WMFKIMeanFieldPicard
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- 原始入力の包絡を正規化するための解析的条件。解や誤差のモーメントではない。 -/
structure InputWeight (P : Measure Ω) (W : Ω → ℝ) : Prop where
  measurable : Measurable W
  memLp : MemLp W 4 P
  one_le : ∀ ω, 1 ≤ W ω
  mean_le : ∀ ω, (∫ ω', W ω' ∂P) ≤ 2*W ω

noncomputable def normalizedWeight (P : Measure Ω) (R : Ω → ℝ) (ω : Ω) : ℝ :=
  1+|R ω|+(∫ ω', |R ω'| ∂P)

theorem normalized_weight (R : Ω → ℝ) (hR : Measurable R) (hL : MemLp R 4 P) :
    InputWeight P (normalizedWeight P R) ∧ ∀ ω, R ω ≤ normalizedWeight P R ω := by
  have hi : Integrable (fun ω => |R ω|) P := by
    simpa only [Real.norm_eq_abs] using (hL.integrable (by norm_num)).norm
  have hLP : MemLp (fun ω => |R ω|) 4 P := by simpa only [Real.norm_eq_abs] using hL.norm
  have hn : 0 ≤ ∫ ω, |R ω| ∂P := integral_nonneg (fun _ => abs_nonneg _)
  have hmabs : Measurable (fun ω => |R ω|) := continuous_abs.measurable.comp hR
  have hm : Measurable (fun ω => 1+|R ω|+(∫ ω', |R ω'| ∂P)) :=
    (measurable_const.add hmabs).add measurable_const
  have hw : MemLp (fun ω => 1+|R ω|+(∫ ω', |R ω'| ∂P)) 4 P :=
    ((memLp_const (μ := P) (p := 4) (1 : ℝ)).add hLP).add (memLp_const (∫ ω, |R ω| ∂P))
  have he : (∫ ω, normalizedWeight P R ω ∂P) = 1+2*(∫ ω, |R ω| ∂P) := by
    unfold normalizedWeight
    rw [integral_add (f := fun ω => 1+|R ω|) ((integrable_const (1 : ℝ)).add hi) (integrable_const (∫ ω, |R ω| ∂P)),
      integral_add (integrable_const (1 : ℝ)) hi]
    simp
    ring
  refine ⟨⟨hm,hw,?_,?_⟩,?_⟩
  · intro ω; dsimp [normalizedWeight]; linarith [abs_nonneg (R ω)]
  · intro ω; rw [he]; dsimp [normalizedWeight]; linarith [abs_nonneg (R ω)]
  · intro ω; dsimp [normalizedWeight]; linarith [le_abs_self (R ω)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {W : Ω → ℝ} {K : E → E} {L : NNReal}

omit [IsProbabilityMeasure P] [NormedSpace ℝ E] in
/-- 包絡から各断面のL4を導く。 -/
theorem weighted_section_memLp (hW : InputWeight P W) {X : Ω → E} (hm : Measurable X)
    (a : ℝ) (hb : ∀ ω, ‖X ω‖ ≤ a*W ω) : MemLp X 4 P :=
  (hW.memLp.const_mul a).mono' hm.aestronglyMeasurable (ae_of_all _ hb)

theorem weighted_drift_growth (hW : InputWeight P W) (hK : LipschitzWith L K)
    {X : Ω → E} (hm : Measurable X) {a : ℝ} (ha : 0 ≤ a) (hb : ∀ ω, ‖X ω‖ ≤ a*W ω)
    (ω : Ω) : ‖lawDrift P K X (X ω)‖ ≤ (‖K 0‖+3*(L : ℝ)*a)*W ω := by
  have hi := (weighted_section_memLp hW hm a hb).integrable (by norm_num)
  have hwi := hW.memLp.integrable (by norm_num)
  have he : (∫ ω', ‖X ω'‖ ∂P) ≤ a*(∫ ω', W ω' ∂P) := by
    rw [← integral_const_mul]
    exact integral_mono hi.norm (hwi.const_mul a) hb
  have hmom := (mul_le_mul_of_nonneg_left he L.coe_nonneg).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hW.mean_le ω) ha) L.coe_nonneg)
  have hpt := mul_le_mul_of_nonneg_left (hb ω) L.coe_nonneg
  have hk := mul_le_mul_of_nonneg_left (hW.one_le ω) (norm_nonneg (K 0))
  have hg := law_drift_growth hK hi (X ω)
  nlinarith

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- 重み付き共通結合評価。期待値を先に存在させてから比較する。 -/
theorem weighted_drift_difference (hW : InputWeight P W) (hK : LipschitzWith L K)
    {X Y : Ω → E} (hX : Integrable X P) (hY : Integrable Y P)
    {q : ℝ} (hq : 0 ≤ q) (hb : ∀ ω, ‖X ω-Y ω‖ ≤ q*W ω) (ω : Ω) :
    ‖lawDrift P K X (X ω)-lawDrift P K Y (Y ω)‖ ≤ 3*(L : ℝ)*q*W ω := by
  have hwi := hW.memLp.integrable (by norm_num)
  have he : (∫ ω', ‖X ω'-Y ω'‖ ∂P) ≤ q*(∫ ω', W ω' ∂P) := by
    rw [← integral_const_mul]
    exact integral_mono (hX.sub hY).norm (hwi.const_mul q) hb
  have hmom := (mul_le_mul_of_nonneg_left he L.coe_nonneg).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hW.mean_le ω) hq) L.coe_nonneg)
  have hpt := mul_le_mul_of_nonneg_left (hb ω) L.coe_nonneg
  have hg := law_drift_coupled_bound hK hX hY (X ω) (Y ω)
  nlinarith

end WMFKIMeanFieldPicard
