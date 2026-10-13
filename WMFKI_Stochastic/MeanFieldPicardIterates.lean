import WMFKI_Stochastic.MeanFieldPicardStep
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed

open MeasureTheory Set
open scoped NNReal Nat

namespace WMFKIMeanFieldPicard
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {P : Measure Ω} [IsProbabilityMeasure P] {W : Ω → ℝ} {K : E → E} {L : ℝ≥0}
  {T : ℝ} {Z : ℝ → Ω → E}

noncomputable def picardIter (P : Measure Ω) (K : E → E) (T : ℝ) (Z : ℝ → Ω → E) :
    ℕ → ℝ → Ω → E
  | 0 => Z
  | n+1 => picardStep P K T Z (picardIter P K T Z n)

def iterationEnvelope (c l T : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => 1+T*(c+3*l*iterationEnvelope c l T n)

theorem iteration_envelope_nonneg {c l T : ℝ} (hc : 0 ≤ c) (hl : 0 ≤ l) (hT : 0 ≤ T) (n : ℕ) :
    0 ≤ iterationEnvelope c l T n := by
  induction n with
  | zero => norm_num [iterationEnvelope]
  | succ n ih => dsimp only [iterationEnvelope]; positivity

/-- 全有限反復を、未知の解のモーメントを入力せずに構成する。 -/
theorem picard_iter_weighted (hW : InputWeight P W) (hK : LipschitzWith L K) (hT : 0 ≤ T)
    (hZ : WeightedPaths W 1 Z) (n : ℕ) :
    WeightedPaths W (iterationEnvelope ‖K 0‖ (L : ℝ) T n) (picardIter P K T Z n) := by
  induction n with
  | zero => exact hZ
  | succ n ih =>
    exact picard_step_weighted hW hK hT hZ ih
      (iteration_envelope_nonneg (norm_nonneg _) L.coe_nonneg hT n)

/-- 各反復の実際のL4と第4モーメント。反復数に一様とはまだ主張しない。 -/
theorem picard_iter_fourth (hW : InputWeight P W) (hK : LipschitzWith L K) (hT : 0 ≤ T)
    (hZ : WeightedPaths W 1 Z) (n : ℕ) (t : ℝ) :
    MemLp (picardIter P K T Z n t) 4 P ∧
    (∫ ω, ‖picardIter P K T Z n t ω‖^4 ∂P) ≤
      (iterationEnvelope ‖K 0‖ (L : ℝ) T n)^4*(∫ ω, W ω^4 ∂P) := by
  have hY := picard_iter_weighted hW hK hT hZ n
  have hL := weighted_paths_memLp hW hY t
  have hi : Integrable (fun ω => W ω^4) P := by
    simpa only [Real.norm_eq_abs, (show Even (4 : ℕ) from by decide).pow_abs] using
      hW.memLp.integrable_norm_pow (p := 4) (by decide)
  refine ⟨hL, ?_⟩
  rw [← integral_const_mul]
  apply integral_mono (hL.integrable_norm_pow (p := 4) (by decide)) (hi.const_mul _)
  intro ω
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hY.bound t ω) 4

noncomputable def factorialBound (C Λ t : ℝ) (n : ℕ) : ℝ :=
  C*Λ^n*t^(n+1)/(n+1)!

/-- 重み付き反復の階乗評価。時刻区間上ではtimeClipが恒等写像になる。 -/
theorem picard_successive_bound (hW : InputWeight P W) (hK : LipschitzWith L K) (hT : 0 ≤ T)
    (hZ : WeightedPaths W 1 Z) (n : ℕ) (t : ℝ) (ω : Ω) :
    ‖picardIter P K T Z (n+1) t ω-picardIter P K T Z n t ω‖ ≤
      factorialBound (‖K 0‖+3*(L : ℝ)) (3*(L : ℝ)) (timeClip T t) n * W ω := by
  have hw : 0 ≤ W ω := (by norm_num : (0 : ℝ) ≤ 1).trans (hW.one_le ω)
  induction n generalizing t ω with
  | zero =>
    have he : picardIter P K T Z 1 t ω-picardIter P K T Z 0 t ω =
        ∫ s in (0 : ℝ)..timeClip T t, lawDrift P K (Z s) (Z s ω) := by
      simp only [picardIter,picardStep,add_sub_cancel_left]
    rw [he]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := timeClip T t) (fun s _ =>
        weighted_drift_growth hW hK (hZ.measurable s) (by norm_num : (0 : ℝ) ≤ 1) (hZ.bound s) ω)
    rw [sub_zero,abs_of_nonneg (time_clip_bounds hT t).1] at h
    convert h using 1
    simp only [factorialBound]
    ring
  | succ n ih =>
    let C := ‖K 0‖+3*(L : ℝ)
    let Λ := 3*(L : ℝ)
    have hn := picard_iter_weighted hW hK hT hZ
    have h := picard_step_difference hW hK hT (hn (n+1)) (hn n) Z t
      (fun s => C*Λ^n/(n+1)!*s^(n+1))
      ((by fun_prop : Continuous (fun s : ℝ => C*Λ^n/(n+1)!*s^(n+1))).intervalIntegrable _ _)
      (fun s hs => by have hs0 := hs.1; dsimp [C,Λ]; positivity) (fun s hs ω' => ?_) ω
    · apply h.trans_eq
      rw [intervalIntegral.integral_const_mul, integral_pow]
      simp only [factorialBound, Nat.factorial_succ (n+1)]
      dsimp [C,Λ]
      push_cast
      field_simp
      ring
    · have hsT : s ∈ Icc 0 T := ⟨hs.1,hs.2.trans (time_clip_bounds hT t).2⟩
      have hi := ih s ω' ((by norm_num : (0 : ℝ) ≤ 1).trans (hW.one_le ω'))
      rw [time_clip_eq hsT] at hi
      convert hi using 1
      dsimp [factorialBound,C,Λ]
      ring

/-- 時間全体での包絡。切り詰めにより有限Tの定数でよい。 -/
theorem picard_successive_uniform (hW : InputWeight P W) (hK : LipschitzWith L K) (hT : 0 ≤ T)
    (hZ : WeightedPaths W 1 Z) (n : ℕ) (t : ℝ) (ω : Ω) :
    ‖picardIter P K T Z (n+1) t ω-picardIter P K T Z n t ω‖ ≤
      factorialBound (‖K 0‖+3*(L : ℝ)) (3*(L : ℝ)) T n * W ω := by
  apply (picard_successive_bound hW hK hT hZ n t ω).trans
  have hw : 0 ≤ W ω := (by norm_num : (0 : ℝ) ≤ 1).trans (hW.one_le ω)
  unfold factorialBound
  gcongr
  · exact (time_clip_bounds hT t).1
  · exact (time_clip_bounds hT t).2

end WMFKIMeanFieldPicard
