import WMFKI_Stochastic.MeanFieldPicardIterates
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
階乗級数とCauchy判定のAPIは、調査済みSharp-W2のMcKeanVlasovPicard
（Yuhao Lei, commit 84dbe881384ad2f0358857b025ef6fd824ebc9a1, Apache-2.0）を参考にした。
本ファイルは外部の有界係数存在定理をimportしない。確率変数重み、時間切り詰め、
非有界核に必要な可積分性は本段階の補題から供給する。
-/

open MeasureTheory Set Filter Topology
open scoped NNReal Nat

namespace WMFKIMeanFieldPicard

theorem factorial_bound_summable {C Λ T : ℝ} (hC : 0 ≤ C) (hΛ : 0 ≤ Λ) (hT : 0 ≤ T) :
    Summable (factorialBound C Λ T) := by
  have hs := (Real.summable_pow_div_factorial (Λ*T)).mul_left (C*T)
  apply Summable.of_nonneg_of_le (fun n => by unfold factorialBound; positivity) _ hs
  intro n
  have hd : (0 : ℝ) < (n ! : ℝ) := by positivity
  have hf : (n ! : ℝ) ≤ ((n+1)! : ℝ) := by exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  calc
    _ ≤ C*Λ^n*T^(n+1)/(n ! : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hd hf
    _ = _ := by ring

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {P : Measure Ω} [IsProbabilityMeasure P] {W : Ω → ℝ} {K : E → E} {L : ℝ≥0}
  {T : ℝ} {Z : ℝ → Ω → E}

noncomputable def picardLimit (P : Measure Ω) (K : E → E) (T : ℝ) (Z : ℝ → Ω → E)
    (t : ℝ) (ω : Ω) : E := limUnder atTop (fun n => picardIter P K T Z n t ω)

theorem picard_limit_tendsto (hW : InputWeight P W) (hK : LipschitzWith L K) (hT : 0 ≤ T)
    (hZ : WeightedPaths W 1 Z) (t : ℝ) (ω : Ω) :
    Tendsto (fun n => picardIter P K T Z n t ω) atTop (𝓝 (picardLimit P K T Z t ω)) := by
  have hs := (factorial_bound_summable (C := ‖K 0‖+3*(L : ℝ))
    (Λ := 3*(L : ℝ)) (by positivity) (by positivity) hT).mul_right (W ω)
  have hc : CauchySeq (fun n => picardIter P K T Z n t ω) :=
    cauchySeq_of_dist_le_of_summable _ (fun n => by
      rw [dist_comm,dist_eq_norm]
      exact picard_successive_uniform hW hK hT hZ n t ω) hs
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete hc)

/-- 時刻に一様、標本ごとに重みWを持つ尾部評価。omega一様とは主張しない。 -/
theorem picard_limit_tail (hW : InputWeight P W) (hK : LipschitzWith L K) (hT : 0 ≤ T)
    (hZ : WeightedPaths W 1 Z) (n : ℕ) (t : ℝ) (ω : Ω) :
    ‖picardIter P K T Z n t ω-picardLimit P K T Z t ω‖ ≤
      (∑' m, factorialBound (‖K 0‖+3*(L : ℝ)) (3*(L : ℝ)) T (m+n))*W ω := by
  have hs := (factorial_bound_summable (C := ‖K 0‖+3*(L : ℝ))
    (Λ := 3*(L : ℝ)) (by positivity) (by positivity) hT).mul_right (W ω)
  rw [← dist_eq_norm]
  have hd := dist_le_tsum_of_dist_le_of_tendsto _ (fun k => by
    rw [dist_comm,dist_eq_norm]
    exact picard_successive_uniform hW hK hT hZ k t ω) hs
    (picard_limit_tendsto hW hK hT hZ t ω) n
  apply hd.trans_eq
  rw [← tsum_mul_right]
  apply tsum_congr
  intro m
  rw [add_comm n m]

/-- 可測性は反復の各断面から、連続性は標本ごとの時間一様収束から導く。 -/
theorem picard_limit_weighted (hW : InputWeight P W) (hK : LipschitzWith L K) (hT : 0 ≤ T)
    (hZ : WeightedPaths W 1 Z) :
    WeightedPaths W (1+∑' n, factorialBound (‖K 0‖+3*(L : ℝ)) (3*(L : ℝ)) T n)
      (picardLimit P K T Z) := by
  constructor
  · intro t
    exact measurable_of_tendsto_metrizable
      (fun n => (picard_iter_weighted hW hK hT hZ n).measurable t)
      (tendsto_pi_nhds.mpr (fun ω => picard_limit_tendsto hW hK hT hZ t ω))
  · intro ω
    have hu : TendstoUniformly (fun n t => picardIter P K T Z n t ω)
        (fun t => picardLimit P K T Z t ω) atTop := by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      have ht : Tendsto (fun n => (∑' m,
          factorialBound (‖K 0‖+3*(L : ℝ)) (3*(L : ℝ)) T (m+n))*W ω) atTop (𝓝 0) := by
        simpa using (tendsto_sum_nat_add
          (factorialBound (‖K 0‖+3*(L : ℝ)) (3*(L : ℝ)) T)).mul_const (W ω)
      filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn t
      rw [dist_comm,dist_eq_norm]
      exact (picard_limit_tail hW hK hT hZ n t ω).trans_lt hn
    exact hu.continuous (Frequently.of_forall (fun n => (picard_iter_weighted hW hK hT hZ n).continuous ω))
  · intro t ω
    have hd := picard_limit_tail hW hK hT hZ 0 t ω
    simp only [picardIter,Nat.add_zero] at hd
    rw [norm_sub_rev] at hd
    have hz := hZ.bound t ω
    have hn := norm_add_le (picardLimit P K T Z t ω-Z t ω) (Z t ω)
    simp only [sub_add_cancel] at hn
    nlinarith

/-- 極限が実際のPicard固定点であることを証明する。 -/
theorem picard_limit_fixed_point (hW : InputWeight P W) (hK : LipschitzWith L K) (hT : 0 ≤ T)
    (hZ : WeightedPaths W 1 Z) (t : ℝ) (ω : Ω) :
    picardLimit P K T Z t ω = picardStep P K T Z (picardLimit P K T Z) t ω := by
  let b := factorialBound (‖K 0‖+3*(L : ℝ)) (3*(L : ℝ)) T
  let tail := fun n => ∑' m, b (m+n)
  have ht : Tendsto tail atTop (𝓝 0) := tendsto_sum_nat_add b
  have htail (n : ℕ) : 0 ≤ tail n := tsum_nonneg (fun m => by dsimp [b,factorialBound]; positivity)
  have hlim := picard_limit_weighted hW hK hT hZ
  have hstep : Tendsto (fun n => picardIter P K T Z (n+1) t ω) atTop
      (𝓝 (picardStep P K T Z (picardLimit P K T Z) t ω)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb (n : ℕ) := picard_step_difference hW hK hT (picard_iter_weighted hW hK hT hZ n)
      hlim Z t (fun _ => tail n) intervalIntegrable_const (fun _ _ => htail n)
      (fun s _ ω' => picard_limit_tail hW hK hT hZ n s ω') ω
    have h0 : Tendsto (fun n => (3*(L : ℝ)*W ω)*(timeClip T t*tail n)) atTop (𝓝 0) := by
      simpa using (ht.const_mul (timeClip T t)).const_mul (3*(L : ℝ)*W ω)
    apply squeeze_zero (fun _ => norm_nonneg _) _ h0
    intro n
    have h := hb n
    rw [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at h
    exact h
  have hs := (picard_limit_tendsto hW hK hT hZ t ω).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hs hstep

/-- 有限時間の解析的な平均場方程式。Brownian構成・適合性・一意性は別段階。 -/
theorem picard_limit_mean_field_equation (hW : InputWeight P W) (hK : LipschitzWith L K)
    (hT : 0 ≤ T) (hZ : WeightedPaths W 1 Z) (t : ℝ) (ht : t ∈ Icc 0 T) (ω : Ω) :
    picardLimit P K T Z t ω = Z t ω + ∫ s in (0 : ℝ)..t,
      ∫ y, K (picardLimit P K T Z s ω-y) ∂(P.map (picardLimit P K T Z s)) := by
  have hm := (picard_limit_weighted hW hK hT hZ).measurable
  rw [picard_limit_fixed_point hW hK hT hZ t ω, picardStep, time_clip_eq ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  exact law_drift_map hK (hm s) _

end WMFKIMeanFieldPicard
