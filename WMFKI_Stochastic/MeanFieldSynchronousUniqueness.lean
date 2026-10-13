import WMFKI_Stochastic.MeanFieldCompletedMeasurable

open MeasureTheory Set Filter Topology
open WMFKIMeanFieldPicard
open scoped NNReal Nat

namespace WMFKIMeanFieldAdapted
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {W : Ω → ℝ} {K : E → E} {L : ℝ≥0} {T : ℝ} {X Y Z : ℝ → Ω → E}

/-- 共通確率1集合上の平均場積分方程式。下の一意性定理は別途経路包絡を要求する。 -/
def MeanFieldEquation (P : Measure Ω) (K : E → E) (T : ℝ) (Z X : ℝ → Ω → E) : Prop :=
  ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, X t ω = Z t ω + ∫ s in (0 : ℝ)..t, lawDrift P K (X s) (X s ω)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure P] in
/-- 全時刻で共通の零集合変更は、法則ドリフトを含めて方程式を保つ。 -/
theorem mean_field_equation_congr {X' : ℝ → Ω → E}
    (he : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, X' t ω = X t ω) (hX : MeanFieldEquation P K T Z X) :
    MeanFieldEquation P K T Z X' := by
  filter_upwards [hX,he] with ω hω heω
  intro t ht
  rw [heω t ht,hω t ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hsT : s ∈ Icc 0 T := by rw [uIcc_of_le ht.1] at hs; exact ⟨hs.1,hs.2.trans ht.2⟩
  unfold lawDrift
  apply integral_congr_ae
  filter_upwards [he] with ω' heω'
  rw [heω s hsT,heω' s hsT]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- 差分の包絡はa.e.でよい。期待値比較の前に可積分性を確保する。 -/
theorem ae_weighted_drift_difference (hW : InputWeight P W) (hK : LipschitzWith L K)
    {U V : Ω → E} (hU : Integrable U P) (hV : Integrable V P)
    {q : ℝ} (hq : 0 ≤ q) (hb : ∀ᵐ ω ∂P, ‖U ω-V ω‖ ≤ q*W ω)
    (ω : Ω) (hω : ‖U ω-V ω‖ ≤ q*W ω) :
    ‖lawDrift P K U (U ω)-lawDrift P K V (V ω)‖ ≤ 3*(L : ℝ)*q*W ω := by
  have hWi := hW.memLp.integrable (by norm_num)
  have hi : (∫ ω, ‖U ω-V ω‖ ∂P) ≤ q*(∫ ω, W ω ∂P) := by
    rw [← integral_const_mul]
    exact integral_mono_ae (hU.sub hV).norm (hWi.const_mul q) hb
  calc
    _ ≤ (L : ℝ)*‖U ω-V ω‖+(L : ℝ)*(∫ ω, ‖U ω-V ω‖ ∂P) := law_drift_coupled_bound hK hU hV _ _
    _ ≤ (L : ℝ)*(q*W ω)+(L : ℝ)*(q*(2*W ω)) :=
      add_le_add (mul_le_mul_of_nonneg_left hω L.coe_nonneg)
        (mul_le_mul_of_nonneg_left (hi.trans (mul_le_mul_of_nonneg_left (hW.mean_le ω) hq)) L.coe_nonneg)
    _ = _ := by ring

/-- 共通駆動が相殺された差分の一段評価。 -/
theorem synchronous_difference_step (hW : InputWeight P W) (hK : LipschitzWith L K)
    (hX : WeightedPaths W 1 X) (hY : WeightedPaths W 1 Y)
    (heX : MeanFieldEquation P K T Z X) (heY : MeanFieldEquation P K T Z Y)
    (q : ℝ → ℝ) (hqc : Continuous q) (hqn : ∀ s ∈ Icc 0 T, 0 ≤ q s)
    (hb : ∀ᵐ ω ∂P, ∀ s ∈ Icc 0 T, ‖X s ω-Y s ω‖ ≤ q s*W ω) :
    ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, ‖X t ω-Y t ω‖ ≤ 3*(L : ℝ)*(∫ s in (0 : ℝ)..t, q s)*W ω := by
  filter_upwards [heX,heY,hb] with ω hx hy hω
  intro t ht
  have he : X t ω-Y t ω = ∫ s in (0 : ℝ)..t,
      lawDrift P K (X s) (X s ω)-lawDrift P K (Y s) (Y s ω) := by
    rw [intervalIntegral.integral_sub
      ((continuous_along_drift hW hK hX ω).intervalIntegrable _ _)
      ((continuous_along_drift hW hK hY ω).intervalIntegrable _ _),hx t ht,hy t ht]
    abel
  rw [he]
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, (3*(L : ℝ)*W ω)*q s := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht.1 _ ((hqc.intervalIntegrable _ _).const_mul _)
      apply ae_of_all
      intro s hs
      have hsT : s ∈ Icc 0 T := ⟨hs.1.le,hs.2.trans ht.2⟩
      have hd := ae_weighted_drift_difference hW hK
        ((weighted_paths_memLp hW hX s).integrable (by norm_num))
        ((weighted_paths_memLp hW hY s).integrable (by norm_num)) (hqn s hsT)
        (hb.mono (fun ω' hω' => hω' s hsT)) ω (hω s hsT)
      convert hd using 1
      ring
    _ = _ := by rw [intervalIntegral.integral_const_mul]; ring

/-- 階乗反復により、a.e.方程式を満たす重み付き解どうしは全時刻同時に一致する。 -/
theorem weighted_mean_field_unique (hW : InputWeight P W) (hK : LipschitzWith L K)
    (hX : WeightedPaths W 1 X) (hY : WeightedPaths W 1 Y)
    (heX : MeanFieldEquation P K T Z X) (heY : MeanFieldEquation P K T Z Y) :
    ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, X t ω = Y t ω := by
  let Λ := 3*(L : ℝ)
  have hbase : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, ‖X t ω-Y t ω‖ ≤ 2*W ω := by
    apply ae_of_all
    intro ω t _
    have hx := hX.bound t ω
    have hy := hY.bound t ω
    have hn := norm_sub_le (X t ω) (Y t ω)
    linarith
  have hf (n : ℕ) : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T,
      ‖X t ω-Y t ω‖ ≤ factorialBound (2*Λ) Λ t n*W ω := by
    induction n with
    | zero =>
      have hs := synchronous_difference_step hW hK hX hY heX heY (fun _ => 2)
        continuous_const (fun _ _ => by norm_num) hbase
      filter_upwards [hs] with ω hω t ht
      convert hω t ht using 1
      simp only [factorialBound,intervalIntegral.integral_const,sub_zero,smul_eq_mul]
      dsimp [Λ]
      ring
    | succ n ih =>
      have hs := synchronous_difference_step hW hK hX hY heX heY
        (fun s => (2*Λ)*Λ^n/(n+1)!*s^(n+1)) (by fun_prop)
        (fun s hs => by have := hs.1; dsimp [Λ]; positivity) ?_
      · filter_upwards [hs] with ω hω t ht
        apply (hω t ht).trans_eq
        rw [intervalIntegral.integral_const_mul,integral_pow]
        simp only [factorialBound,Nat.factorial_succ (n+1)]
        dsimp [Λ]
        push_cast
        field_simp
        ring
      · filter_upwards [ih] with ω hω t ht
        convert hω t ht using 1
        unfold factorialBound
        ring
  have hall := ae_all_iff.mpr hf
  filter_upwards [hall] with ω hω t ht
  have hs := (factorial_bound_summable (C := 2*Λ) (Λ := Λ)
    (by dsimp [Λ]; positivity) (by dsimp [Λ]; positivity) ht.1).mul_right (W ω)
  have hz : ‖X t ω-Y t ω‖ ≤ 0 :=
    ge_of_tendsto hs.tendsto_atTop_zero (Filter.Eventually.of_forall (fun n => hω n t ht))
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

end WMFKIMeanFieldAdapted
