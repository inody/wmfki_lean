import WMFKI_Stochastic.MeanFieldFiniteHorizon
import EndToEndBrownianPathMoments
import WMFKI_Stochastic.IndependentBrownianFamilyProbe
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory Set
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter12
open scoped NNReal

namespace WMFKIMeanFieldPicard
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- 既存BrownianSystemの有限時間制限。t∈[0,T]では実際のBrownian座標と一致。 -/
noncomputable def compactBrownianForcing (B : BrownianSystem P d) (T : ℝ) (hT : 0 ≤ T)
    (σ : ℝ) (t : ℝ) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  σ • WithLp.toLp 2 (brownianSystemCompactPath B T ω ⟨timeClip T t,time_clip_bounds hT t⟩)

/-- 原始Brownian経路のL4から駆動の包絡を構成する。解のモーメントは仮定しない。 -/
theorem brownian_forcing_envelope (B : BrownianSystem P d) (T : ℝ) (hT : 0 ≤ T) (σ : ℝ) :
    let F := compactBrownianForcing B T hT σ
    (∀ t, Measurable (F t)) ∧ (∀ ω, Continuous (fun t => F t ω)) ∧
    (∀ᵐ ω ∂P, F 0 ω = 0) ∧
    ∃ H : Ω → ℝ, Measurable H ∧ MemLp H 4 P ∧ (∀ ω, 0 ≤ H ω) ∧
      (∀ t ω, ‖F t ω‖ ≤ H ω) ∧
      (∀ t ∈ Icc 0 T, ∀ ω, F t ω =
        σ • WithLp.toLp 2 (fun j => B.W j (realTimeClamp t) ω)) := by
  dsimp only
  let Q := brownianSystemCompactPath B T
  let H := fun ω => |σ| * (d : ℝ)*‖Q ω‖
  have hQm := brownian_system_compact_measurable B T
  have hQL := Asakura.EndToEnd.brownian_system_path_memLp P B T hT 4 (by norm_num)
  have hH : MemLp H 4 P := hQL.norm.const_mul (|σ| * (d : ℝ))
  have hHn (ω : Ω) : 0 ≤ H ω := by dsimp [H]; positivity
  have he (t : ℝ) (ht : t ∈ Icc 0 T) (ω : Ω) : compactBrownianForcing B T hT σ t ω =
      σ • WithLp.toLp 2 (fun j => B.W j (realTimeClamp t) ω) := by
    unfold compactBrownianForcing
    have ht' : (⟨timeClip T t,time_clip_bounds hT t⟩ : Icc (0 : ℝ) T) = ⟨t,ht⟩ :=
      Subtype.ext (time_clip_eq ht)
    rw [ht']
    rfl
  refine ⟨?_,?_,?_,H,?_,hH,hHn,?_,he⟩
  · intro t
    change Measurable (fun ω => σ • WithLp.toLp 2
      (brownianSystemCompactPath B T ω ⟨timeClip T t,time_clip_bounds hT t⟩))
    have hm0 : Measurable (fun ω => Q ω ⟨timeClip T t,time_clip_bounds hT t⟩) :=
      (ContinuousMap.measurable_eval (⟨timeClip T t,time_clip_bounds hT t⟩ : Icc (0 : ℝ) T)).comp hQm
    have hm1 : Measurable (fun ω => (WithLp.toLp 2 (Q ω ⟨timeClip T t,time_clip_bounds hT t⟩) :
        EuclideanSpace ℝ (Fin d))) := (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp hm0
    exact hm1.const_smul σ
  · intro ω
    have ht : Continuous (fun t => (⟨timeClip T t,time_clip_bounds hT t⟩ : Icc (0 : ℝ) T)) :=
      (continuous_const.min (continuous_const.max continuous_id)).subtype_mk _
    change Continuous (fun t => σ • WithLp.toLp 2 (Q ω ⟨timeClip T t,time_clip_bounds hT t⟩))
    exact ((PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
      ((Q ω).continuous.comp ht)).const_smul σ
  · have hj (j : Fin d) : B.W j (realTimeClamp 0) =ᵐ[P] 0 := by
      obtain ⟨τ,_,_,_,_,hb⟩ := (B.martingale j).localizers
      have hz := (hb 0).1.initial
      have he0 : (realTimeClamp 0 : HalfClosedTime) = ⊥ := Subtype.ext (real_time_clamp_eq 0 le_rfl le_top)
      simpa only [he0,min_eq_right bot_le] using hz
    have hall := (ae_all_iff).mpr hj
    filter_upwards [hall] with ω hω
    rw [he 0 ⟨le_rfl,hT⟩ ω]
    have hz : (fun j => B.W j (realTimeClamp 0) ω) = 0 := by funext j; exact hω j
    rw [hz]
    simp
  · exact measurable_const.mul hQm.norm
  · intro t ω
    let x : EuclideanSpace ℝ (Fin d) :=
      WithLp.toLp 2 (Q ω ⟨timeClip T t,time_clip_bounds hT t⟩)
    have hc (j : Fin d) : ‖x j‖ ≤ ‖Q ω‖ :=
      (norm_le_pi_norm _ j).trans ((Q ω).norm_coe_le_norm ⟨timeClip T t,time_clip_bounds hT t⟩)
    have hsq : ‖x‖^2 ≤ ((d : ℝ)*‖Q ω‖)^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc
        _ ≤ ∑ _j : Fin d, ‖Q ω‖^2 := by
          apply Finset.sum_le_sum
          intro j _
          simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) (hc j) 2
        _ ≤ (∑ _j : Fin d, ‖Q ω‖)^2 := Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)
        _ = _ := by simp
    have hx : ‖x‖ ≤ (d : ℝ)*‖Q ω‖ := by
      nlinarith [norm_nonneg x, mul_nonneg (Nat.cast_nonneg d) (norm_nonneg (Q ω))]
    change ‖σ • x‖ ≤ H ω
    rw [norm_smul,Real.norm_eq_abs]
    dsimp [H]
    nlinarith [mul_le_mul_of_nonneg_left hx (abs_nonneg σ)]

/-- 実際のBrownian駆動から有限時間の平均場積分方程式を構成する。
    フィルトレーション適合性・一意性・iidコピーはこの終点では未主張。 -/
theorem exists_mean_field_brownian (B : BrownianSystem P d) (T : ℝ) (hT : 0 ≤ T)
    (σ : ℝ) (ξ : Ω → EuclideanSpace ℝ (Fin d)) (hξm : Measurable ξ) (hξ : MemLp ξ 4 P)
    {L : ℝ≥0} (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : LipschitzWith L K) :
    ∃ Y : ℝ → Ω → EuclideanSpace ℝ (Fin d), (∀ t, Measurable (Y t)) ∧
      (∀ ω, Continuous (fun t => Y t ω)) ∧ (∀ t, MemLp (Y t) 4 P) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t, (∫ ω, ‖Y t ω‖^4 ∂P) ≤ C) ∧
      (∀ ω, Continuous (fun t => ∫ y, K (Y t ω-y) ∂(P.map (Y t)))) ∧
      (∀ᵐ ω ∂P, Y 0 ω = ξ ω ∧ ∀ t ∈ Icc 0 T,
        Y t ω = ξ ω + (∫ u in (0 : ℝ)..t, ∫ y, K (Y u ω-y) ∂(P.map (Y u))) +
          σ • WithLp.toLp 2 (fun j => B.W j (realTimeClamp t) ω)) := by
  obtain ⟨hFm,hFc,hF0,H,hHm,hHL,hHn,hHb,hFe⟩ := brownian_forcing_envelope B T hT σ
  let R := fun ω => ‖ξ ω‖+H ω
  have hRm : Measurable R := hξm.norm.add hHm
  have hRL : MemLp R 4 P := hξ.norm.add hHL
  have hRb : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, ‖ξ ω+compactBrownianForcing B T hT σ t ω‖ ≤ R ω := by
    apply ae_of_all
    intro ω t _
    exact (norm_add_le _ _).trans (add_le_add le_rfl (hHb t ω))
  obtain ⟨Y,hm,hc,hL,hM,hd,he⟩ := exists_mean_field_additive T hT ξ hξm
    (compactBrownianForcing B T hT σ) hFm (ae_of_all _ (fun ω => (hFc ω).continuousOn)) hF0
    R hRm hRL hRb K hK
  refine ⟨Y,hm,hc,hL,hM,hd,?_⟩
  filter_upwards [he] with ω hω
  refine ⟨hω.1,fun t ht => ?_⟩
  rw [← hFe t ht ω]
  exact hω.2 t ht

/-- 与えられたa.s.連続Brownian族への同一確率空間上の接続。
    同時零集合で元の全駆動座標へ戻す。初期値との独立性・適合性は未使用。 -/
theorem exists_mean_field_of_brownian_family (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ) (hT : 0 ≤ T) (σ : ℝ)
    (ξ : Ω → EuclideanSpace ℝ (Fin d)) (hξm : Measurable ξ) (hξ : MemLp ξ 4 P)
    (W : Fin d → ℝ≥0 → Ω → ℝ) (hW : ∀ j, ProbabilityTheory.IsBrownianReal (W j) P)
    (hm : ∀ j t, Measurable (W j t))
    (hI : ProbabilityTheory.iIndepFun (fun j ω t => W j t ω) P)
    {L : ℝ≥0} (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : LipschitzWith L K) :
    ∃ Y : ℝ → Ω → EuclideanSpace ℝ (Fin d), (∀ t, Measurable (Y t)) ∧
      (∀ ω, Continuous (fun t => Y t ω)) ∧ (∀ t, MemLp (Y t) 4 P) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t, (∫ ω, ‖Y t ω‖^4 ∂P) ≤ C) ∧
      (∀ ω, Continuous (fun t => ∫ y, K (Y t ω-y) ∂(P.map (Y t)))) ∧
      (∀ᵐ ω ∂P, Y 0 ω = ξ ω ∧ ∀ t ∈ Icc 0 T,
        Y t ω = ξ ω + (∫ u in (0 : ℝ)..t, ∫ y, K (Y u ω-y) ∂(P.map (Y u))) +
          σ • WithLp.toLp 2 (fun j => W j (halfTimeReal (realTimeClamp t)) ω)) := by
  obtain ⟨B,hB⟩ := WMFKIExternalProbe.exists_brownian_family_system P W hW hm hI
  obtain ⟨Y,hYm,hYc,hYL,hYM,hYd,he⟩ := exists_mean_field_brownian B T hT σ ξ hξm hξ K hK
  refine ⟨Y,hYm,hYc,hYL,hYM,hYd,?_⟩
  filter_upwards [he,hB] with ω hω hBω
  refine ⟨hω.1,fun t ht => ?_⟩
  rw [hω.2 t ht]
  congr 2
  apply congrArg (WithLp.toLp 2)
  funext j
  exact hBω j (realTimeClamp t)

end WMFKIMeanFieldPicard
