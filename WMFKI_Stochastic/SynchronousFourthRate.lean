import WMFKI_Stochastic.SynchronousPathEnvelope
import WMFKI_Stochastic.FourthMomentAlgebra

open MeasureTheory ProbabilityTheory Set
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
open WMFKISynchronousModel WMFKIExternalProbe
open scoped NNReal BigOperators
namespace WMFKIRealizedFluctuation
variable {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω] {N d : ℕ}

/-- Nとは無関係なGronwall・時間積分定数。L=0やT=0で割り算しない。 -/
noncomputable def synchronousFourthConstant (L : ℝ≥0) (T C : ℝ) : ℝ :=
  8*(Real.exp (((L : ℝ)+1)*T))^4 *
    (1+(((L : ℝ)+1)*T*Real.exp (2*((L : ℝ)+1)*T))^4)*T^4*C

theorem coupling_envelope_fourth (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P] {T R C : ℝ} (hT : 0 ≤ T)
    {ξ : A → EuclideanSpace ℝ (Fin d)} {D Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d)}
    {L : ℝ≥0} {K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hK : LipschitzWith L K) (hy : ArrayNonlinearFamily π P T K ξ D Y R)
    (hF : UniformFluctuationFourth π P T K Y C) (hN : 0 < N) (i : Fin N) :
    MemLp (couplingEnvelope π P T L K Y i) 4 (arrayMeasure π P (Fin N)) ∧
    (∫ z, (couplingEnvelope π P T L K Y i z)^4 ∂arrayMeasure π P (Fin N)) ≤
      synchronousFourthConstant L T C/(N : ℝ)^2 := by
  have ha j := fluctuation_time_fourth π P hT hK hy hF hN j
  obtain ⟨hm,hb⟩ := comparison_envelope_l4 hN (fluctuationTimeEnvelope π P T K Y)
    (fun j => (ha j).1) (T^4*C/(N : ℝ)^2) (fun j => (ha j).2.1)
    (((L : ℝ)+1)*T*Real.exp (2*((L : ℝ)+1)*T)) (Real.exp (((L : ℝ)+1)*T)) i
  refine ⟨hm,hb.trans_eq ?_⟩
  unfold synchronousFourthConstant
  ring

/-- 同期差自体のL4を包絡から導き、その後に期待値を比較する。 -/
theorem synchronous_fourth_rate (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P] (hN : 0 < N)
    (W : Fin d → ℝ≥0 → Ω → ℝ) (ξ : A → EuclideanSpace ℝ (Fin d))
    (T : ℝ) (hT : 0 ≤ T) (σ R C : ℝ) {L : ℝ≥0}
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : LipschitzWith L K)
    (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d))
    (hy : ArrayNonlinearFamily π P T K ξ
      (fun t z => σ • WithLp.toLp 2 (fun j => W j (halfTimeReal (realTimeClamp t)) z.2)) Y R)
    (hF : UniformFluctuationFourth π P T K Y C)
    (B : BrownianSystem (arrayMeasure π P (Fin N)) (N*d))
    (X : HalfClosedTime → (Fin N → A) × (Fin N → Ω) → Fin (N*d) → ℝ)
    (hs : SynchronousParticlePair π P W ξ T σ K Y B X) :
    ∀ i : Fin N, ∀ t ∈ Icc 0 T,
      MemLp (fun z => realParticle X i t z-arrayCopy Y i t z) 4 (arrayMeasure π P (Fin N)) ∧
      (∫ z, ‖realParticle X i t z-arrayCopy Y i t z‖^4 ∂arrayMeasure π P (Fin N)) ≤
        synchronousFourthConstant L T C/(N : ℝ)^2 := by
  have hd := synchronous_path_envelope π P hN W ξ T hT σ R C K hK Y hy hF B X hs
  intro i t ht
  obtain ⟨hE,hB⟩ := coupling_envelope_fourth π P hT hK hy hF hN i
  have hx : Measurable (fun z => realParticle X i t z) :=
    (continuous_particlePositions N d i).measurable.comp
      ((hs.solution.adapted _ (real_time_below t ht.1 (EReal.coe_lt_top _))).mono (B.le _) le_rfl)
  have hm := hE.of_le (hx.sub ((hy.paths N i).measurable t ht)).aestronglyMeasurable (by
    filter_upwards [hd] with z hz
    exact (hz i t ht).trans (le_abs_self _))
  refine ⟨hm,?_⟩
  apply (integral_mono_ae (hm.integrable_norm_pow (p := 4) (by decide)) (integrable_fourth hE) ?_).trans hB
  filter_upwards [hd] with z hz
  exact pow_le_pow_left₀ (norm_nonneg _) (hz i t ht) 4

set_option maxHeartbeats 1000000 in
/-- 原始初期値・独立Brownian・globally Lipschitz核から、実際の同期L4率を構成。
    Cは全N・ラベル・時刻より先に選ぶ。解や揺らぎの評価を原始仮定にしない。 -/
theorem exists_synchronous_fourth_rate (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P]
    (W : Fin d → ℝ≥0 → Ω → ℝ) (hW : ∀ j, IsBrownianReal (W j) P)
    (hm : ∀ j t, Measurable (W j t)) (hI : iIndepFun (fun j ω t => W j t ω) P)
    (ξ : A → EuclideanSpace ℝ (Fin d)) (hξm : Measurable ξ) (hξ : MemLp ξ 4 π)
    (T : ℝ) (hT : 0 ≤ T) (σ : ℝ) {L : ℝ≥0}
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : LipschitzWith L K) :
    ∃ (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d)) (R C : ℝ),
      ArrayNonlinearFamily π P T K ξ
        (fun t z => σ • WithLp.toLp 2 (fun j => W j (halfTimeReal (realTimeClamp t)) z.2)) Y R ∧
      0 ≤ C ∧ ∀ N : ℕ, 0 < N →
      ∃ (B : BrownianSystem (arrayMeasure π P (Fin N)) (N*d))
        (X : HalfClosedTime → (Fin N → A) × (Fin N → Ω) → Fin (N*d) → ℝ),
        SynchronousParticlePair π P W ξ T σ K Y B X ∧
        ∀ i : Fin N, ∀ t ∈ Icc 0 T,
          MemLp (fun z => realParticle X i t z-arrayCopy Y i t z) 4 (arrayMeasure π P (Fin N)) ∧
          (∫ z, ‖realParticle X i t z-arrayCopy Y i t z‖^4 ∂arrayMeasure π P (Fin N)) ≤ C/(N : ℝ)^2 := by
  obtain ⟨Y,R,F,hy,hF,hp⟩ := exists_synchronous_family_with_fluctuation π P W hW hm hI ξ hξm hξ T hT σ K hK
  refine ⟨Y,R,synchronousFourthConstant L T F,hy,?_,fun N hN => ?_⟩
  · have hpos := hF.1
    unfold synchronousFourthConstant
    positivity
  · obtain ⟨B,X,hs⟩ := hp N hN
    exact ⟨B,X,hs,synchronous_fourth_rate π P hN W ξ T hT σ R F K hK Y hy hF B X hs⟩

end WMFKIRealizedFluctuation
