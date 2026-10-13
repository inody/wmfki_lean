import WMFKI_Stochastic.MeanFieldPicardAdapted
import WMFKI_Stochastic.MeanFieldBrownianExistence
import WMFKI_Stochastic.RandomInitialParticleProbe

open MeasureTheory ProbabilityTheory Set
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
open WMFKIMeanFieldPicard
open scoped NNReal

namespace WMFKIMeanFieldAdapted
variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- 切り詰めたBrownian駆動は対象区間で元のフィルトレーションに適合する。 -/
theorem compact_brownian_forcing_adapted (B : BrownianSystem P d) (T : ℝ) (hT : 0 ≤ T) (σ : ℝ) :
    AdaptedOn (fun t => B.F (realTimeClamp t)) T (compactBrownianForcing B T hT σ) := by
  obtain ⟨_,_,_,_,_,_,_,_,he⟩ := brownian_forcing_envelope B T hT σ
  intro t ht
  have hb : (realTimeClamp t : HalfClosedTime) < ⊤ := by
    change ((realTimeClamp (T := ⊤) t).val : EReal) < ⊤
    rw [real_time_clamp_eq t ht.1 le_top]
    exact EReal.coe_lt_top t
  have hj (j : Fin d) := (B.martingale j).adapted P B.F (realTimeClamp t) hb
  have hm : Measurable[B.F (realTimeClamp t)] (fun ω =>
      σ • (WithLp.toLp 2 (fun j => B.W j (realTimeClamp t) ω) : EuclideanSpace ℝ (Fin d))) := by
    let : MeasurableSpace Ω := B.F (realTimeClamp t)
    have hp : Measurable (fun ω j => B.W j (realTimeClamp t) ω) := Measurable.of_eval hj
    exact ((WithLp.measurable_toLp 2 (Fin d → ℝ)).comp hp).const_smul σ
  have heq := funext (he t ht)
  rw [heq]
  exact hm

/-- F0可測初期値と実際のBrownian駆動から、適合した平均場解を構成する。 -/
theorem exists_adapted_brownian_mean_field (B : BrownianSystem P d) (T : ℝ) (hT : 0 ≤ T)
    (σ : ℝ) (ξ : Ω → EuclideanSpace ℝ (Fin d)) (hξ0 : Measurable[B.F ⊥] ξ) (hξ : MemLp ξ 4 P)
    {L : ℝ≥0} (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : LipschitzWith L K) :
    ∃ Y : ℝ → Ω → EuclideanSpace ℝ (Fin d), AdaptedOn (fun t => B.F (realTimeClamp t)) T Y ∧
      (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∃ H : Ω → ℝ, Measurable H ∧ MemLp H 4 P ∧ ∀ t ω, ‖Y t ω‖ ≤ H ω) ∧
      (∀ t, MemLp (Y t) 4 P) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t, (∫ ω, ‖Y t ω‖^4 ∂P) ≤ C) ∧
      (∀ ω, Continuous (fun t => ∫ y, K (Y t ω-y) ∂(P.map (Y t)))) ∧
      (∀ᵐ ω ∂P, Y 0 ω = ξ ω ∧ ∀ t ∈ Icc 0 T,
        Y t ω = ξ ω + (∫ s in (0 : ℝ)..t, ∫ y, K (Y s ω-y) ∂(P.map (Y s))) +
          σ • WithLp.toLp 2 (fun j => B.W j (realTimeClamp t) ω)) := by
  obtain ⟨hFm,hFc,hF0,H,hHm,hHL,_,hHb,hFe⟩ := brownian_forcing_envelope B T hT σ
  have hξm : Measurable ξ := hξ0.mono (B.le ⊥) le_rfl
  have hFA := compact_brownian_forcing_adapted B T hT σ
  let Z := fun t ω => ξ ω+compactBrownianForcing B T hT σ t ω
  have hZA : AdaptedOn (fun t => B.F (realTimeClamp t)) T Z := by
    intro t ht
    exact (hξ0.mono (B.mono bot_le) le_rfl).add (hFA t ht)
  have hZc (ω : Ω) : Continuous (fun t => Z t ω) := continuous_const.add (hFc ω)
  let R := fun ω => ‖ξ ω‖+H ω
  have hb : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, ‖Z t ω‖ ≤ R ω :=
    ae_of_all _ (fun ω t _ => (norm_add_le _ _).trans (add_le_add le_rfl (hHb t ω)))
  obtain ⟨Y,hA,hm,hc,hE,hL,hM,hd,he⟩ := exists_adapted_mean_field T hT
    (fun t => B.F (realTimeClamp t)) (fun _ _ hst => B.mono (real_time_clamp_mono hst))
    (fun _ => B.le _) (fun _ => B.null _) Z (fun t => hξm.add (hFm t)) hZA
    (ae_of_all _ (fun ω => (hZc ω).continuousOn)) R (hξm.norm.add hHm) (hξ.norm.add hHL) hb K hK
  refine ⟨Y,hA,hm,hc,hE,hL,hM,hd,?_⟩
  filter_upwards [he,hF0] with ω hω h0
  refine ⟨?_,fun t ht => ?_⟩
  · have h := hω 0 ⟨le_rfl,hT⟩
    simpa only [Z,h0,add_zero,intervalIntegral.integral_same] using h
  · rw [hω t ht]
    dsimp only [Z]
    rw [hFe t ht ω]
    abel

/-- 独立初期値とa.s.連続Brownian族の積モデル上で、フィルトレーションも構成する。
    任意の既存joint realizationへの移送はこの定理の主張ではない。 -/
theorem exists_product_adapted_mean_field
    {I : Type*} [MeasurableSpace I] (π : Measure I) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P]
    (W : Fin d → ℝ≥0 → Ω → ℝ) (hW : ∀ j, IsBrownianReal (W j) P)
    (hm : ∀ j t, Measurable (W j t)) (hI : iIndepFun (fun j ω t => W j t ω) P)
    (ξ : I → EuclideanSpace ℝ (Fin d)) (hξm : Measurable ξ) (hξ : MemLp ξ 4 π)
    (T : ℝ) (hT : 0 ≤ T) (σ : ℝ)
    {L : ℝ≥0} (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : LipschitzWith L K) :
    ∃ (B : BrownianSystem (π.prod P) d) (Y : ℝ → I × Ω → EuclideanSpace ℝ (Fin d)),
      (∀ᵐ z ∂π.prod P, ∀ j t, B.W j t z = W j (halfTimeReal t) z.2) ∧
      AdaptedOn (fun t => B.F (realTimeClamp t)) T Y ∧
      (∀ t, Measurable (Y t)) ∧ (∀ z, Continuous (fun t => Y t z)) ∧
      (∃ H : I × Ω → ℝ, Measurable H ∧ MemLp H 4 (π.prod P) ∧ ∀ t z, ‖Y t z‖ ≤ H z) ∧
      (∀ t, MemLp (Y t) 4 (π.prod P)) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t, (∫ z, ‖Y t z‖^4 ∂π.prod P) ≤ C) ∧
      (∀ᵐ z ∂π.prod P, Y 0 z = ξ z.1 ∧ ∀ t ∈ Icc 0 T,
        Y t z = ξ z.1 + (∫ s in (0 : ℝ)..t, ∫ y, K (Y s z-y) ∂((π.prod P).map (Y s))) +
          σ • WithLp.toLp 2 (fun j => W j (halfTimeReal (realTimeClamp t)) z.2)) := by
  obtain ⟨B,hBW,hfst,_⟩ := WMFKIExternalProbe.exists_initial_brownian_system π P W hW hm hI
  obtain ⟨Y,hA,hYm,hYc,hE,hL,hM,_,he⟩ := exists_adapted_brownian_mean_field B T hT σ
    (fun z => ξ z.1) (hξm.comp (hfst ⊥)) (hξ.comp_measurePreserving measurePreserving_fst) K hK
  refine ⟨B,Y,hBW,hA,hYm,hYc,hE,hL,hM,?_⟩
  filter_upwards [he,hBW] with z hz hw
  refine ⟨hz.1,fun t ht => ?_⟩
  rw [hz.2 t ht]
  congr 2
  apply congrArg (WithLp.toLp 2)
  funext j
  exact hw j (realTimeClamp t)

end WMFKIMeanFieldAdapted
