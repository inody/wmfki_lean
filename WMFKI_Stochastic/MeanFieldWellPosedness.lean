import WMFKI_Stochastic.MeanFieldFiniteUniqueness
import WMFKI_Stochastic.MeanFieldBrownianAdapted

open MeasureTheory ProbabilityTheory Set
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
open scoped NNReal

namespace WMFKIMeanFieldAdapted
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- 実際の母集団法則積分と同じ初期値・駆動に対する一意性。 -/
theorem additive_mean_field_unique {T : ℝ} (hT : 0 ≤ T) {L : ℝ≥0} {K : E → E}
    (hK : LipschitzWith L K) (ξ : Ω → E) (D : ℝ → Ω → E) (X Y : ℝ → Ω → E)
    (hX : FiniteL4Paths P T X) (hY : FiniteL4Paths P T Y)
    (heX : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, X t ω = ξ ω +
      (∫ s in (0 : ℝ)..t, ∫ y, K (X s ω-y) ∂(P.map (X s))) + D t ω)
    (heY : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, Y t ω = ξ ω +
      (∫ s in (0 : ℝ)..t, ∫ y, K (Y s ω-y) ∂(P.map (Y s))) + D t ω) :
    ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, X t ω = Y t ω := by
  let Z := fun t ω => ξ ω+D t ω
  have hx : MeanFieldEquation P K T Z X := by
    apply mean_field_equation_of_law_integral hK hX.measurable
    filter_upwards [heX] with ω hω t ht
    rw [hω t ht]
    dsimp only [Z]
    abel
  have hy : MeanFieldEquation P K T Z Y := by
    apply mean_field_equation_of_law_integral hK hY.measurable
    filter_upwards [heY] with ω hω t ht
    rw [hω t ht]
    dsimp only [Z]
    abel
  exact finite_l4_mean_field_unique hT hK hX hY hx hy

/-- 固定BrownianSystem上の適合した解を構成し、有限L4経路包絡クラスで一意性を供給。 -/
theorem exists_unique_adapted_brownian_mean_field {d : ℕ} (B : BrownianSystem P d)
    (T : ℝ) (hT : 0 ≤ T) (σ : ℝ) (ξ : Ω → EuclideanSpace ℝ (Fin d))
    (hξ0 : Measurable[B.F ⊥] ξ) (hξ : MemLp ξ 4 P)
    {L : ℝ≥0} (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : LipschitzWith L K) :
    ∃ Y : ℝ → Ω → EuclideanSpace ℝ (Fin d),
      AdaptedOn (fun t => B.F (realTimeClamp t)) T Y ∧ FiniteL4Paths P T Y ∧
      (∀ᵐ ω ∂P, Y 0 ω = ξ ω ∧ ∀ t ∈ Icc 0 T,
        Y t ω = ξ ω + (∫ s in (0 : ℝ)..t, ∫ y, K (Y s ω-y) ∂(P.map (Y s))) +
          σ • WithLp.toLp 2 (fun j => B.W j (realTimeClamp t) ω)) ∧
      (∀ X : ℝ → Ω → EuclideanSpace ℝ (Fin d), FiniteL4Paths P T X →
        (∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, X t ω = ξ ω +
          (∫ s in (0 : ℝ)..t, ∫ y, K (X s ω-y) ∂(P.map (X s))) +
            σ • WithLp.toLp 2 (fun j => B.W j (realTimeClamp t) ω)) →
        ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, X t ω = Y t ω) := by
  obtain ⟨Y,hA,hm,hc,hE,_,_,_,he⟩ := exists_adapted_brownian_mean_field B T hT σ ξ hξ0 hξ K hK
  have hY := finite_l4_paths_of_global_envelope (T := T) hm hc hE
  refine ⟨Y,hA,hY,he,fun X hX hx => ?_⟩
  exact additive_mean_field_unique hT hK ξ
    (fun t ω => σ • WithLp.toLp 2 (fun j => B.W j (realTimeClamp t) ω))
    X Y hX hY hx (he.mono (fun _ hω => hω.2))

set_option maxHeartbeats 600000 in
/-- 原始入力からの積モデル終点。解の経路包絡・適合性・一意性は結論である。 -/
theorem exists_unique_product_adapted_mean_field
    {I : Type*} [MeasurableSpace I] (π : Measure I) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P] {d : ℕ}
    (W : Fin d → ℝ≥0 → Ω → ℝ) (hW : ∀ j, IsBrownianReal (W j) P)
    (hm : ∀ j t, Measurable (W j t)) (hI : iIndepFun (fun j ω t => W j t ω) P)
    (ξ : I → EuclideanSpace ℝ (Fin d)) (hξm : Measurable ξ) (hξ : MemLp ξ 4 π)
    (T : ℝ) (hT : 0 ≤ T) (σ : ℝ)
    {L : ℝ≥0} (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : LipschitzWith L K) :
    ∃ (B : BrownianSystem (π.prod P) d) (Y : ℝ → I × Ω → EuclideanSpace ℝ (Fin d)),
      (∀ᵐ z ∂π.prod P, ∀ j t, B.W j t z = W j (halfTimeReal t) z.2) ∧
      AdaptedOn (fun t => B.F (realTimeClamp t)) T Y ∧ FiniteL4Paths (π.prod P) T Y ∧
      (∀ᵐ z ∂π.prod P, Y 0 z = ξ z.1 ∧ ∀ t ∈ Icc 0 T,
        Y t z = ξ z.1 + (∫ s in (0 : ℝ)..t, ∫ y, K (Y s z-y) ∂((π.prod P).map (Y s))) +
          σ • WithLp.toLp 2 (fun j => W j (halfTimeReal (realTimeClamp t)) z.2)) ∧
      (∀ X : ℝ → I × Ω → EuclideanSpace ℝ (Fin d), FiniteL4Paths (π.prod P) T X →
        (∀ᵐ z ∂π.prod P, ∀ t ∈ Icc 0 T, X t z = ξ z.1 +
          (∫ s in (0 : ℝ)..t, ∫ y, K (X s z-y) ∂((π.prod P).map (X s))) +
            σ • WithLp.toLp 2 (fun j => W j (halfTimeReal (realTimeClamp t)) z.2)) →
        ∀ᵐ z ∂π.prod P, ∀ t ∈ Icc 0 T, X t z = Y t z) := by
  obtain ⟨B,Y,hBW,hA,hmY,hc,hE,_,_,he⟩ := exists_product_adapted_mean_field π P W hW hm hI
    ξ hξm hξ T hT σ K hK
  have hY := finite_l4_paths_of_global_envelope (T := T) hmY hc hE
  refine ⟨B,Y,hBW,hA,hY,he,fun X hX hx => ?_⟩
  exact additive_mean_field_unique hT hK (fun z => ξ z.1)
    (fun t z => σ • WithLp.toLp 2 (fun j => W j (halfTimeReal (realTimeClamp t)) z.2))
    X Y hX hY hx
    (he.mono (fun _ hz => hz.2))

end WMFKIMeanFieldAdapted
