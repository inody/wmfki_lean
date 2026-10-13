import WMFKI_Stochastic.ContinuousFeatureDesign

open MeasureTheory ProbabilityTheory Set
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
open WMFKIExternalProbe WMFKISynchronousModel WMFKIRealizedFluctuation
open scoped NNReal
namespace WMFKIFeatureCoupling
variable {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω] {d : ℕ}

/-- 設計を構成する前に、粒子位置自身のL2をコピーと同期差から得る。 -/
theorem coupled_position_second {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) [IsProbabilityMeasure P] (x y : Ω → E)
    (hy : MemLp y 4 P) (he : MemLp (fun ω => x ω-y ω) 4 P)
    (R q : ℝ) (hR : 0 ≤ R) (hq : 0 ≤ q)
    (hyR : (∫ ω, ‖y ω‖^4 ∂P) ≤ R) (heq : (∫ ω, ‖x ω-y ω‖^4 ∂P) ≤ q) :
    MemLp x 2 P ∧ (∫ ω, ‖x ω‖^2 ∂P) ≤ 2*(Real.sqrt R+Real.sqrt q) := by
  obtain ⟨hy2,hyB⟩ := fourth_to_second P y hy R hR hyR
  obtain ⟨he2,heB⟩ := fourth_to_second P (fun ω => x ω-y ω) he q hq heq
  have h := two_vector_l2_moment P y (fun ω => x ω-y ω) hy2 he2 (Real.sqrt R) (Real.sqrt q) hyB heB
  have heq' : (fun ω => y ω+(x ω-y ω)) = x := by funext ω;abel
  have heq'' (ω : Ω) : y ω+(x ω-y ω) = x ω := by abel
  simpa only [heq',heq''] using h

set_option maxHeartbeats 1400000 in
/-- 原始入力から、実際の粒子設計とiidコピー設計のFrobenius誤差O(M/N)を構成。
    これは参照母集団設計へのP2評価やD0全体の代わりではない。 -/
theorem exists_continuous_design_coupling (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P]
    (W : Fin d → ℝ≥0 → Ω → ℝ) (hW : ∀ j, IsBrownianReal (W j) P)
    (hm : ∀ j t, Measurable (W j t)) (hI : iIndepFun (fun j ω t => W j t ω) P)
    (ξ : A → EuclideanSpace ℝ (Fin d)) (hξm : Measurable ξ) (hξ : MemLp ξ 4 π)
    (T : ℝ) (hT : 0 ≤ T) (σ : ℝ) {L : ℝ≥0}
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : LipschitzWith L K)
    (nr nc : ℕ) (hnr : 0 < nr)
    (ψ : Fin nr → ℝ → ℝ) (φ : Fin nr → EuclideanSpace ℝ (Fin d) → ℝ)
    (atom : Fin nc → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (B G H J C : ℝ) (hC : 0 ≤ C) {D : ℝ≥0}
    (hφ : ∀ a, C3TestBounds d (φ a) G H J) (hψm : ∀ a, Measurable (ψ a))
    (hψ : ∀ a t, t ∈ Icc 0 T → |ψ a t| ≤ B)
    (hAtom : ∀ m x, ‖atom m x‖ ≤ C*(1+‖x‖)) (hAL : ∀ m, LipschitzWith D (atom m)) :
    ∃ (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d)) (R S F : ℝ),
      ArrayNonlinearFamily π P T K ξ
        (fun t z => σ • WithLp.toLp 2 (fun j => W j (halfTimeReal (realTimeClamp t)) z.2)) Y R ∧
      0 ≤ S ∧ 0 ≤ F ∧ ∀ N : ℕ, 0 < N →
      ∃ (BN : BrownianSystem (arrayMeasure π P (Fin N)) (N*d))
        (X : HalfClosedTime → (Fin N → A) × (Fin N → Ω) → Fin (N*d) → ℝ),
        SynchronousParticlePair π P W ξ T σ K Y BN X ∧
        (∀ i : Fin N, ∀ t ∈ Icc 0 T,
          MemLp (fun z => realParticle X i t z-arrayCopy Y i t z) 4 (arrayMeasure π P (Fin N)) ∧
          (∫ z, ‖realParticle X i t z-arrayCopy Y i t z‖^4 ∂arrayMeasure π P (Fin N)) ≤ S/(N : ℝ)^2) ∧
        let A := fun z => continuousFeatureDesign N nr nc T ψ φ atom (realParticle X) z-
          continuousFeatureDesign N nr nc T ψ φ atom (arrayCopy Y) z
        MemLp (fun z => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => A z am.1 am.2) :
          EuclideanSpace ℝ (Fin nr × Fin nc))) 2 (arrayMeasure π P (Fin N)) ∧
        (∫ z, WMFKI.frobenius (A z)^2 ∂arrayMeasure π P (Fin N)) ≤ (nc : ℝ)*T^2*F/(N : ℝ) := by
  obtain ⟨Y,R,S,F,hy,hS,hF,hFamily⟩ := exists_feature_coupled_family π P W hW hm hI ξ hξm hξ
    T hT σ K hK nr nc ψ φ atom B G H J C hC hφ hψm hψ hAtom hAL
  refine ⟨Y,R,S,F,hy,hS,hF,fun N hN => ?_⟩
  obtain ⟨BN,X,hs,hr,hGap⟩ := hFamily N hN
  refine ⟨BN,X,hs,hr,?_⟩
  apply continuous_design_coupling (arrayMeasure π P (Fin N)) N nr nc hN hnr T hT ψ φ atom
    B G H J C (2*(Real.sqrt R+Real.sqrt (S/(N : ℝ)^2))) (Real.sqrt R) F hC (by positivity)
    (Real.sqrt_nonneg _) hF hφ hψm hψ hAtom hAL (realParticle X) (arrayCopy Y)
    (fun i => particle_real_jointly_measurable _ BN K σ _ X hs.solution i) (hy.joint N)
  · intro t ht i
    exact coupled_position_second _ (realParticle X i t) (arrayCopy Y i t)
      (hy.fourth N i t ht).1 (hr i t ht).1 R (S/(N : ℝ)^2) hy.nonneg (by positivity)
      (hy.fourth N i t ht).2 (hr i t ht).2
  · intro t ht i
    exact fourth_to_second _ (arrayCopy Y i t) (hy.fourth N i t ht).1 R hy.nonneg (hy.fourth N i t ht).2
  · intro a m i j t ht
    exact (hGap a m i j).2 t ht

end WMFKIFeatureCoupling
