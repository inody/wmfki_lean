import WMFKI_Stochastic.MatrixErrorComposition

open MeasureTheory ProbabilityTheory Set
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
open WMFKIExternalProbe WMFKISynchronousModel WMFKIRealizedFluctuation WMFKIFeatureCoupling
open scoped NNReal
namespace WMFKIPopulationDesign
variable {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω] {d : ℕ}

set_option maxHeartbeats 1600000 in
/-- 原始入力から、実際の粒子設計対mu_t×mu_t母集団設計の連続時間率を構成。
    同期コピーはF1とP2で同一。全定数をNより先に選ぶ。 -/
theorem exists_continuous_population_rate (π : Measure A) (P : Measure Ω)
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
    ∃ (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d)) (R S Cpop : ℝ),
      ArrayNonlinearFamily π P T K ξ
        (fun t z => σ • WithLp.toLp 2 (fun j => W j (halfTimeReal (realTimeClamp t)) z.2)) Y R ∧
      0 ≤ S ∧ 0 ≤ Cpop ∧ ∀ N : ℕ, 0 < N →
      ∃ (BN : BrownianSystem (arrayMeasure π P (Fin N)) (N*d))
        (X : HalfClosedTime → (Fin N → A) × (Fin N → Ω) → Fin (N*d) → ℝ),
        SynchronousParticlePair π P W ξ T σ K Y BN X ∧
        (∀ i : Fin N, ∀ t ∈ Icc 0 T,
          MemLp (fun z => realParticle X i t z-arrayCopy Y i t z) 4 (arrayMeasure π P (Fin N)) ∧
          (∫ z, ‖realParticle X i t z-arrayCopy Y i t z‖^4 ∂arrayMeasure π P (Fin N)) ≤ S/(N : ℝ)^2) ∧
        let A := fun z => continuousFeatureDesign N nr nc T ψ φ atom (realParticle X) z-
          populationFeatureDesign (π.prod P) T nr nc ψ φ atom Y
        MemLp (fun z => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => A z am.1 am.2) :
          EuclideanSpace ℝ (Fin nr × Fin nc))) 2 (arrayMeasure π P (Fin N)) ∧
        (∫ z, WMFKI.frobenius (A z)^2 ∂arrayMeasure π P (Fin N)) ≤ (nc : ℝ)*Cpop/(N : ℝ) := by
  obtain ⟨Y,R,S,F,hy,hS,hF,hFamily⟩ := exists_continuous_design_coupling π P W hW hm hI ξ hξm hξ
    T hT σ K hK nr nc hnr ψ φ atom B G H J C hC hφ hψm hψ hAtom hAL
  obtain ⟨R0,hR0,hM⟩ := hy.base_paths.uniform_fourth
  let V := featureSecondConstant B G C (Real.sqrt R0)
  have hV : 0 ≤ V := feature_second_constant_nonneg _ _ _ _ (Real.sqrt_nonneg _)
  have hmY := base_jointly_measurable hy
  have hY t ht : MemLp (Y t) 2 (π.prod P) ∧ (∫ z, ‖Y t z‖^2 ∂π.prod P) ≤ Real.sqrt R0 :=
    fourth_to_second (π.prod P) (Y t) (hy.base_paths.memLp t ht) R0 hR0 (hM t ht)
  refine ⟨Y,R,S,2*T^2*(F+5*V),hy,hS,by positivity,fun N hN => ?_⟩
  obtain ⟨BN,X,hs,hr,hCoupling⟩ := hFamily N hN
  have hIID := iid_time_design_rate π P N nr nc hN hnr T hT ψ φ atom Y B G H J C (Real.sqrt R0)
    hC (Real.sqrt_nonneg _) hφ hψm hψ hAtom hAL hmY hY
  obtain ⟨hl,hb⟩ := matrix_error_composition (arrayMeasure π P (Fin N)) nr nc
    (continuousFeatureDesign N nr nc T ψ φ atom (realParticle X))
    (continuousFeatureDesign N nr nc T ψ φ atom (arrayCopy Y))
    (fun _ => populationFeatureDesign (π.prod P) T nr nc ψ φ atom Y)
    hCoupling.1 hIID.1 _ _ hCoupling.2 hIID.2
  refine ⟨BN,X,hs,hr,hl,hb.trans_eq ?_⟩
  dsimp only [V]
  ring

end WMFKIPopulationDesign
