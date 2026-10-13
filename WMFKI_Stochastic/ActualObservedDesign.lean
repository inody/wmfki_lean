import WMFKI_Stochastic.IndependentObservedDesign

open MeasureTheory ProbabilityTheory Set
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
open WMFKIExternalProbe WMFKISynchronousModel WMFKIFeatureCoupling WMFKIPopulationDesign
open scoped NNReal
namespace WMFKIObservedDesign

set_option maxHeartbeats 2000000 in
/-- 原始入力から、本番fullPairDesignと実際の母集団設計とのD0を構成する。
    RMS求積仮定は構成済みの同じXについて供給される。定数は全Nと雑音族より先に選ぶ。 -/
theorem exists_observed_full_design_rate {A Ω Ξ : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω] [MeasurableSpace Ξ] {d : ℕ}
    (π : Measure A) (P : Measure Ω) [IsProbabilityMeasure π] [IsProbabilityMeasure P]
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
    (hAtom : ∀ m x, ‖atom m x‖ ≤ C*(1+‖x‖)) (hAL : ∀ m, LipschitzWith D (atom m))
    (W0 Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d)) (R Rpos CA : ℝ),
      ArrayNonlinearFamily π P T K ξ
        (fun t z => σ • WithLp.toLp 2 (fun j => W j (halfTimeReal (realTimeClamp t)) z.2)) Y R ∧
      0 ≤ Rpos ∧ 0 ≤ CA ∧ ∀ N : ℕ, 0 < N →
      ∃ (BN : BrownianSystem (arrayMeasure π P (Fin N)) (N*d))
        (X : HalfClosedTime → (Fin N → A) × (Fin N → Ω) → Fin (N*d) → ℝ),
        SynchronousParticlePair π P W ξ T σ K Y BN X ∧
        (∀ i : Fin N, ∀ t ∈ Icc 0 T, MemLp (realParticle X i t) 2 (arrayMeasure π P (Fin N)) ∧
          (∫ z, ‖realParticle X i t z‖^2 ∂arrayMeasure π P (Fin N)) ≤ Rpos) ∧
        ∀ (nt : ℕ) (w τ : Fin nt → ℝ), (∑ t,|w t|) ≤ W0 → (∀ t, τ t ∈ Icc 0 T) →
        ∀ (Pe : Measure Ξ) [IsProbabilityMeasure Pe] (q : ℝ), 0 ≤ q →
        ∀ (ε : Fin nt → Fin N → Ξ → EuclideanSpace ℝ (Fin d)),
        (∀ t i, Measurable (ε t i)) → (∀ t i, MemLp (ε t i) 2 Pe) →
        (∀ t i, (∫ z, ‖ε t i z‖^2 ∂Pe) ≤ q) → ∀ (e : ℝ), 0 ≤ e →
        MemLp (fun z => (WithLp.toLp 2 (fun am : Fin nr × Fin nc =>
          (discreteDictionaryDesign nr N nt d nc w τ atom φ ψ (particleGrid N d nt τ X) z-
            continuousDictionaryDesign nr N d nc atom φ ψ T X z) am.1 am.2) :
              EuclideanSpace ℝ (Fin nr × Fin nc))) 2 (arrayMeasure π P (Fin N)) →
        (∫ z, WMFKI.frobenius (discreteDictionaryDesign nr N nt d nc w τ atom φ ψ (particleGrid N d nt τ X) z-
          continuousDictionaryDesign nr N d nc atom φ ψ T X z)^2 ∂arrayMeasure π P (Fin N)) ≤ Q*e →
        let Obs := fun z i t => particleGrid N d nt τ X t i z.1+ε t i z.2
        let E := fun z => WMFKI.fullPairDesign (WMFKI.observedPairFeature Obs
          (fun a t => ψ a (τ t)) (fun a => gradient (φ a)) atom) w z-
          populationFeatureDesign (π.prod P) T nr nc ψ φ atom Y
        MemLp (fun z => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => E z am.1 am.2) :
          EuclideanSpace ℝ (Fin nr × Fin nc))) 2 ((arrayMeasure π P (Fin N)).prod Pe) ∧
        (∫ z, WMFKI.frobenius (E z)^2 ∂(arrayMeasure π P (Fin N)).prod Pe) ≤ CA*(1/(N : ℝ)+e+q) := by
  obtain ⟨Y,R,S,Cpop,hy,hS,hCpop,hRate⟩ := exists_continuous_population_rate π P W hW hm hI ξ hξm hξ
    T hT σ K hK nr nc hnr ψ φ atom B G H J C hC hφ hψm hψ hAtom hAL
  let Rpos := 2*(Real.sqrt R+Real.sqrt S)
  have hRpos : 0 ≤ Rpos := by dsimp [Rpos];positivity
  let Cobs := kernelObservationConstant W0 B G H C D Rpos
  have hCobs : 0 ≤ Cobs := by dsimp [Cobs,kernelObservationConstant];positivity
  have hG : 0 ≤ G := (norm_nonneg (fderiv ℝ (φ ⟨0,hnr⟩) (0 : EuclideanSpace ℝ (Fin d)))).trans ((hφ ⟨0,hnr⟩).first 0)
  have hH : 0 ≤ H := (norm_nonneg (fderiv ℝ (fderiv ℝ (φ ⟨0,hnr⟩)) (0 : EuclideanSpace ℝ (Fin d)))).trans ((hφ ⟨0,hnr⟩).second 0)
  refine ⟨Y,R,Rpos,3*((nc : ℝ)*Cobs+Q+(nc : ℝ)*Cpop),hy,hRpos,by positivity,fun N hN => ?_⟩
  obtain ⟨BN,X,hs,hr,hcont⟩ := hRate N hN
  have hpos i t ht : MemLp (realParticle X i t) 2 (arrayMeasure π P (Fin N)) ∧
      (∫ z, ‖realParticle X i t z‖^2 ∂arrayMeasure π P (Fin N)) ≤ Rpos :=
    coupled_uniform_position_second (arrayMeasure π P (Fin N)) N hN (realParticle X i t) (arrayCopy Y i t)
      (hy.fourth N i t ht).1 (hr i t ht).1 R S hy.nonneg hS (hy.fourth N i t ht).2 (hr i t ht).2
  refine ⟨BN,X,hs,hpos,?_⟩
  intro nt w τ hw hτ Pe hPe q hq ε hεm hεl hεq e he hql hqQ
  let := hPe
  have hxm t i : Measurable (particleGrid N d nt τ X t i) :=
    (particle_real_jointly_measurable (arrayMeasure π P (Fin N)) BN K σ _ X hs.solution i).measurable.comp
      (measurable_const.prodMk measurable_id)
  dsimp only at hcont
  simp_rw [continuous_design_bridge] at hcont
  have hb := independent_observed_design_budget (arrayMeasure π P (Fin N)) Pe N nt d nr nc hN hnr
    Rpos q hRpos hq w τ W0 hw ψ φ atom G H J C D B hG hH hC D.coe_nonneg hφ
    (fun a t => hψ a (τ t) (hτ t)) (fun m => (hAL m).continuous.measurable) hAtom
    (fun m x y => by simpa only [dist_eq_norm] using (hAL m).dist_le_mul x y)
    T X hxm (fun t i => (hpos i (τ t) (hτ t)).1) (fun t i => (hpos i (τ t) (hτ t)).2)
    ε hεm hεl hεq (populationFeatureDesign (π.prod P) T nr nc ψ φ atom Y)
    ((nc : ℝ)*Cpop/(N : ℝ)) Q e hcont.1 hcont.2 hql hqQ
  dsimp only at hb ⊢
  simp_rw [discrete_design_bridge] at hb
  refine ⟨hb.1,hb.2.trans ?_⟩
  exact design_budget_common_constant N ((nc : ℝ)*Cobs) Q ((nc : ℝ)*Cpop) e q
    (by positivity) hQ (by positivity) he hq

end WMFKIObservedDesign
