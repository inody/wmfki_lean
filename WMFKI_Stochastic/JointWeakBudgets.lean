import WMFKI_Stochastic.IndependentResidualFromPosition

open MeasureTheory ProbabilityTheory Set
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
open WMFKIExternalProbe WMFKISynchronousModel WMFKIFeatureCoupling WMFKIPopulationDesign WMFKIObservedDesign
open scoped NNReal
namespace WMFKIJointAssembly
-- 標準CLM構造のキャッシュ。新しいノルムや正則性仮定ではない。
private noncomputable local instance (d : ℕ) : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := inferInstance
private noncomputable local instance (d : ℕ) : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := inferInstance
private noncomputable local instance (d : ℕ) : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := inferInstance
private noncomputable local instance (d : ℕ) : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := inferInstance

theorem three_budget_absorption (a b c x y z : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    a*x+b*y+c*z ≤ (a+b+c)*(x+y+z) := by
  have h1 := mul_le_mul_of_nonneg_left (show x ≤ x+y+z by linarith) ha
  have h2 := mul_le_mul_of_nonneg_left (show y ≤ x+y+z by linarith) hb
  have h3 := mul_le_mul_of_nonneg_left (show z ≤ x+y+z by linarith) hc
  nlinarith

set_option maxHeartbeats 2400000 in
/-- 原始入力から同じX、同じ観測、同じ母集団設計に対するD0とV0を同時構成。
    両RMS求積仮定以外の予算を原始仮定にしない。 -/
theorem exists_joint_weak_budgets {A Ω Ξ : Type*}
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
    (hφ : ∀ a, C3TestBounds d (φ a) G H J) (hψc : ∀ a, ContDiff ℝ 1 (ψ a))
    (hψ : ∀ a t, t ∈ Icc 0 T → |ψ a t| ≤ B)
    (hdψ : ∀ a t, t ∈ Icc 0 T → |deriv (ψ a) t| ≤ B)
    (hψ0 : ∀ a, ψ a 0 = 0) (hψT : ∀ a, ψ a T = 0)
    (hAtom : ∀ m x, ‖atom m x‖ ≤ C*(1+‖x‖)) (hAL : ∀ m, LipschitzWith D (atom m))
    (θ : EuclideanSpace ℝ (Fin nc)) (hReal : ∀ x, ∑ m, θ m • atom m x = K x)
    (W0 Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d)) (R Rpos CA CV : ℝ),
      ArrayNonlinearFamily π P T K ξ
        (fun t z => σ • WithLp.toLp 2 (fun j => W j (halfTimeReal (realTimeClamp t)) z.2)) Y R ∧
      0 ≤ Rpos ∧ 0 ≤ CA ∧ 0 ≤ CV ∧ ∀ N : ℕ, 0 < N →
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
        MemLp (fun z => discreteResponseVector nr N nt d σ w τ φ ψ (particleGrid N d nt τ X) z-
          continuousResponseVector nr N d σ φ ψ T X z) 2 (arrayMeasure π P (Fin N)) →
        (∫ z, ‖discreteResponseVector nr N nt d σ w τ φ ψ (particleGrid N d nt τ X) z-
          continuousResponseVector nr N d σ φ ψ T X z‖^2 ∂arrayMeasure π P (Fin N)) ≤ Q*e →
        let Obs := fun z i t => particleGrid N d nt τ X t i z.1+ε t i z.2
        let h := WMFKI.observedPairFeature Obs (fun a t => ψ a (τ t)) (fun a => gradient (φ a)) atom
        let b := WMFKI.observedWeakResponse Obs φ (fun a => Laplacian.laplacian (φ a))
          (fun a t => ψ a (τ t)) (fun a t => deriv (ψ a) (τ t)) w σ
        let E := fun z => WMFKI.fullPairDesign h w z-populationFeatureDesign (π.prod P) T nr nc ψ φ atom Y
        (MemLp (fun z => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => E z am.1 am.2) :
          EuclideanSpace ℝ (Fin nr × Fin nc))) 2 ((arrayMeasure π P (Fin N)).prod Pe) ∧
        (∫ z, WMFKI.frobenius (E z)^2 ∂(arrayMeasure π P (Fin N)).prod Pe) ≤ CA*(1/(N : ℝ)+e+q)) ∧
        MemLp (WMFKI.fullRegressionResidual h w b θ) 2 ((arrayMeasure π P (Fin N)).prod Pe) ∧
        (∫ z, ‖WMFKI.fullRegressionResidual h w b θ z‖^2 ∂(arrayMeasure π P (Fin N)).prod Pe) ≤
          CV*(σ^2/(N : ℝ)+e+q) := by
  obtain ⟨Y,R,Rpos,CA,hy,hRpos,hCA,hFamily⟩ := exists_observed_full_design_rate (Ξ := Ξ) π P W hW hm hI ξ hξm hξ
    T hT σ K hK nr nc hnr ψ φ atom B G H J C hC hφ (fun a => (hψc a).continuous.measurable)
    hψ hAtom hAL W0 Q hQ
  let KT := ‖K 0‖+(L : ℝ)
  have hKT : 0 ≤ KT := by dsimp [KT];positivity
  let Cb := responseObservationConstant d σ W0 B G J
  let Ck := kernelObservationConstant W0 B G H KT L Rpos
  have hCb : 0 ≤ Cb := by dsimp [Cb,responseObservationConstant];positivity
  have hCk : 0 ≤ Ck := by dsimp [Ck,kernelObservationConstant];positivity
  have hG : 0 ≤ G := (norm_nonneg (fderiv ℝ (φ ⟨0,hnr⟩) (0 : EuclideanSpace ℝ (Fin d)))).trans ((hφ ⟨0,hnr⟩).first 0)
  have hH : 0 ≤ H := (norm_nonneg (fderiv ℝ (fderiv ℝ (φ ⟨0,hnr⟩)) (0 : EuclideanSpace ℝ (Fin d)))).trans ((hφ ⟨0,hnr⟩).second 0)
  have hJ : 0 ≤ J := (norm_nonneg (fderiv ℝ (fderiv ℝ (fderiv ℝ (φ ⟨0,hnr⟩))) (0 : EuclideanSpace ℝ (Fin d)))).trans ((hφ ⟨0,hnr⟩).third 0)
  have hB : 0 ≤ B := (abs_nonneg (ψ ⟨0,hnr⟩ 0)).trans (hψ ⟨0,hnr⟩ 0 ⟨le_rfl,hT⟩)
  have hΓ := averaged_time_energy_bound nr hnr G B T hB hT ψ (fun a => (hψc a).continuous) hψ
  refine ⟨Y,R,Rpos,CA,6*G^2*T*B^2+12*Q*(1+‖θ‖^2)+3*(Cb+Ck),hy,hRpos,hCA,by positivity,fun N hN => ?_⟩
  obtain ⟨BN,X,hs,hpos,hObs⟩ := hFamily N hN
  refine ⟨BN,X,hs,hpos,?_⟩
  intro nt w τ hw hτ Pe hPe q hq ε hεm hεl hεq e he hqa hQa hqb hQb
  let := hPe
  have hD0 := hObs nt w τ hw hτ Pe q hq ε hεm hεl hεq e he hqa hQa
  have hV0 := independent_residual_from_position (arrayMeasure π P (Fin N)) Pe nr N nt d nc hnr hN q hq
    ε hεm hεl hεq σ w τ W0 hw K hK.continuous atom (fun m => (hAL m).continuous) θ hReal φ ψ hψc
    G H J KT L B hG hH hJ hKT L.coe_nonneg hφ (fun a t => hψ a (τ t) (hτ t))
    (fun a t => hdψ a (τ t) (hτ t)) (WMFKIIndependentFourth.lipschitz_growth_with_origin d hK)
    (fun x y => hK.norm_sub_le x y) T hT hτ hψ0 hψT BN _ X hs.solution Rpos hRpos
    (fun t i => (hpos i (τ t) (hτ t)).1) (fun t i => (hpos i (τ t) (hτ t)).2)
    Q e hqb hQb hqa hQa
  dsimp only at hV0 hD0 ⊢
  simp_rw [full_residual_bridge] at hV0
  refine ⟨hD0,hV0.1,hV0.2.trans ?_⟩
  have hΓs := mul_le_mul_of_nonneg_left hΓ.2 (show 0 ≤ 6*(σ^2/(N : ℝ)) by positivity)
  calc
    _ ≤ (6*G^2*T*B^2)*(σ^2/(N : ℝ))+(12*Q*(1+‖θ‖^2))*e+(3*(Cb+Ck))*q := by
      dsimp only [Cb,Ck] at *
      nlinarith
    _ ≤ _ := three_budget_absorption (6*G^2*T*B^2) (12*Q*(1+‖θ‖^2)) (3*(Cb+Ck)) (σ^2/(N : ℝ)) e q
      (by positivity) (by positivity) (by positivity) (by positivity) he hq

end WMFKIJointAssembly
