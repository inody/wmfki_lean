import WMFKI_Stochastic.RecoveryCertificate

open MeasureTheory ProbabilityTheory Set
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
open WMFKIExternalProbe WMFKISynchronousModel WMFKIFeatureCoupling WMFKIPopulationDesign WMFKIObservedDesign
open scoped NNReal
namespace WMFKIJointAssembly

set_option maxHeartbeats 2400000 in
/-- 実際の原始入力から、同じ観測粒子モデル上の既知support OLSとLASSOへ接続する。
    原稿の有界phiを明示する。Laplacian境界はC3から導出し、D0/V0や出力証明書を
    原始仮定として受け取らない。求積・識別幾何・許容誤差・penalty条件は明示的に残す。 -/
theorem exists_particle_weak_recovery {A Ω Ξ : Type*}
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
    (Cφ : ℝ) (hφb : ∀ a x, |φ a x| ≤ Cφ)
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
          CV*(σ^2/(N : ℝ)+e+q) ∧
        RecoveryCertificate ((arrayMeasure π P (Fin N)).prod Pe) N nt nr nc h b w θ
          (populationFeatureDesign (π.prod P) T nr nc ψ φ atom Y)
          (CA*(1/(N : ℝ)+e+q)) (CV*(σ^2/(N : ℝ)+e+q))
          (WMFKI.featureMomentBound B G C (2*Rpos+2*q))
          (WMFKI.featureMomentBound B G (‖K 0‖+(L : ℝ)) (2*Rpos+2*q)) atom K := by
  obtain ⟨Y,R,Rpos,CA,CV,hy,hRpos,hCA,hCV,hFamily⟩ := exists_joint_weak_budgets (Ξ := Ξ) π P W hW hm hI ξ hξm hξ
    T hT σ K hK nr nc hnr ψ φ atom B G H J C hC hφ hψc hψ hdψ hψ0 hψT hAtom hAL θ hReal W0 Q hQ
  have hG : 0 ≤ G := (norm_nonneg (fderiv ℝ (φ ⟨0,hnr⟩) (0 : EuclideanSpace ℝ (Fin d)))).trans ((hφ ⟨0,hnr⟩).first 0)
  have hB : 0 ≤ B := (abs_nonneg (ψ ⟨0,hnr⟩ 0)).trans (hψ ⟨0,hnr⟩ 0 ⟨le_rfl,hT⟩)
  refine ⟨Y,R,Rpos,CA,CV,hy,hRpos,hCA,hCV,fun N hN => ?_⟩
  obtain ⟨BN,X,hs,hpos,hBudgets⟩ := hFamily N hN
  refine ⟨BN,X,hs,hpos,?_⟩
  intro nt w τ hw hτ Pe hPe q hq ε hεm hεl hεq e he hqa hQa hqb hQb
  let := hPe
  have hb := hBudgets nt w τ hw hτ Pe q hq ε hεm hεl hεq e he hqa hQa hqb hQb
  have hxm t i : Measurable (particleGrid N d nt τ X t i) :=
    (particle_real_jointly_measurable (arrayMeasure π P (Fin N)) BN K σ _ X hs.solution i).measurable.comp
      (measurable_const.prodMk measurable_id)
  let O := independentObservationSamples (arrayMeasure π P (Fin N)) Pe N nt Rpos q (particleGrid N d nt τ X) ε
    hxm hεm (fun t i => (hpos i (τ t) (hτ t)).1) hεl (fun t i => (hpos i (τ t) (hτ t)).2) hεq
  have hr := recover_genuine_assembly ((arrayMeasure π P (Fin N)).prod Pe) N nt d nr nc hnr Rpos q hRpos hq O
    σ w τ ψ φ atom B G H J C Cφ hB hG hC hφ hφb (fun a t => hψ a (τ t) (hτ t))
    (fun m => (hAL m).continuous) hAtom K hK.continuous (‖K 0‖+(L : ℝ)) (by positivity)
    (WMFKIIndependentFourth.lipschitz_growth_with_origin d hK) θ hReal
    (populationFeatureDesign (π.prod P) T nr nc ψ φ atom Y)
    (CA*(1/(N : ℝ)+e+q)) (CV*(σ^2/(N : ℝ)+e+q)) hb.1.2 hb.2.2
  exact ⟨hb.1,hb.2.1,hb.2.2,hr⟩

end WMFKIJointAssembly
