import WMFKI_Stochastic.WeakFeatureCoupling

open MeasureTheory ProbabilityTheory Set
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
open WMFKIExternalProbe WMFKISynchronousModel WMFKIRealizedFluctuation
open scoped NNReal
namespace WMFKIFeatureCoupling
variable {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω] {N d : ℕ}

theorem particle_real_jointly_measurable (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P (N*d)) (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (σ : ℝ) (ξ : Ω → Fin (N*d) → ℝ) (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hX : VectorSDESolution P B.F B.W (particleCoordinateDrift N d K)
      (fun i j _ => if i = j then σ else 0) ξ X) (i : Fin N) :
    StronglyMeasurable (fun z : ℝ × Ω => realParticle X i z.1 z.2) := by
  have hf (r : ℝ) : (realTimeClamp r : HalfClosedTime) < ⊤ := by
    apply (real_time_clamp_mono (le_max_left r 0)).trans_lt
    exact real_time_below (max r 0) (le_max_right r 0) (EReal.coe_lt_top _)
  apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (fun ω => particle_real_paths P B K σ ξ X hX ω i)
  intro t
  exact ((continuous_particlePositions N d i).measurable.comp
    ((hX.adapted _ (hf t)).mono (B.le _) le_rfl)).stronglyMeasurable

theorem weak_pair_feature_jointly_measurable
    (ψ : ℝ → ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hψ : Measurable ψ) {G H J : ℝ} (hφ : C3TestBounds d φ G H J) {D : ℝ≥0}
    (hK : LipschitzWith D K) (U V : ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hU : StronglyMeasurable (fun z : ℝ × Ω => U z.1 z.2))
    (hV : StronglyMeasurable (fun z : ℝ × Ω => V z.1 z.2)) :
    StronglyMeasurable (fun z : ℝ × Ω => weakPairFeature ψ φ K z.1 (U z.1 z.2) (V z.1 z.2)) := by
  exact ((hψ.comp measurable_fst).mul (((gradient_measurable_of_c3 hφ).comp hU.measurable).inner
    (hK.continuous.measurable.comp (hU.measurable.sub hV.measurable)))).stronglyMeasurable

noncomputable def featureGap (ψ : ℝ → ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (atom : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d))
    (X : HalfClosedTime → (Fin N → A) × (Fin N → Ω) → Fin (N*d) → ℝ)
    (i j : Fin N) (t : ℝ) (z : (Fin N → A) × (Fin N → Ω)) : ℝ :=
  weakPairFeature ψ φ atom t (realParticle X i t z) (realParticle X j t z)-
    weakPairFeature ψ φ atom t (arrayCopy Y i t z) (arrayCopy Y j t z)

set_option maxHeartbeats 1200000 in
/-- 原始入力から、全N・全行・全辞書列・全粒子対・全時刻に共通の特徴誤差率を構成する。
    同期率を入力で仮定せず、exists_synchronous_fourth_rateから得る。 -/
theorem exists_feature_coupled_family (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P]
    (W : Fin d → ℝ≥0 → Ω → ℝ) (hW : ∀ j, IsBrownianReal (W j) P)
    (hm : ∀ j t, Measurable (W j t)) (hI : iIndepFun (fun j ω t => W j t ω) P)
    (ξ : A → EuclideanSpace ℝ (Fin d)) (hξm : Measurable ξ) (hξ : MemLp ξ 4 π)
    (T : ℝ) (hT : 0 ≤ T) (σ : ℝ) {L : ℝ≥0}
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : LipschitzWith L K)
    (nr nc : ℕ) (ψ : Fin nr → ℝ → ℝ) (φ : Fin nr → EuclideanSpace ℝ (Fin d) → ℝ)
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
        ∀ a m (i j : Fin N),
          StronglyMeasurable (fun z : ℝ × ((Fin N → A) × (Fin N → Ω)) => featureGap (ψ a) (φ a) (atom m) Y X i j z.1 z.2) ∧
          ∀ t ∈ Icc 0 T,
            MemLp (featureGap (ψ a) (φ a) (atom m) Y X i j t) 2 (arrayMeasure π P (Fin N)) ∧
            (∫ z, (featureGap (ψ a) (φ a) (atom m) Y X i j t z)^2 ∂arrayMeasure π P (Fin N)) ≤ F/(N : ℝ) := by
  obtain ⟨Y,R,S,hy,hS,hRate⟩ := exists_synchronous_fourth_rate π P W hW hm hI ξ hξm hξ T hT σ K hK
  refine ⟨Y,R,S,featureCouplingConstant B G H C D R S,hy,hS,
    feature_coupling_constant_nonneg _ _ _ _ _ _ _,fun N hN => ?_⟩
  obtain ⟨BN,X,hs,hr⟩ := hRate N hN
  have hj i := particle_real_jointly_measurable (arrayMeasure π P (Fin N)) BN K σ _ X hs.solution i
  refine ⟨BN,X,hs,hr,fun a m i j => ⟨?_,fun t ht => ?_⟩⟩
  · exact (weak_pair_feature_jointly_measurable (ψ a) (φ a) (atom m) (hψm a) (hφ a) (hAL m)
      (realParticle X i) (realParticle X j) (hj i) (hj j)).sub
      (weak_pair_feature_jointly_measurable (ψ a) (φ a) (atom m) (hψm a) (hφ a) (hAL m)
        (arrayCopy Y i) (arrayCopy Y j) (hy.joint N i) (hy.joint N j))
  · exact weak_pair_feature_coupling (arrayMeasure π P (Fin N)) N hN (ψ a) (φ a) (atom m) (hAL m)
      B G H J C R S hC hS (hφ a) (hAtom m) t (hψ a t ht)
      (realParticle X i t) (realParticle X j t) (arrayCopy Y i t) (arrayCopy Y j t)
      ((hj i).measurable.comp (measurable_const.prodMk measurable_id))
      ((hj j).measurable.comp (measurable_const.prodMk measurable_id))
      ((hy.paths N i).measurable t ht) ((hy.paths N j).measurable t ht)
      (hy.fourth N i t ht).1 (hy.fourth N j t ht).1 (hr i t ht).1 (hr j t ht).1
      (hy.fourth N i t ht).2 (hy.fourth N j t ht).2 (hr i t ht).2 (hr j t ht).2

end WMFKIFeatureCoupling
