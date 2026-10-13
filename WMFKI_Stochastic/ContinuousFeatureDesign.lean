import WMFKI_Stochastic.ContinuousPairAverage
import WMFKI_Stochastic.WeakFeatureGrowth
import Lean_Code.MatrixBridge

open MeasureTheory Set
open WMFKIExternalProbe
open scoped NNReal BigOperators
namespace WMFKIFeatureCoupling
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

noncomputable def continuousFeatureDesign (N nr nc : ℕ) (T : ℝ)
    (ψ : Fin nr → ℝ → ℝ) (φ : Fin nr → EuclideanSpace ℝ (Fin d) → ℝ)
    (atom : Fin nc → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (U : Fin N → ℝ → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) : Matrix (Fin nr) (Fin nc) ℝ :=
  fun a m => (Real.sqrt (nr : ℝ))⁻¹*continuousPairAverage N T
    (fun t i j ω => weakPairFeature (ψ a) (φ a) (atom m) t (U i t ω) (U j t ω)) ω

/-- 差だけでなく、各設計そのものの時間積分の可積分性を保証する。 -/
theorem process_pair_average_second (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ) (hN : 0 < N) (T : ℝ) (hT : 0 ≤ T)
    (ψ : ℝ → ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hψm : Measurable ψ)
    {D : ℝ≥0} (hKL : LipschitzWith D K) (B G H J C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hφ : C3TestBounds d φ G H J) (hψ : ∀ t ∈ Icc 0 T, |ψ t| ≤ B)
    (hK : ∀ x, ‖K x‖ ≤ C*(1+‖x‖))
    (U : Fin N → ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hm : ∀ i, StronglyMeasurable (fun z : ℝ × Ω => U i z.1 z.2))
    (hU : ∀ t ∈ Icc 0 T, ∀ i, MemLp (U i t) 2 P ∧ (∫ ω, ‖U i t ω‖^2 ∂P) ≤ R) :
    let f := fun t i j ω => weakPairFeature ψ φ K t (U i t ω) (U j t ω)
    MemLp (continuousPairAverage N T f) 2 P ∧
    (∫ ω, (continuousPairAverage N T f ω)^2 ∂P) ≤ T^2*featureSecondConstant B G C R ∧
    (∀ᵐ ω ∂P, IntervalIntegrable (fun s => offDiagonalAverage N (f s) ω) volume 0 T) := by
  apply continuous_pair_average_second P N hN T hT _
    (fun i j => weak_pair_feature_jointly_measurable ψ φ K hψm hφ hKL (U i) (U j) (hm i) (hm j))
    _ (feature_second_constant_nonneg _ _ _ _ hR)
  intro t ht i j
  exact weak_pair_feature_second P ψ φ K hKL.continuous.measurable B G H J C R hC hφ hK t (hψ t ht)
    (U i t) (U j t) ((hm i).measurable.comp (measurable_const.prodMk measurable_id))
    ((hm j).measurable.comp (measurable_const.prodMk measurable_id))
    (hU t ht i).1 (hU t ht j).1 (hU t ht i).2 (hU t ht j).2

set_option maxHeartbeats 1200000 in
/-- 実際の二つの連続時間設計の差。Frobenius二乗のみを加算し、作用素ノルムの加算性は使わない。 -/
theorem continuous_design_coupling (P : Measure Ω) [IsProbabilityMeasure P]
    (N nr nc : ℕ) (hN : 0 < N) (hnr : 0 < nr) (T : ℝ) (hT : 0 ≤ T)
    (ψ : Fin nr → ℝ → ℝ) (φ : Fin nr → EuclideanSpace ℝ (Fin d) → ℝ)
    (atom : Fin nc → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (B G H J C RU RV F : ℝ) (hC : 0 ≤ C) (hRU : 0 ≤ RU) (hRV : 0 ≤ RV) (hF : 0 ≤ F) {D : ℝ≥0}
    (hφ : ∀ a, C3TestBounds d (φ a) G H J) (hψm : ∀ a, Measurable (ψ a))
    (hψ : ∀ a t, t ∈ Icc 0 T → |ψ a t| ≤ B)
    (hAtom : ∀ m x, ‖atom m x‖ ≤ C*(1+‖x‖)) (hAL : ∀ m, LipschitzWith D (atom m))
    (U V : Fin N → ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hUm : ∀ i, StronglyMeasurable (fun z : ℝ × Ω => U i z.1 z.2))
    (hVm : ∀ i, StronglyMeasurable (fun z : ℝ × Ω => V i z.1 z.2))
    (hU : ∀ t ∈ Icc 0 T, ∀ i, MemLp (U i t) 2 P ∧ (∫ ω, ‖U i t ω‖^2 ∂P) ≤ RU)
    (hV : ∀ t ∈ Icc 0 T, ∀ i, MemLp (V i t) 2 P ∧ (∫ ω, ‖V i t ω‖^2 ∂P) ≤ RV)
    (hGap : ∀ a m i j t, t ∈ Icc 0 T →
      MemLp (fun ω => weakPairFeature (ψ a) (φ a) (atom m) t (U i t ω) (U j t ω)-
        weakPairFeature (ψ a) (φ a) (atom m) t (V i t ω) (V j t ω)) 2 P ∧
      (∫ ω, (weakPairFeature (ψ a) (φ a) (atom m) t (U i t ω) (U j t ω)-
        weakPairFeature (ψ a) (φ a) (atom m) t (V i t ω) (V j t ω))^2 ∂P) ≤ F/(N : ℝ)) :
    let A := fun ω => continuousFeatureDesign N nr nc T ψ φ atom U ω-continuousFeatureDesign N nr nc T ψ φ atom V ω
    MemLp (fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => A ω am.1 am.2) :
      EuclideanSpace ℝ (Fin nr × Fin nc))) 2 P ∧
    (∫ ω, WMFKI.frobenius (A ω)^2 ∂P) ≤ (nc : ℝ)*T^2*F/(N : ℝ) := by
  let f := fun a m t i j ω => weakPairFeature (ψ a) (φ a) (atom m) t (U i t ω) (U j t ω)
  let g := fun a m t i j ω => weakPairFeature (ψ a) (φ a) (atom m) t (V i t ω) (V j t ω)
  have hf a m := process_pair_average_second P N hN T hT (ψ a) (φ a) (atom m) (hψm a) (hAL m)
    B G H J C RU hC hRU (hφ a) (hψ a) (hAtom m) U hUm hU
  have hg a m := process_pair_average_second P N hN T hT (ψ a) (φ a) (atom m) (hψm a) (hAL m)
    B G H J C RV hC hRV (hφ a) (hψ a) (hAtom m) V hVm hV
  let r := fun (am : Fin nr × Fin nc) ω => continuousPairAverage N T (f am.1 am.2) ω-continuousPairAverage N T (g am.1 am.2) ω
  have hr (am : Fin nr × Fin nc) : MemLp (r am) 2 P ∧ (∫ ω, (r am ω)^2 ∂P) ≤ T^2*F/(N : ℝ) := by
    obtain ⟨hL,hB,_⟩ := continuous_pair_average_second P N hN T hT
      (fun t i j ω => f am.1 am.2 t i j ω-g am.1 am.2 t i j ω)
      (fun i j => (weak_pair_feature_jointly_measurable _ _ _ (hψm _) (hφ _) (hAL _) _ _ (hUm i) (hUm j)).sub
        (weak_pair_feature_jointly_measurable _ _ _ (hψm _) (hφ _) (hAL _) _ _ (hVm i) (hVm j)))
      (F/(N : ℝ)) (by positivity) (fun t ht i j => hGap am.1 am.2 i j t ht)
    have he := continuous_pair_average_sub P N T (f am.1 am.2) (g am.1 am.2)
      (hf am.1 am.2).2.2 (hg am.1 am.2).2.2
    refine ⟨MemLp.ae_eq he.symm hL,?_⟩
    calc
      _ = ∫ ω, (continuousPairAverage N T (fun t i j ω => f am.1 am.2 t i j ω-g am.1 am.2 t i j ω) ω)^2 ∂P :=
        integral_congr_ae (he.mono (fun _ h => congrArg (fun x : ℝ => x^2) h))
      _ ≤ T^2*(F/(N : ℝ)) := hB
      _ = _ := by ring
  dsimp only
  have he ω a m : (continuousFeatureDesign N nr nc T ψ φ atom U ω-continuousFeatureDesign N nr nc T ψ φ atom V ω) a m =
      (Real.sqrt (nr : ℝ))⁻¹*r (a,m) ω := by
    simp [continuousFeatureDesign,r,f,g,mul_sub]
  have hLp : MemLp (fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc =>
      (continuousFeatureDesign N nr nc T ψ φ atom U ω-continuousFeatureDesign N nr nc T ψ φ atom V ω) am.1 am.2) :
      EuclideanSpace ℝ (Fin nr × Fin nc))) 2 P := by
    apply MemLp.of_eval_piLp
    intro am
    change MemLp (fun ω => (continuousFeatureDesign N nr nc T ψ φ atom U ω-continuousFeatureDesign N nr nc T ψ φ atom V ω) am.1 am.2) 2 P
    simp_rw [he]
    exact (hr am).1.const_mul _
  have hn ω : WMFKI.frobenius (continuousFeatureDesign N nr nc T ψ φ atom U ω-continuousFeatureDesign N nr nc T ψ φ atom V ω)^2 =
      (nr : ℝ)⁻¹*∑ am, r am ω^2 := by
    rw [WMFKI.frobenius_eq_vector_norm,EuclideanSpace.real_norm_sq_eq]
    change (∑ am : Fin nr × Fin nc, ((continuousFeatureDesign N nr nc T ψ φ atom U ω-continuousFeatureDesign N nr nc T ψ φ atom V ω) am.1 am.2)^2) = _
    simp_rw [he,mul_pow]
    rw [← Finset.mul_sum,inv_pow,Real.sq_sqrt (Nat.cast_nonneg nr)]
  refine ⟨hLp,?_⟩
  simp_rw [hn]
  rw [integral_const_mul,integral_finsetSum _ (fun am _ => (hr am).1.integrable_sq)]
  calc
    _ ≤ (nr : ℝ)⁻¹*∑ _am : Fin nr × Fin nc, T^2*F/(N : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun am _ => (hr am).2)) (by positivity)
    _ = _ := by
      have hl : (nr : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnr)
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul]
      field_simp

end WMFKIFeatureCoupling
