import WMFKI_Stochastic.DiscreteDesignBridge

open MeasureTheory
open WMFKIExternalProbe WMFKIFeatureCoupling
namespace WMFKIObservedDesign

noncomputable def rowNormalizedMatrix {Ω : Type*} (nr nc : ℕ)
    (r : Fin nr → Fin nc → Ω → ℝ) (ω : Ω) : Matrix (Fin nr) (Fin nc) ℝ :=
  fun a m => (Real.sqrt (nr : ℝ))⁻¹*r a m ω

/-- 行だけをsqrt(nr)で正規化するFrobenius集約。行・列の独立性は不要。 -/
theorem row_normalized_matrix_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (nr nc : ℕ) (hnr : 0 < nr)
    (r : Fin nr → Fin nc → Ω → ℝ) (hr : ∀ a m, MemLp (r a m) 2 P)
    (C : ℝ) (hb : ∀ a m, (∫ ω, r a m ω^2 ∂P) ≤ C) :
    let A := rowNormalizedMatrix nr nc r
    MemLp (fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => A ω am.1 am.2) :
      EuclideanSpace ℝ (Fin nr × Fin nc))) 2 P ∧
    (∫ ω, WMFKI.frobenius (A ω)^2 ∂P) ≤ (nc : ℝ)*C := by
  dsimp only
  have hl : MemLp (fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc =>
      (Real.sqrt (nr : ℝ))⁻¹*r am.1 am.2 ω) : EuclideanSpace ℝ (Fin nr × Fin nc))) 2 P := by
    apply MemLp.of_eval_piLp
    intro am
    exact (hr am.1 am.2).const_mul _
  have he ω : WMFKI.frobenius (rowNormalizedMatrix nr nc r ω)^2 =
      (nr : ℝ)⁻¹*∑ am : Fin nr × Fin nc, r am.1 am.2 ω^2 := by
    rw [WMFKI.frobenius_eq_vector_norm,EuclideanSpace.real_norm_sq_eq]
    change (∑ am : Fin nr × Fin nc, ((Real.sqrt (nr : ℝ))⁻¹*r am.1 am.2 ω)^2) = _
    simp_rw [mul_pow]
    rw [← Finset.mul_sum,inv_pow,Real.sq_sqrt (Nat.cast_nonneg nr)]
  refine ⟨hl,?_⟩
  simp_rw [he]
  rw [integral_const_mul,integral_finsetSum _ (fun am _ => (hr am.1 am.2).integrable_sq)]
  calc
    _ ≤ (nr : ℝ)⁻¹*∑ _am : Fin nr × Fin nc, C :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun am _ => hb am.1 am.2)) (by positivity)
    _ = _ := by
      have hn : (nr : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnr)
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul]
      field_simp

/-- 真の観測値から作った辞書行列の摂動。雑音対潜在位置の独立性だけでよい。 -/
theorem observed_dictionary_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (nr nc N nt d : ℕ) (hnr : 0 < nr) (hN : 0 < N)
    (R q : ℝ) (hR : 0 ≤ R) (hq : 0 ≤ q)
    (D : ObservationSamples (E := EuclideanSpace ℝ (Fin d)) P N nt R q)
    (w τ : Fin nt → ℝ) (W : ℝ) (hw : (∑ t,|w t|) ≤ W)
    (ψ : Fin nr → ℝ → ℝ) (φ : Fin nr → EuclideanSpace ℝ (Fin d) → ℝ)
    (atom : Fin nc → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (G H J C A B : ℝ) (hG : 0 ≤ G) (hH : 0 ≤ H) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hφ : ∀ a, C3TestBounds d (φ a) G H J) (hψ : ∀ a t, |ψ a (τ t)| ≤ B)
    (hm : ∀ m, Measurable (atom m)) (hg : ∀ m x, ‖atom m x‖ ≤ C*(1+‖x‖))
    (hLip : ∀ m x y, ‖atom m x-atom m y‖ ≤ A*‖x-y‖) :
    let X := fun t i ω => D.pos t i ω+D.noise t i ω
    let E := fun ω => discreteDictionaryDesign nr N nt d nc w τ atom φ ψ X ω-
      discreteDictionaryDesign nr N nt d nc w τ atom φ ψ D.pos ω
    MemLp (fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => E ω am.1 am.2) :
      EuclideanSpace ℝ (Fin nr × Fin nc))) 2 P ∧
    (∫ ω, WMFKI.frobenius (E ω)^2 ∂P) ≤ (nc : ℝ)*kernelObservationConstant W B G H C A R*q := by
  let X := fun t i ω => D.pos t i ω+D.noise t i ω
  let r := fun a m ω => discreteKernelDesign N nt d w τ (atom m) (φ a) (ψ a) X ω-
    discreteKernelDesign N nt d w τ (atom m) (φ a) (ψ a) D.pos ω
  have hp a m := discrete_kernel_observation_moment P N nt d R q D hN hq hR w τ (atom m) (hm m)
    (φ a) (ψ a) G H J C A B hG hH hC hA (hφ a) (hψ a) (hg m) (hLip m)
  have hW : 0 ≤ W := (Finset.sum_nonneg (fun t _ => abs_nonneg (w t))).trans hw
  have hw2 := (sq_le_sq₀ (Finset.sum_nonneg (fun t _ => abs_nonneg (w t))) hW).mpr hw
  have hb a m : (∫ ω, r a m ω^2 ∂P) ≤ kernelObservationConstant W B G H C A R*q := by
    apply (hp a m).2.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw2 (sq_nonneg B)) (by positivity)) hq
  have hh := row_normalized_matrix_moment P nr nc hnr r (fun a m => (hp a m).1)
    (kernelObservationConstant W B G H C A R*q) hb
  have he ω : discreteDictionaryDesign nr N nt d nc w τ atom φ ψ X ω-
      discreteDictionaryDesign nr N nt d nc w τ atom φ ψ D.pos ω =
      rowNormalizedMatrix nr nc r ω := by
    funext a m
    simp [discreteDictionaryDesign,discreteKernelVector,normalizedTestVector,r,one_div,mul_sub,rowNormalizedMatrix]
  simp_rw [← he] at hh
  simpa only [mul_assoc] using hh

end WMFKIObservedDesign
