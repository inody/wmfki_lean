import WMFKI_Stochastic.WeakFeatureCoupling

open MeasureTheory
open WMFKIExternalProbe
namespace WMFKIFeatureCoupling
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

noncomputable def featureSecondConstant (B G C R : ℝ) : ℝ := 3*(B*G*C)^2*(1+2*R)

theorem feature_second_constant_nonneg (B G C R : ℝ) (hR : 0 ≤ R) :
    0 ≤ featureSecondConstant B G C R := by unfold featureSecondConstant;positivity

theorem weak_pair_feature_growth (ψ : ℝ → ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (B G H J C : ℝ) (hC : 0 ≤ C) (hφ : C3TestBounds d φ G H J)
    (hK : ∀ x, ‖K x‖ ≤ C*(1+‖x‖)) (t : ℝ) (hψ : |ψ t| ≤ B)
    (x y : EuclideanSpace ℝ (Fin d)) :
    |weakPairFeature ψ φ K t x y| ≤ (B*G*C)*(1+‖x‖+‖y‖) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans hψ
  have hG : 0 ≤ G := (norm_nonneg (gradient φ 0)).trans (hφ.observation_bounds.1 0)
  have hk : ‖K (x-y)‖ ≤ C*(1+‖x‖+‖y‖) := (hK _).trans
    (mul_le_mul_of_nonneg_left (by linarith [norm_sub_le x y]) hC)
  calc
    _ = |ψ t| * |inner ℝ (gradient φ x) (K (x-y))| := abs_mul _ _
    _ ≤ B*(G*(C*(1+‖x‖+‖y‖))) := mul_le_mul hψ
      ((abs_real_inner_le_norm _ _).trans
        (mul_le_mul (hφ.observation_bounds.1 x) hk (norm_nonneg _) hG)) (abs_nonneg _) hB
    _ = _ := by ring

theorem weak_pair_feature_second (P : Measure Ω) [IsProbabilityMeasure P]
    (ψ : ℝ → ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hKm : Measurable K)
    (B G H J C R : ℝ) (hC : 0 ≤ C) (hφ : C3TestBounds d φ G H J)
    (hK : ∀ x, ‖K x‖ ≤ C*(1+‖x‖)) (t : ℝ) (hψ : |ψ t| ≤ B)
    (x y : Ω → EuclideanSpace ℝ (Fin d)) (hxm : Measurable x) (hym : Measurable y)
    (hx : MemLp x 2 P) (hy : MemLp y 2 P)
    (hxR : (∫ ω, ‖x ω‖^2 ∂P) ≤ R) (hyR : (∫ ω, ‖y ω‖^2 ∂P) ≤ R) :
    MemLp (fun ω => weakPairFeature ψ φ K t (x ω) (y ω)) 2 P ∧
    (∫ ω, (weakPairFeature ψ φ K t (x ω) (y ω))^2 ∂P) ≤ featureSecondConstant B G C R := by
  obtain ⟨hL,hB⟩ := three_l2_moment (P := P) (fun _ : Ω => 1) (fun ω => ‖x ω‖) (fun ω => ‖y ω‖)
    (memLp_const _) hx.norm hy.norm 1 R R (by simp) hxR hyR
  apply real_l2_domination P _ (fun ω => (B*G*C)*(1+‖x ω‖+‖y ω‖))
    (measurable_const.mul (((gradient_measurable_of_c3 hφ).comp hxm).inner (hKm.comp (hxm.sub hym))))
    (hL.const_mul _) (fun ω => weak_pair_feature_growth ψ φ K B G H J C hC hφ hK t hψ _ _)
  simp_rw [mul_pow]
  rw [integral_const_mul]
  calc
    _ ≤ (B^2*G^2*C^2)*(3*(1+R+R)) := mul_le_mul_of_nonneg_left hB (by positivity)
    _ = featureSecondConstant B G C R := by unfold featureSecondConstant;ring

end WMFKIFeatureCoupling
