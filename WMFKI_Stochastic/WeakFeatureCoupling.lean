import WMFKI_Stochastic.CoupledFeatureMoments
import WMFKI_Stochastic.ObservationDerivativeBounds

open MeasureTheory Set
open WMFKIExternalProbe
open scoped NNReal
namespace WMFKIFeatureCoupling
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- 原稿の実際の時間重み・勾配・辞書核。代用の勾配変数ではない。 -/
noncomputable def weakPairFeature (ψ : ℝ → ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) : ℝ := pairFeature (ψ t) (gradient φ) K x y

noncomputable def featureCouplingConstant (B G H C D R S : ℝ) : ℝ :=
  B^2*featureMomentFactor G H C D R*Real.sqrt S

theorem feature_coupling_constant_nonneg (B G H C D R S : ℝ) :
    0 ≤ featureCouplingConstant B G H C D R S :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (feature_moment_factor_nonneg _ _ _ _ _)) (Real.sqrt_nonneg _)

theorem gradient_measurable_of_c3 {φ : EuclideanSpace ℝ (Fin d) → ℝ} {G H J : ℝ}
    (hφ : C3TestBounds d φ G H J) : Measurable (gradient φ) := by
  have hH : 0 ≤ H := (norm_nonneg (fderiv ℝ (fderiv ℝ φ) 0)).trans (hφ.second 0)
  have hl : LipschitzWith ⟨H,hH⟩ (gradient φ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖gradient φ x-gradient φ y‖ ≤ H*‖x-y‖
    exact hφ.observation_bounds.2.2.1 x y
  exact hl.continuous.measurable

/-- 同期L4評価から、実際の弱特徴のL2評価へ。i≠jを必要とせず依存を許す。 -/
theorem weak_pair_feature_coupling (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ) (hN : 0 < N) (ψ : ℝ → ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) {D : ℝ≥0}
    (hKL : LipschitzWith D K) (B G H J C R S : ℝ) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hφ : C3TestBounds d φ G H J) (hK : ∀ x, ‖K x‖ ≤ C*(1+‖x‖))
    (t : ℝ) (hψ : |ψ t| ≤ B)
    (u v x y : Ω → EuclideanSpace ℝ (Fin d))
    (hum : Measurable u) (hvm : Measurable v) (hxm : Measurable x) (hym : Measurable y)
    (hx : MemLp x 4 P) (hy : MemLp y 4 P)
    (hu : MemLp (fun ω => u ω-x ω) 4 P) (hv : MemLp (fun ω => v ω-y ω) 4 P)
    (hxR : (∫ ω, ‖x ω‖^4 ∂P) ≤ R) (hyR : (∫ ω, ‖y ω‖^4 ∂P) ≤ R)
    (huS : (∫ ω, ‖u ω-x ω‖^4 ∂P) ≤ S/(N : ℝ)^2)
    (hvS : (∫ ω, ‖v ω-y ω‖^4 ∂P) ≤ S/(N : ℝ)^2) :
    let F := fun ω => weakPairFeature ψ φ K t (u ω) (v ω)-weakPairFeature ψ φ K t (x ω) (y ω)
    MemLp F 2 P ∧ (∫ ω,(F ω)^2 ∂P) ≤ featureCouplingConstant B G H C D R S/(N : ℝ) := by
  have hG : 0 ≤ G := (norm_nonneg (fderiv ℝ φ 0)).trans (hφ.first 0)
  have hH : 0 ≤ H := (norm_nonneg (fderiv ℝ (fderiv ℝ φ) 0)).trans (hφ.second 0)
  obtain ⟨hl,hb⟩ := weighted_coupled_feature_moment P (ψ t) B hψ (gradient φ) K
    (gradient_measurable_of_c3 hφ) hKL.continuous.measurable G H C D hG hH hC D.coe_nonneg
    hφ.observation_bounds.1 hφ.observation_bounds.2.2.1 hK
    (fun a b => hKL.norm_sub_le a b) x y (fun ω => u ω-x ω) (fun ω => v ω-y ω)
    hxm hym (hum.sub hxm) (hvm.sub hym) hx hy hu hv (S/(N : ℝ)^2) R (by positivity) hxR hyR huS hvS
  have heq (a b : EuclideanSpace ℝ (Fin d)) : a+(b-a) = b := by abel
  simp only [heq] at hl hb
  refine ⟨hl,hb.trans_eq ?_⟩
  rw [Real.sqrt_div hS,Real.sqrt_sq (by exact_mod_cast hN.le)]
  unfold featureCouplingConstant
  ring

end WMFKIFeatureCoupling
