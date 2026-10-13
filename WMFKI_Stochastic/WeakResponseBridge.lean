import WMFKI_Stochastic.ActualObservedDesign
import Lean_Code.WeakPairRecovery

open MeasureTheory
open WMFKIExternalProbe
namespace WMFKIJointAssembly

/-- 実際のLaplacian・時間微分を用いた旧応答と本番応答は、N=0も含めて同じ有限和。 -/
theorem weak_response_bridge {Ω : Type*} (nr N nt d : ℕ)
    (σ : ℝ) (w τ : Fin nt → ℝ)
    (φ : Fin nr → EuclideanSpace ℝ (Fin d) → ℝ) (ψ : Fin nr → ℝ → ℝ)
    (x : Fin nt → Fin N → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    discreteResponseVector nr N nt d σ w τ φ ψ x ω =
      WithLp.toLp 2 (WMFKI.observedWeakResponse (fun ω i t => x t i ω) φ
        (fun a => Laplacian.laplacian (φ a)) (fun a t => ψ a (τ t))
        (fun a t => deriv (ψ a) (τ t)) w σ ω) := by
  ext a
  have h1 : (∑ i, ∑ t, w t*φ a (x t i ω)*deriv (ψ a) (τ t)) =
      ∑ t, ∑ i, w t*φ a (x t i ω)*deriv (ψ a) (τ t) := Finset.sum_comm
  have h2 : (∑ i, ∑ t, w t*Laplacian.laplacian (φ a) (x t i ω)*ψ a (τ t)) =
      ∑ t, ∑ i, w t*Laplacian.laplacian (φ a) (x t i ω)*ψ a (τ t) := Finset.sum_comm
  change (1/Real.sqrt (nr : ℝ))*discreteWeakResponse N nt d σ w τ (φ a) (ψ a) x ω = _
  simp only [discreteWeakResponse,particleTimeAverage,weakResponseIntegrand,WMFKI.observedWeakResponse]
  rw [h1,h2]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [div_eq_mul_inv,mul_inv_rev,one_mul]
  ring

/-- 応答・設計の両方を同じ観測値で同定し、本番の全ペア回帰残差へつなぐ。 -/
theorem full_residual_bridge {Ω : Type*} (nr N nt d nc : ℕ)
    (σ : ℝ) (w τ : Fin nt → ℝ)
    (φ : Fin nr → EuclideanSpace ℝ (Fin d) → ℝ) (ψ : Fin nr → ℝ → ℝ)
    (atom : Fin nc → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin nc)) (x : Fin nt → Fin N → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    discreteResponseVector nr N nt d σ w τ φ ψ x ω-
      WMFKI.matrixMap (discreteDictionaryDesign nr N nt d nc w τ atom φ ψ x ω) θ =
    WMFKI.fullRegressionResidual (WMFKI.observedPairFeature (fun ω i t => x t i ω)
      (fun a t => ψ a (τ t)) (fun a => gradient (φ a)) atom) w
      (WMFKI.observedWeakResponse (fun ω i t => x t i ω) φ (fun a => Laplacian.laplacian (φ a))
        (fun a t => ψ a (τ t)) (fun a t => deriv (ψ a) (τ t)) w σ) θ ω := by
  rw [weak_response_bridge,WMFKIObservedDesign.discrete_design_bridge]
  ext a
  simp [WMFKI.fullRegressionResidual,WMFKI.matrixMap_apply]

end WMFKIJointAssembly
