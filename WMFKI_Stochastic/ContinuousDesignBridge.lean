import WMFKI_Stochastic.ContinuousPopulationRate
import WMFKI_Stochastic.IndependentObservedParticleBudget

open MeasureTheory Set
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
open WMFKIExternalProbe WMFKISynchronousModel WMFKIFeatureCoupling WMFKIPopulationDesign
namespace WMFKIObservedDesign

/-- 被積分関数の代数的一致。積分の和との交換ではない。 -/
theorem feature_average_configuration {Ω : Type*} (N d : ℕ)
    (ψ : ℝ → ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (U : Fin N → ℝ → Ω → EuclideanSpace ℝ (Fin d)) (t : ℝ) (ω : Ω) :
    offDiagonalAverage N (fun i j ω => weakPairFeature ψ φ K t (U i t ω) (U j t ω)) ω =
      ψ t*configurationKernelFunctional N d φ (fun i => U i t ω) K := by
  classical
  have hi (i j : Fin N) (a b : ℝ) : (if i=j then 0 else a*b) = a*(if i=j then 0 else b) := by
    by_cases h : i=j <;> simp [h]
  simp only [offDiagonalAverage,weakPairFeature,pairFeature,configuration_kernel_apply,hi,← Finset.mul_sum]
  ring

/-- 任意の入力関数に対する定義等式。SDEや正則性を仮定せず、同じ積分そのものを同定する。 -/
theorem continuous_design_bridge {Ω : Type*} (N d nr nc : ℕ) (T : ℝ)
    (ψ : Fin nr → ℝ → ℝ) (φ : Fin nr → EuclideanSpace ℝ (Fin d) → ℝ)
    (atom : Fin nc → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ) (ω : Ω) :
    continuousFeatureDesign N nr nc T ψ φ atom (realParticle X) ω =
      continuousDictionaryDesign nr N d nc atom φ ψ T X ω := by
  funext a m
  simp only [continuousFeatureDesign,continuousPairAverage]
  simp_rw [feature_average_configuration N d (ψ a) (φ a) (atom m) (realParticle X)]
  simp only [configuration_kernel_apply,realParticle,continuousDictionaryDesign,continuousKernelVector,
    normalizedTestVector,one_div,empiricalPairInteraction]

end WMFKIObservedDesign
