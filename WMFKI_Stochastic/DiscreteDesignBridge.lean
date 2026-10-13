import WMFKI_Stochastic.ContinuousDesignBridge
import Lean_Code.ObservedFeatures

open MeasureTheory
open WMFKIExternalProbe WMFKIFeatureCoupling
namespace WMFKIObservedDesign

/-- 全OrderedPair和と対角0の二重和はN=0,1を含めて一致する。 -/
theorem ordered_pair_sum (N : ℕ) (f : Fin N → Fin N → ℝ) :
    (∑ p : WMFKI.OrderedPair N, f p.1.1 p.1.2) = ∑ i, ∑ j, if i=j then 0 else f i j := by
  classical
  change (∑ p : (Finset.univ : Finset (Fin N)).offDiag, f p.1.1 p.1.2) = _
  rw [Finset.sum_coe_sort _ (fun p : Fin N × Fin N => f p.1 p.2)]
  have he : (Finset.univ : Finset (Fin N)).offDiag = Finset.univ.filter (fun p : Fin N × Fin N => p.1 ≠ p.2) := by
    ext p
    simp
  rw [he,Finset.sum_filter,Fintype.sum_prod_type (fun p : Fin N × Fin N => if p.1 ≠ p.2 then f p.1 p.2 else 0)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i=j <;> simp [h]

/-- 既存の離散辞書設計は、本物のgradientで構成した本番fullPairDesignと厳密に同じ。 -/
theorem discrete_design_bridge {Ω : Type*} (N nt d nr nc : ℕ) (w τ : Fin nt → ℝ)
    (ψ : Fin nr → ℝ → ℝ) (φ : Fin nr → EuclideanSpace ℝ (Fin d) → ℝ)
    (atom : Fin nc → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : Fin nt → Fin N → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    discreteDictionaryDesign nr N nt d nc w τ atom φ ψ x ω =
      WMFKI.fullPairDesign (WMFKI.observedPairFeature (fun ω i t => x t i ω)
        (fun a t => ψ a (τ t)) (fun a => gradient (φ a)) atom) w ω := by
  funext a m
  have he (t : Fin nt) := ordered_pair_sum N (fun i j =>
    ψ a (τ t)*inner ℝ (gradient (φ a) (x t i ω)) (atom m (x t i ω-x t j ω)))
  simp only [discreteDictionaryDesign,discreteKernelVector,normalizedTestVector,
    discreteKernelDesign,pairTimeAverage,WMFKI.fullPairDesign,WMFKI.observedPairFeature,
    div_eq_mul_inv,inv_pow]
  simp_rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  ring

end WMFKIObservedDesign
