import WMFKI_Stochastic.ThreeMatrixErrors

open MeasureTheory Set
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
open WMFKIExternalProbe WMFKIFeatureCoupling
namespace WMFKIObservedDesign

/-- 可測L2の雑音族を潜在過程に独立に付加し、観測・求積・母集団誤差を合成する。
    この補題の連続設計予算は、原始入力終点で先の構成定理から供給する。 -/
theorem independent_observed_design_budget {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Pe : Measure Ξ) [IsProbabilityMeasure P] [IsProbabilityMeasure Pe]
    (N nt d nr nc : ℕ) (hN : 0 < N) (hnr : 0 < nr)
    (R q : ℝ) (hR : 0 ≤ R) (hq : 0 ≤ q) (w τ : Fin nt → ℝ) (W : ℝ) (hw : (∑ t,|w t|) ≤ W)
    (ψ : Fin nr → ℝ → ℝ) (φ : Fin nr → EuclideanSpace ℝ (Fin d) → ℝ)
    (atom : Fin nc → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (G H J C A B : ℝ) (hG : 0 ≤ G) (hH : 0 ≤ H) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hφ : ∀ a, C3TestBounds d (φ a) G H J) (hψ : ∀ a t, |ψ a (τ t)| ≤ B)
    (hm : ∀ m, Measurable (atom m)) (hg : ∀ m x, ‖atom m x‖ ≤ C*(1+‖x‖))
    (hLip : ∀ m x y, ‖atom m x-atom m y‖ ≤ A*‖x-y‖)
    (T : ℝ) (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hxm : ∀ t i, Measurable (particleGrid N d nt τ X t i))
    (hxl : ∀ t i, MemLp (particleGrid N d nt τ X t i) 2 P)
    (hxR : ∀ t i, (∫ ω, ‖particleGrid N d nt τ X t i ω‖^2 ∂P) ≤ R)
    (ε : Fin nt → Fin N → Ξ → EuclideanSpace ℝ (Fin d))
    (hεm : ∀ t i, Measurable (ε t i)) (hεl : ∀ t i, MemLp (ε t i) 2 Pe)
    (hεq : ∀ t i, (∫ z, ‖ε t i z‖^2 ∂Pe) ≤ q)
    (Aref : Matrix (Fin nr) (Fin nc) ℝ) (S Q e : ℝ)
    (hcl : MemLp (fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc =>
      (continuousDictionaryDesign nr N d nc atom φ ψ T X ω-Aref) am.1 am.2) : EuclideanSpace ℝ (Fin nr × Fin nc))) 2 P)
    (hcS : (∫ ω, WMFKI.frobenius (continuousDictionaryDesign nr N d nc atom φ ψ T X ω-Aref)^2 ∂P) ≤ S)
    (hql : MemLp (fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc =>
      (discreteDictionaryDesign nr N nt d nc w τ atom φ ψ (particleGrid N d nt τ X) ω-
        continuousDictionaryDesign nr N d nc atom φ ψ T X ω) am.1 am.2) : EuclideanSpace ℝ (Fin nr × Fin nc))) 2 P)
    (hqQ : (∫ ω, WMFKI.frobenius (discreteDictionaryDesign nr N nt d nc w τ atom φ ψ (particleGrid N d nt τ X) ω-
      continuousDictionaryDesign nr N d nc atom φ ψ T X ω)^2 ∂P) ≤ Q*e) :
    let Y := fun t i (z : Ω × Ξ) => particleGrid N d nt τ X t i z.1+ε t i z.2
    let E := fun z => discreteDictionaryDesign nr N nt d nc w τ atom φ ψ Y z-Aref
    MemLp (fun z => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => E z am.1 am.2) :
      EuclideanSpace ℝ (Fin nr × Fin nc))) 2 (P.prod Pe) ∧
    (∫ z, WMFKI.frobenius (E z)^2 ∂P.prod Pe) ≤
      3*((nc : ℝ)*kernelObservationConstant W B G H C A R*q+Q*e+S) := by
  let Dobs := independentObservationSamples P Pe N nt R q (particleGrid N d nt τ X) ε hxm hεm hxl hεl hxR hεq
  have ho := observed_dictionary_moment (P.prod Pe) nr nc N nt d hnr hN R q hR hq Dobs w τ W hw ψ φ atom
    G H J C A B hG hH hC hA hφ hψ hm hg hLip
  let Ad := discreteDictionaryDesign nr N nt d nc w τ atom φ ψ (particleGrid N d nt τ X)
  let Ac := continuousDictionaryDesign nr N d nc atom φ ψ T X
  have hqp : MemLp (fun z : Ω × Ξ => (WithLp.toLp 2 (fun am : Fin nr × Fin nc =>
      (Ad z.1-Ac z.1) am.1 am.2) : EuclideanSpace ℝ (Fin nr × Fin nc))) 2 (P.prod Pe) :=
    hql.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := Pe))
  have hcp : MemLp (fun z : Ω × Ξ => (WithLp.toLp 2 (fun am : Fin nr × Fin nc =>
      (Ac z.1-Aref) am.1 am.2) : EuclideanSpace ℝ (Fin nr × Fin nc))) 2 (P.prod Pe) :=
    hcl.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := Pe))
  have hQp : (∫ z : Ω × Ξ, WMFKI.frobenius (Ad z.1-Ac z.1)^2 ∂P.prod Pe) ≤ Q*e := by
    rw [integral_fun_fst (fun ω => WMFKI.frobenius (Ad ω-Ac ω)^2)]
    simpa using hqQ
  have hSp : (∫ z : Ω × Ξ, WMFKI.frobenius (Ac z.1-Aref)^2 ∂P.prod Pe) ≤ S := by
    rw [integral_fun_fst (fun ω => WMFKI.frobenius (Ac ω-Aref)^2)]
    simpa using hcS
  exact three_matrix_errors (P.prod Pe) nr nc
    (discreteDictionaryDesign nr N nt d nc w τ atom φ ψ (fun t i z => particleGrid N d nt τ X t i z.1+ε t i z.2))
    (fun z => Ad z.1) (fun z => Ac z.1) (fun _ => Aref) ho.1 hqp hcp _ _ _ ho.2 hQp hSp

/-- 三予算を共通定数の標準D0形へまとめる。 -/
theorem design_budget_common_constant (N : ℕ) (U V W e q : ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (he : 0 ≤ e) (hq : 0 ≤ q) :
    3*(U*q+V*e+W/(N : ℝ)) ≤ 3*(U+V+W)*(1/(N : ℝ)+e+q) := by
  have hn : 0 ≤ (1 : ℝ)/(N : ℝ) := by positivity
  have hu := mul_le_mul_of_nonneg_left (show q ≤ 1/(N : ℝ)+e+q by linarith) hU
  have hv := mul_le_mul_of_nonneg_left (show e ≤ 1/(N : ℝ)+e+q by linarith) hV
  have hw := mul_le_mul_of_nonneg_left (show 1/(N : ℝ) ≤ 1/(N : ℝ)+e+q by linarith) hW
  rw [mul_one_div] at hw
  nlinarith

end WMFKIObservedDesign
