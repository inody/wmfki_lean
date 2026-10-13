import WMFKI_Stochastic.ObservationFeaturePerturbation

open MeasureTheory Set
open scoped BigOperators
namespace WMFKIExternalProbe

theorem scalar_observation_difference_moment {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (u : E → ℝ) (hu : Measurable u) (C : ℝ)
    (hlip : ∀ x y, |u x-u y| ≤ C*‖x-y‖)
    (x e : Ω → E) (hxm : Measurable x) (hem : Measurable e) (he : MemLp e 2 P)
    (q : ℝ) (heq : (∫ ω, ‖e ω‖^2 ∂P) ≤ q) :
    MemLp (fun ω => u (x ω+e ω)-u (x ω)) 2 P ∧
      (∫ ω,(u (x ω+e ω)-u (x ω))^2 ∂P) ≤ C^2*q := by
  apply real_l2_domination P _ (fun ω => C*‖e ω‖)
    ((hu.comp (hxm.add hem)).sub (hu.comp hxm)) (he.norm.const_mul C)
    (fun ω => by simpa using hlip (x ω+e ω) (x ω))
  simp only [mul_pow]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left heq (sq_nonneg C)

noncomputable def particleTimeAverage {Ω : Type*} (N nt : ℕ) (w : Fin nt → ℝ)
    (f : Fin nt → Fin N → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ t,w t*((N : ℝ)⁻¹*∑ i,f t i ω)

noncomputable def pairTimeAverage {Ω : Type*} (N nt : ℕ) (w : Fin nt → ℝ)
    (f : Fin nt → Fin N → Fin N → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ t,w t*((N : ℝ)⁻¹^2*∑ i,∑ j,if i=j then 0 else f t i j ω)

theorem particle_time_average_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (N nt : ℕ) (hN : 0 < N) (w : Fin nt → ℝ)
    (f : Fin nt → Fin N → Ω → ℝ) (hf : ∀ t i,MemLp (f t i) 2 P)
    (C : ℝ) (hb : ∀ t i,(∫ ω,(f t i ω)^2 ∂P) ≤ C) :
    MemLp (particleTimeAverage N nt w f) 2 P ∧
    (∫ ω,(particleTimeAverage N nt w f ω)^2 ∂P) ≤ (∑ t,|w t|)^2*C := by
  have ha t := average_l2_moment hN (f t) (hf t) C (hb t)
  exact stable_weighted_l2_moment P w _ (fun t => (ha t).1) C (fun t => (ha t).2)

theorem pair_time_average_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (N nt : ℕ) (hN : 0 < N) (w : Fin nt → ℝ)
    (f : Fin nt → Fin N → Fin N → Ω → ℝ) (hf : ∀ t i j,MemLp (f t i j) 2 P)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t i j,(∫ ω,(f t i j ω)^2 ∂P) ≤ C) :
    MemLp (pairTimeAverage N nt w f) 2 P ∧
    (∫ ω,(pairTimeAverage N nt w f ω)^2 ∂P) ≤ (∑ t,|w t|)^2*C := by
  classical
  let F := fun t i j ω => if i=j then (0 : ℝ) else f t i j ω
  have hF t i j : MemLp (F t i j) 2 P := by
    by_cases h : i=j
    · simp [F,h]
    · simpa only [F,h,ite_false] using hf t i j
  have hFB t i j : (∫ ω,(F t i j ω)^2 ∂P) ≤ C := by
    by_cases h : i=j
    · simpa only [F,h,ite_true,zero_pow (by decide : (2 : ℕ) ≠ 0),integral_zero] using hC
    · simpa only [F,h,ite_false] using hb t i j
  have hi t i := average_l2_moment hN (F t i) (hF t i) C (hFB t i)
  have hrow t := average_l2_moment hN _ (fun i => (hi t i).1) C (fun i => (hi t i).2)
  have h := stable_weighted_l2_moment P w _ (fun t => (hrow t).1) C (fun t => (hrow t).2)
  have he : (fun ω => ∑ t,w t*((N : ℝ)⁻¹*∑ i,(N : ℝ)⁻¹*∑ j,F t i j ω)) = pairTimeAverage N nt w f := by
    funext ω
    unfold pairTimeAverage
    apply Finset.sum_congr rfl
    intro t _
    rw [←Finset.mul_sum]
    simp only [F]
    ring
  rw [←he]
  exact h

end WMFKIExternalProbe
