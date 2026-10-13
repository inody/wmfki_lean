import WMFKI_Stochastic.IndependentFourthAlgebra

open MeasureTheory ProbabilityTheory

namespace WMFKIIndependentFourth
variable {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- 同じ2次・4次モーメントを持つ中心化独立変数の有限和の正確な式。 -/
theorem finite_centered_fourth_formula (s : Finset I) {X : I → Ω → ℝ}
    (hI : iIndepFun X P) (hm : ∀ i, Measurable (X i)) (hL : ∀ i, MemLp (X i) 4 P)
    (h0 : ∀ i, (∫ ω, X i ω ∂P) = 0) (v k : ℝ)
    (h2 : ∀ i, (∫ ω, X i ω^2 ∂P) = v) (h4 : ∀ i, (∫ ω, X i ω^4 ∂P) = k) :
    (∫ ω, (∑ i ∈ s, X i ω)^2 ∂P) = (s.card : ℝ)*v ∧
    (∫ ω, (∑ i ∈ s, X i ω)^4 ∂P) =
      (s.card : ℝ)*k + 3*(s.card : ℝ)*((s.card : ℝ)-1)*v^2 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
    let S := fun ω => ∑ j ∈ s, X j ω
    have hs : MemLp S 4 P := memLp_finsetSum s (fun j _ => hL j)
    have hs0 : (∫ ω, S ω ∂P) = 0 := by
      rw [show S = (fun ω => ∑ j ∈ s, X j ω) from rfl,
        integral_finsetSum s (fun j _ => (hL j).integrable (by norm_num))]
      simp [h0]
    have hsi : IndepFun S (X i) P := by
      have he : (∑ j ∈ s, X j) = S := by ext ω; simp [S]
      rw [← he]
      exact hI.indepFun_finsetSum_of_notMem hm hi
    simp_rw [Finset.sum_insert hi]
    rw [independent_centered_second_add (hL i) hs hsi.symm (h0 i) hs0,
      independent_centered_fourth_add (hL i) hs hsi.symm (h0 i) hs0, h2 i, h4 i]
    change v + (∫ ω, (∑ j ∈ s, X j ω)^2 ∂P) = _ ∧
      k + 6*v*(∫ ω, (∑ j ∈ s, X j ω)^2 ∂P) + (∫ ω, (∑ j ∈ s, X j ω)^4 ∂P) = _
    rw [ih.1, ih.2, Finset.card_insert_of_notMem hi]
    push_cast
    constructor <;> ring

/-- 母集団核のL4と中心化から上の式の入力を導く。 -/
theorem iid_centered_kernel_fourth_formula {E : Type*} [MeasurableSpace E]
    (ρ : Measure E) (s : Finset I) {X : I → Ω → E}
    (hI : iIndepFun X P) (hm : ∀ i, Measurable (X i)) (hLaw : ∀ i, HasLaw (X i) ρ P)
    (f : E → ℝ) (hf : Measurable f) (hL : MemLp f 4 ρ) (h0 : (∫ x, f x ∂ρ) = 0) :
    MemLp (fun ω => ∑ i ∈ s, f (X i ω)) 4 P ∧
    (∫ ω, (∑ i ∈ s, f (X i ω))^4 ∂P) = (s.card : ℝ)*(∫ x, f x^4 ∂ρ) +
      3*(s.card : ℝ)*((s.card : ℝ)-1)*(∫ x, f x^2 ∂ρ)^2 := by
  have hp i : MemLp (fun ω => f (X i ω)) 4 P := (hLaw i).memLp_fun_comp hL
  refine ⟨memLp_finsetSum s (fun i _ => hp i), ?_⟩
  apply (finite_centered_fourth_formula s (hI.comp (fun _ => f) (fun _ => hf))
    (fun i => hf.comp (hm i)) hp ?_ (∫ x, f x^2 ∂ρ) (∫ x, f x^4 ∂ρ) ?_ ?_).2
  · intro i
    exact ((hLaw i).integral_comp hf.aestronglyMeasurable).trans h0
  · intro i
    exact (hLaw i).integral_comp (hf.pow_const 2).aestronglyMeasurable
  · intro i
    exact (hLaw i).integral_comp (hf.pow_const 4).aestronglyMeasurable

/-- 空和も含めて、中心化iid和の4次モーメントは3 n² E[f⁴]以下。 -/
theorem iid_centered_kernel_fourth_bound {E : Type*} [MeasurableSpace E]
    (ρ : Measure E) [IsProbabilityMeasure ρ] (s : Finset I) {X : I → Ω → E}
    (hI : iIndepFun X P) (hm : ∀ i, Measurable (X i)) (hLaw : ∀ i, HasLaw (X i) ρ P)
    (f : E → ℝ) (hf : Measurable f) (hL : MemLp f 4 ρ) (h0 : (∫ x, f x ∂ρ) = 0) :
    MemLp (fun ω => ∑ i ∈ s, f (X i ω)) 4 P ∧
    (∫ ω, (∑ i ∈ s, f (X i ω))^4 ∂P) ≤
      3*(s.card : ℝ)^2*(∫ x, f x^4 ∂ρ) := by
  obtain ⟨hp,he⟩ := iid_centered_kernel_fourth_formula ρ s hI hm hLaw f hf hL h0
  refine ⟨hp, ?_⟩
  rw [he]
  by_cases hz : s.card = 0
  · simp [hz]
  have hn : (1 : ℝ) ≤ s.card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
  have hk : 0 ≤ ∫ x, f x^4 ∂ρ := integral_nonneg (fun _ => by positivity)
  have hv := second_moment_sq_le_fourth hL
  have ht := mul_le_mul_of_nonneg_left hv
    (show 0 ≤ 3*(s.card : ℝ)*((s.card : ℝ)-1) by positivity)
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ s.card by positivity) hk]

end WMFKIIndependentFourth
