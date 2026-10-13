import WMFKI_Stochastic.NormalizedWeakResidual
import Mathlib.Probability.Independence.Integration

open MeasureTheory Set
open scoped BigOperators
namespace WMFKIExternalProbe

theorem two_vector_l2_moment {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Measure Ω)
    (f g : Ω → E) (hf : MemLp f 2 P) (hg : MemLp g 2 P)
    (A B : ℝ) (hA : (∫ ω, ‖f ω‖^2 ∂P) ≤ A) (hB : (∫ ω, ‖g ω‖^2 ∂P) ≤ B) :
    MemLp (fun ω => f ω+g ω) 2 P ∧ (∫ ω, ‖f ω+g ω‖^2 ∂P) ≤ 2*(A+B) := by
  have hi := hf.add hg
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ ω, 2*(‖f ω‖^2+‖g ω‖^2) ∂P := by
      apply integral_mono_ae hi.norm.integrable_sq
        ((hf.norm.integrable_sq.add hg.norm.integrable_sq).const_mul 2)
      apply ae_of_all
      intro ω
      have hh := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (norm_add_le (f ω) (g ω))
      change ‖f ω+g ω‖^2 ≤ 2*(‖f ω‖^2+‖g ω‖^2)
      nlinarith [sq_nonneg (‖f ω‖-‖g ω‖)]
    _ = 2*((∫ ω, ‖f ω‖^2 ∂P)+(∫ ω, ‖g ω‖^2 ∂P)) := by
      rw [integral_const_mul,integral_add hf.norm.integrable_sq hg.norm.integrable_sq]
    _ ≤ _ := by linarith

theorem stable_weighted_l2_moment {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (w : ι → ℝ) (f : ι → Ω → ℝ)
    (hf : ∀ i, MemLp (f i) 2 P) (C : ℝ) (hC : ∀ i, (∫ ω, (f i ω)^2 ∂P) ≤ C) :
    MemLp (fun ω => ∑ i,w i*f i ω) 2 P ∧
      (∫ ω, (∑ i,w i*f i ω)^2 ∂P) ≤ (∑ i,|w i|)^2*C := by
  classical
  have hi : MemLp (fun ω => ∑ i,w i*f i ω) 2 P :=
    memLp_finsetSum _ (fun i _ => (hf i).const_mul (w i))
  have hs : 0 ≤ ∑ i,|w i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ ω, (∑ i,|w i|)*(∑ i,|w i| * (f i ω)^2) ∂P := by
      apply integral_mono_ae hi.integrable_sq
        ((integrable_finsetSum _ (fun i _ => (hf i).integrable_sq.const_mul |w i|)).const_mul _)
      apply ae_of_all
      intro ω
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
        (fun i _ => abs_nonneg (w i)) (fun i _ => mul_nonneg (abs_nonneg (w i)) (sq_nonneg (f i ω)))
      intro i _
      rw [mul_pow]
      nlinarith [sq_abs (w i)]
    _ = (∑ i,|w i|)*(∑ i,|w i| * (∫ ω,(f i ω)^2 ∂P)) := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => (hf i).integrable_sq.const_mul |w i|)]
      simp_rw [integral_const_mul]
    _ ≤ (∑ i,|w i|)*(∑ i,|w i| * C) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hC i) (abs_nonneg _))) hs
    _ = _ := by rw [←Finset.sum_mul]; ring

/-- Unlike the centered Brownian case, observation perturbations need not be centered. -/
theorem normalized_vector_second_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (L : ℕ)
    (r : Fin L → Ω → ℝ) (hr : ∀ a, MemLp (r a) 2 P)
    (C : ℝ) (hv : ∀ a, (∫ ω,(r a ω)^2 ∂P) ≤ C) (hL : 0 < L) :
    MemLp (normalizedTestVector L r) 2 P ∧ (∫ ω, ‖normalizedTestVector L r ω‖^2 ∂P) ≤ C := by
  have hV : MemLp (normalizedTestVector L r) 2 P :=
    MemLp.of_eval_piLp (fun a => (hr a).const_mul (1/Real.sqrt (L : ℝ)))
  have hn ω : ‖normalizedTestVector L r ω‖^2 = (1/(L : ℝ))*∑ a,(r a ω)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ a, ((1/Real.sqrt (L : ℝ))*r a ω)^2) = _
    simp_rw [mul_pow]
    rw [←Finset.mul_sum,div_pow,one_pow,Real.sq_sqrt (Nat.cast_nonneg L)]
  refine ⟨hV,?_⟩
  simp_rw [hn]
  rw [integral_const_mul,integral_finsetSum _ (fun a _ => (hr a).integrable_sq)]
  calc
    _ ≤ (1/(L : ℝ))*∑ _ : Fin L,C := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun a _ => hv a)) (one_div_nonneg.mpr (Nat.cast_nonneg L))
    _ = C := by simp; field_simp

theorem real_l2_domination {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f H : Ω → ℝ) (hm : Measurable f) (hH : MemLp H 2 P)
    (hb : ∀ ω, |f ω| ≤ H ω) (C : ℝ) (hC : (∫ ω,(H ω)^2 ∂P) ≤ C) :
    MemLp f 2 P ∧ (∫ ω,(f ω)^2 ∂P) ≤ C := by
  have hi : MemLp f 2 P := hH.of_le hm.aestronglyMeasurable (ae_of_all _ (fun ω => by
    simpa only [Real.norm_eq_abs] using (hb ω).trans (le_abs_self (H ω))))
  refine ⟨hi,?_⟩
  apply le_trans (integral_mono_ae hi.integrable_sq hH.integrable_sq ?_) hC
  apply ae_of_all
  intro ω
  have hh := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr ((hb ω).trans (le_abs_self _))
  simpa only [sq_abs] using hh

end WMFKIExternalProbe
