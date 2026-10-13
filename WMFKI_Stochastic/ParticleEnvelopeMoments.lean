import WMFKI_Stochastic.ParticleDriftProbe
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
open scoped BigOperators
namespace WMFKIExternalProbe

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem three_l2_moment (f g h : Ω → ℝ)
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) (hh : MemLp h 2 P)
    (A B C : ℝ) (hA : (∫ ω, (f ω)^2 ∂P) ≤ A)
    (hB : (∫ ω, (g ω)^2 ∂P) ≤ B) (hC : (∫ ω, (h ω)^2 ∂P) ≤ C) :
    MemLp (fun ω => f ω + g ω + h ω) 2 P ∧
    (∫ ω, (f ω + g ω + h ω)^2 ∂P) ≤ 3*(A+B+C) := by
  have hi := (hf.add hg).add hh
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ ω, 3*((f ω)^2+(g ω)^2+(h ω)^2) ∂P := by
      apply integral_mono hi.integrable_sq (((hf.integrable_sq.add hg.integrable_sq).add hh.integrable_sq).const_mul 3)
      intro ω
      change (f ω+g ω+h ω)^2 ≤ 3*((f ω)^2+(g ω)^2+(h ω)^2)
      nlinarith [sq_nonneg (f ω-g ω),sq_nonneg (f ω-h ω),sq_nonneg (g ω-h ω)]
    _ = 3*((∫ ω, (f ω)^2 ∂P)+(∫ ω, (g ω)^2 ∂P)+(∫ ω, (h ω)^2 ∂P)) := by
      rw [integral_const_mul, integral_add (f := fun ω => (f ω)^2+(g ω)^2)
          (g := fun ω => (h ω)^2) (hf.integrable_sq.add hg.integrable_sq) hh.integrable_sq,
        integral_add hf.integrable_sq hg.integrable_sq]
    _ ≤ _ := by linarith

theorem average_l2_moment {N : ℕ} (hN : 0 < N) (a : Fin N → Ω → ℝ)
    (ha : ∀ i, MemLp (a i) 2 P) (A : ℝ) (hA : ∀ i, (∫ ω, (a i ω)^2 ∂P) ≤ A) :
    let m := fun ω => (N : ℝ)⁻¹ * ∑ i, a i ω
    MemLp m 2 P ∧ (∫ ω, (m ω)^2 ∂P) ≤ A := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hm := (memLp_finsetSum Finset.univ (fun i _ => ha i)).const_mul ((N : ℝ)⁻¹)
  refine ⟨hm,?_⟩
  calc
    _ ≤ ∫ ω, (N : ℝ)⁻¹ * ∑ i, (a i ω)^2 ∂P := by
      apply integral_mono hm.integrable_sq
        ((integrable_finsetSum _ (fun i _ => (ha i).integrable_sq)).const_mul _)
      intro ω
      simpa only [Real.norm_eq_abs, sq_abs, smul_eq_mul] using mean_norm_sq_le hN (fun i => a i ω)
    _ = (N : ℝ)⁻¹ * ∑ i, ∫ ω, (a i ω)^2 ∂P := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => (ha i).integrable_sq)]
    _ ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, A := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ => hA i) (le_of_lt (inv_pos.mpr hn))
    _ = A := by simp; field_simp

theorem comparison_envelope_l2 {N : ℕ} (hN : 0 < N) (a : Fin N → Ω → ℝ)
    (ha : ∀ i, MemLp (a i) 2 P) (A : ℝ) (hA : ∀ i, (∫ ω, (a i ω)^2 ∂P) ≤ A)
    (c e : ℝ) (i : Fin N) :
    let F := fun ω => (a i ω + c*((N : ℝ)⁻¹ * ∑ j, a j ω))*e
    MemLp F 2 P ∧ (∫ ω, (F ω)^2 ∂P) ≤ 2*e^2*(1+c^2)*A := by
  obtain ⟨hm,hmb⟩ := average_l2_moment hN a ha A hA
  let m := fun ω => (N : ℝ)⁻¹ * ∑ j, a j ω
  have hF := ((ha i).add (hm.const_mul c)).mul_const e
  refine ⟨hF,?_⟩
  calc
    _ ≤ ∫ ω, (2*e^2)*((a i ω)^2+c^2*(m ω)^2) ∂P := by
      apply integral_mono hF.integrable_sq
        (((ha i).integrable_sq.add (hm.integrable_sq.const_mul (c^2))).const_mul _)
      intro ω
      change ((a i ω+c*m ω)*e)^2 ≤ (2*e^2)*((a i ω)^2+c^2*(m ω)^2)
      nlinarith [mul_nonneg (sq_nonneg e) (sq_nonneg (a i ω-c*m ω))]
    _ = (2*e^2)*((∫ ω, (a i ω)^2 ∂P)+c^2*(∫ ω, (m ω)^2 ∂P)) := by
      rw [integral_const_mul, integral_add (ha i).integrable_sq (hm.integrable_sq.const_mul (c^2)),
        integral_const_mul]
    _ ≤ (2*e^2)*(A+c^2*A) := mul_le_mul_of_nonneg_left
      (add_le_add (hA i) (mul_le_mul_of_nonneg_left hmb (sq_nonneg c))) (by positivity)
    _ = _ := by ring

end WMFKIExternalProbe
#print axioms WMFKIExternalProbe.three_l2_moment
#print axioms WMFKIExternalProbe.average_l2_moment
#print axioms WMFKIExternalProbe.comparison_envelope_l2
