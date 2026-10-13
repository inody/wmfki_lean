import WMFKI_Stochastic.ParticleEnvelopeMoments

open MeasureTheory
open scoped BigOperators
namespace WMFKIExternalProbe

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem integrable_fourth {f : Ω → ℝ} (hf : MemLp f 4 P) :
    Integrable (fun ω => (f ω)^4) P := by
  simpa only [Real.norm_eq_abs, (show Even (4 : ℕ) from by decide).pow_abs] using
    hf.integrable_norm_pow (p := 4) (by decide)

theorem fourth_two_le (a b : ℝ) : (a+b)^4 ≤ 8*(a^4+b^4) := by
  have h : (a+b)^2 ≤ 2*(a^2+b^2) := by nlinarith [sq_nonneg (a-b)]
  have hh := pow_le_pow_left₀ (sq_nonneg (a+b)) h 2
  nlinarith [sq_nonneg (a^2-b^2)]

theorem fourth_three_le (a b c : ℝ) : (a+b+c)^4 ≤ 27*(a^4+b^4+c^4) := by
  have h : (a+b+c)^2 ≤ 3*(a^2+b^2+c^2) := by
    nlinarith [sq_nonneg (a-b),sq_nonneg (a-c),sq_nonneg (b-c)]
  have hh := pow_le_pow_left₀ (sq_nonneg (a+b+c)) h 2
  have h' : (a^2+b^2+c^2)^2 ≤ 3*(a^4+b^4+c^4) := by
    nlinarith [sq_nonneg (a^2-b^2),sq_nonneg (a^2-c^2),sq_nonneg (b^2-c^2)]
  nlinarith only [hh,h']

theorem three_l4_moment (f g h : Ω → ℝ)
    (hf : MemLp f 4 P) (hg : MemLp g 4 P) (hh : MemLp h 4 P)
    (A B C : ℝ) (hA : (∫ ω, (f ω)^4 ∂P) ≤ A)
    (hB : (∫ ω, (g ω)^4 ∂P) ≤ B) (hC : (∫ ω, (h ω)^4 ∂P) ≤ C) :
    MemLp (fun ω => f ω+g ω+h ω) 4 P ∧
    (∫ ω, (f ω+g ω+h ω)^4 ∂P) ≤ 27*(A+B+C) := by
  have hi := (hf.add hg).add hh
  have hfi := integrable_fourth hf
  have hgi := integrable_fourth hg
  have hhi := integrable_fourth hh
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ ω, 27*((f ω)^4+(g ω)^4+(h ω)^4) ∂P :=
      integral_mono (integrable_fourth hi) (((hfi.add hgi).add hhi).const_mul 27)
        (fun ω => fourth_three_le (f ω) (g ω) (h ω))
    _ = 27*((∫ ω, (f ω)^4 ∂P)+(∫ ω, (g ω)^4 ∂P)+(∫ ω, (h ω)^4 ∂P)) := by
      rw [integral_const_mul, integral_add (f := fun ω => (f ω)^4+(g ω)^4)
        (g := fun ω => (h ω)^4) (hfi.add hgi) hhi, integral_add hfi hgi]
    _ ≤ _ := by linarith

theorem mean_fourth_le {N : ℕ} (hN : 0 < N) (a : Fin N → ℝ) :
    ((N : ℝ)⁻¹ * ∑ i, a i)^4 ≤ (N : ℝ)⁻¹ * ∑ i, (a i)^4 := by
  have h1 : ((N : ℝ)⁻¹ * ∑ i, a i)^2 ≤ (N : ℝ)⁻¹ * ∑ i, (a i)^2 := by
    simpa only [Real.norm_eq_abs,sq_abs,smul_eq_mul] using mean_norm_sq_le hN a
  have h2 : ((N : ℝ)⁻¹ * ∑ i, (a i)^2)^2 ≤ (N : ℝ)⁻¹ * ∑ i, (a i)^4 := by
    have hh := mean_norm_sq_le hN (fun i => (a i)^2)
    simp only [Real.norm_eq_abs,sq_abs,smul_eq_mul] at hh
    simpa only [← pow_mul] using hh
  simpa only [← pow_mul] using (pow_le_pow_left₀ (sq_nonneg _) h1 2).trans h2

theorem average_l4_moment {N : ℕ} (hN : 0 < N) (a : Fin N → Ω → ℝ)
    (ha : ∀ i, MemLp (a i) 4 P) (A : ℝ) (hA : ∀ i, (∫ ω, (a i ω)^4 ∂P) ≤ A) :
    let m := fun ω => (N : ℝ)⁻¹ * ∑ i, a i ω
    MemLp m 4 P ∧ (∫ ω, (m ω)^4 ∂P) ≤ A := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hm := (memLp_finsetSum Finset.univ (fun i _ => ha i)).const_mul ((N : ℝ)⁻¹)
  refine ⟨hm,?_⟩
  calc
    _ ≤ ∫ ω, (N : ℝ)⁻¹ * ∑ i, (a i ω)^4 ∂P :=
      integral_mono (integrable_fourth hm)
        ((integrable_finsetSum _ (fun i _ => integrable_fourth (ha i))).const_mul _)
        (fun ω => mean_fourth_le hN (fun i => a i ω))
    _ = (N : ℝ)⁻¹ * ∑ i, ∫ ω, (a i ω)^4 ∂P := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => integrable_fourth (ha i))]
    _ ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, A := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ => hA i) (le_of_lt (inv_pos.mpr hn))
    _ = A := by simp; field_simp

theorem comparison_envelope_l4 {N : ℕ} (hN : 0 < N) (a : Fin N → Ω → ℝ)
    (ha : ∀ i, MemLp (a i) 4 P) (A : ℝ) (hA : ∀ i, (∫ ω, (a i ω)^4 ∂P) ≤ A)
    (c e : ℝ) (i : Fin N) :
    let F := fun ω => (a i ω+c*((N : ℝ)⁻¹ * ∑ j, a j ω))*e
    MemLp F 4 P ∧ (∫ ω, (F ω)^4 ∂P) ≤ 8*e^4*(1+c^4)*A := by
  obtain ⟨hm,hmb⟩ := average_l4_moment hN a ha A hA
  let m := fun ω => (N : ℝ)⁻¹ * ∑ j, a j ω
  have hF := ((ha i).add (hm.const_mul c)).mul_const e
  refine ⟨hF,?_⟩
  calc
    _ ≤ ∫ ω, (8*e^4)*((a i ω)^4+c^4*(m ω)^4) ∂P := by
      apply integral_mono (integrable_fourth hF)
        (((integrable_fourth (ha i)).add ((integrable_fourth hm).const_mul (c^4))).const_mul _)
      intro ω
      change ((a i ω+c*m ω)*e)^4 ≤ (8*e^4)*((a i ω)^4+c^4*(m ω)^4)
      convert mul_le_mul_of_nonneg_right (fourth_two_le (a i ω) (c*m ω)) (by positivity : 0 ≤ e^4) using 1 <;> ring
    _ = (8*e^4)*((∫ ω, (a i ω)^4 ∂P)+c^4*(∫ ω, (m ω)^4 ∂P)) := by
      rw [integral_const_mul, integral_add (integrable_fourth (ha i)) ((integrable_fourth hm).const_mul (c^4)),
        integral_const_mul]
    _ ≤ (8*e^4)*(A+c^4*A) := mul_le_mul_of_nonneg_left
      (add_le_add (hA i) (mul_le_mul_of_nonneg_left hmb (by positivity))) (by positivity)
    _ = _ := by ring

end WMFKIExternalProbe
