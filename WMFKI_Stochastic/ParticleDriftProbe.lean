import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

open scoped BigOperators
namespace WMFKIExternalProbe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def particleDrift {N : ℕ} (K : E → E) (x : Fin N → E) (i : Fin N) : E :=
  (N : ℝ)⁻¹ • ∑ j, if i = j then 0 else K (x i - x j)

theorem mean_norm_sq_le {N : ℕ} (hN : 0 < N) (a : Fin N → E) :
    ‖(N : ℝ)⁻¹ • ∑ j, a j‖ ^ 2 ≤ (N : ℝ)⁻¹ * ∑ j, ‖a j‖ ^ 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : ‖∑ j, a j‖ ^ 2 ≤ (N : ℝ) * ∑ j, ‖a j‖ ^ 2 := by
    calc
      _ ≤ (∑ j, ‖a j‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr
          (norm_sum_le _ _)
      _ ≤ _ := by
        simpa [mul_comm] using (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun j : Fin N => ‖a j‖) (fun _ => (1 : ℝ)))
  calc
    _ = ((N : ℝ)⁻¹)^2 * ‖∑ j, a j‖^2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), mul_pow]
    _ ≤ ((N : ℝ)⁻¹)^2 * ((N : ℝ) * ∑ j, ‖a j‖^2) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = _ := by field_simp

/-- Squared Lipschitz constant 4 L², independent of the number of particles.
Self-interactions are excluded; no value of K at zero is assumed. -/
theorem particleDrift_lipschitz_sq {N : ℕ} (hN : 0 < N)
    (K : E → E) (L : ℝ) (hL : 0 ≤ L)
    (hK : ∀ u v, ‖K u - K v‖ ≤ L * ‖u - v‖)
    (x y : Fin N → E) :
    (∑ i, ‖particleDrift K x i - particleDrift K y i‖^2) ≤
      4 * L^2 * ∑ i, ‖x i - y i‖^2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  let a := fun i j => (if i = j then 0 else K (x i - x j)) -
    (if i = j then 0 else K (y i - y j))
  have ha i j : ‖a i j‖^2 ≤ 2 * L^2 * (‖x i - y i‖^2 + ‖x j - y j‖^2) := by
    by_cases hij : i = j
    · simp only [a, ite_eq_left hij, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      positivity
    · have he : (x i - x j) - (y i - y j) = (x i - y i) - (x j - y j) := by abel
      have hb : ‖a i j‖ ≤ L * (‖x i - y i‖ + ‖x j - y j‖) := by
        simpa only [a, ite_eq_right hij] using (hK (x i - x j) (y i - y j)).trans
          (mul_le_mul_of_nonneg_left (he ▸ norm_sub_le (x i - y i) (x j - y j)) hL)
      have hs := (sq_le_sq₀ (norm_nonneg (a i j))
        (mul_nonneg hL (add_nonneg (norm_nonneg _) (norm_nonneg _)))).mpr hb
      nlinarith [mul_nonneg (sq_nonneg L)
        (sq_nonneg (‖x i - y i‖ - ‖x j - y j‖))]
  have hrow i : ‖particleDrift K x i - particleDrift K y i‖^2 ≤
      (N : ℝ)⁻¹ * ∑ j, 2 * L^2 * (‖x i - y i‖^2 + ‖x j - y j‖^2) := by
    have he : particleDrift K x i - particleDrift K y i = (N : ℝ)⁻¹ • ∑ j, a i j := by
      simp only [particleDrift, a, Finset.sum_sub_distrib, smul_sub]
    rw [he]
    exact (mean_norm_sq_le hN (a i)).trans
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ha i j) (le_of_lt (inv_pos.mpr hn)))
  calc
    _ ≤ ∑ i, (N : ℝ)⁻¹ * ∑ j, 2 * L^2 * (‖x i - y i‖^2 + ‖x j - y j‖^2) :=
      Finset.sum_le_sum fun i _ => hrow i
    _ = _ := by
      simp_rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp_rw [← Finset.mul_sum]
      field_simp
      ring

/-- The componentwise growth estimate, with constants independent of N. -/
theorem particleDrift_growth {N : ℕ} (hN : 0 < N) (K : E → E)
    (G : ℝ) (hG : 0 ≤ G) (hK : ∀ z, ‖K z‖ ≤ G * (1 + ‖z‖))
    (x : Fin N → E) (i : Fin N) :
    ‖particleDrift K x i‖ ≤ G * (1 + ‖x i‖ + (N : ℝ)⁻¹ * ∑ j, ‖x j‖) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hj j : ‖(if i = j then 0 else K (x i - x j))‖ ≤ G * (1 + ‖x i‖ + ‖x j‖) := by
    by_cases hij : i = j
    · simp only [ite_eq_left hij, norm_zero]
      positivity
    · simp only [ite_eq_right hij]
      have hh := (hK (x i - x j)).trans
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl (norm_sub_le (x i) (x j))) hG)
      simpa only [add_assoc] using hh
  rw [particleDrift, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ j, G * (1 + ‖x i‖ + ‖x j‖) :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
        (Finset.sum_le_sum fun j _ => hj j)) (le_of_lt (inv_pos.mpr hn))
    _ = _ := by
      simp_rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

end WMFKIExternalProbe
#print axioms WMFKIExternalProbe.particleDrift_lipschitz_sq
#print axioms WMFKIExternalProbe.particleDrift_growth
