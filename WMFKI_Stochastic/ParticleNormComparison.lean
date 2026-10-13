import WMFKI_Stochastic.ParticlePathComparison

open MeasureTheory Set
open scoped BigOperators
namespace WMFKIExternalProbe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem particleDrift_path_continuous {N : ℕ} (K : E → E) (hK : Continuous K)
    (x : Fin N → ℝ → E) (hc : ∀ i, Continuous (x i)) (i : Fin N) :
    Continuous (fun t => particleDrift K (fun j => x j t) i) := by
  classical
  unfold particleDrift
  apply Continuous.const_smul
  apply continuous_finsetSum
  intro j _
  by_cases h : i = j
  · simpa only [ite_eq_left h] using (continuous_const : Continuous (fun _ : ℝ => (0 : E)))
  · simpa only [ite_eq_right h, Function.comp_def, Pi.sub_apply] using hK.comp ((hc i).sub (hc j))

/-- A pathwise estimate of the actual integral equation. All drift integrals
are integrable by continuity; no default value for a divergent integral is used. -/
theorem particle_norm_comparison {N : ℕ} (hN : 0 < N)
    (K : E → E) (hKc : Continuous K) (G : ℝ) (hG : 0 ≤ G)
    (hK : ∀ z, ‖K z‖ ≤ G*(1+‖z‖))
    (x w : Fin N → ℝ → E) (ξ : Fin N → E) (σ T : ℝ) (hT : 0 ≤ T)
    (hc : ∀ i, Continuous (x i)) (H : Fin N → ℝ) (hH : ∀ i, 0 ≤ H i)
    (hw : ∀ i t, t ∈ Icc 0 T → ‖w i t‖ ≤ H i)
    (he : ∀ i t, t ∈ Icc 0 T → x i t = ξ i +
      (∫ s in 0..t, particleDrift K (fun j => x j s) i) + σ • w i t) :
    let a := fun i => ‖ξ i‖ + |σ| * H i + (G+1)*T
    ∀ i t, t ∈ Icc 0 T → ‖x i t‖ ≤
      (a i + (G+1)*T*((N : ℝ)⁻¹ * ∑ j, a j)*Real.exp (2*(G+1)*T))*Real.exp ((G+1)*T) := by
  let u := fun i t => ‖x i t‖
  let m := fun t => (N : ℝ)⁻¹ * ∑ j, u j t
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have huc i : Continuous (u i) := (hc i).norm
  have hmc : Continuous m := (continuous_finsetSum _ (fun i _ => huc i)).const_mul _
  have hmn s : 0 ≤ m s := mul_nonneg (le_of_lt (inv_pos.mpr hn))
    (Finset.sum_nonneg fun i _ => norm_nonneg _)
  apply particle_path_comparison hN u _ (G+1) T (by positivity) hT
    (fun i => (huc i).continuousOn)
  · intro i
    have hh := hH i
    positivity
  · intro i t ht
    have hdi : IntervalIntegrable (fun s => particleDrift K (fun j => x j s) i) volume 0 t :=
      (particleDrift_path_continuous K hKc x hc i).intervalIntegrable 0 t
    have hub : IntervalIntegrable (fun s => G*(1+u i s+m s)) volume 0 t :=
      (((continuous_const.add (huc i)).add hmc).const_mul G).intervalIntegrable 0 t
    have hint := intervalIntegral.integral_mono_on ht.1 hdi.norm hub
      (fun s _ => particleDrift_growth hN K G hG hK (fun j => x j s) i)
    have hlin : (∫ s in 0..t, G*(1+u i s+m s)) = G*t + G*(∫ s in 0..t, u i s+m s) := by
      simp_rw [add_assoc]
      have hiu : IntervalIntegrable (fun s => u i s + m s) volume 0 t :=
        ((huc i).add hmc).intervalIntegrable 0 t
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (f := fun _ : ℝ => (1 : ℝ))
          (g := fun s => u i s + m s) intervalIntegrable_const hiu]
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
      ring
    rw [hlin] at hint
    have hwi : ‖σ • w i t‖ ≤ |σ| * H i := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hw i t ht) (abs_nonneg _)
    have htri : ‖x i t‖ ≤ ‖ξ i‖ + ‖∫ s in 0..t, particleDrift K (fun j => x j s) i‖ + ‖σ • w i t‖ := by
      rw [he i t ht]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    have hni := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun s => particleDrift K (fun j => x j s) i) ht.1
    have hpos : 0 ≤ ∫ s in 0..t, u i s + m s :=
      intervalIntegral.integral_nonneg_of_forall ht.1 (fun s => add_nonneg (norm_nonneg _) (hmn s))
    change ‖x i t‖ ≤ (‖ξ i‖ + |σ| * H i + (G+1)*T) + (G+1)*(∫ s in 0..t, u i s+m s)
    nlinarith [mul_le_mul_of_nonneg_left ht.2 hG]

end WMFKIExternalProbe
#print axioms WMFKIExternalProbe.particle_norm_comparison
