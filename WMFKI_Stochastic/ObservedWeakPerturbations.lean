import WMFKI_Stochastic.ObservationSamples

open MeasureTheory Set
open scoped BigOperators
namespace WMFKIExternalProbe

noncomputable def weakResponseIntegrand (d : ℕ) (σ : ℝ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (ψ : ℝ → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (-deriv ψ t)*φ x + (-(σ^2/2)*ψ t)*Laplacian.laplacian φ x

noncomputable def discreteWeakResponse {Ω : Type*} (N nt d : ℕ) (σ : ℝ)
    (w τ : Fin nt → ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ) (ψ : ℝ → ℝ)
    (x : Fin nt → Fin N → Ω → EuclideanSpace ℝ (Fin d)) : Ω → ℝ :=
  particleTimeAverage N nt w (fun t i ω => weakResponseIntegrand d σ φ ψ (τ t) (x t i ω))

noncomputable def discreteKernelDesign {Ω : Type*} (N nt d : ℕ)
    (w τ : Fin nt → ℝ) (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (ψ : ℝ → ℝ)
    (x : Fin nt → Fin N → Ω → EuclideanSpace ℝ (Fin d)) : Ω → ℝ :=
  pairTimeAverage N nt w (fun t i j ω => ψ (τ t)*inner ℝ (gradient φ (x t i ω)) (K (x t i ω-x t j ω)))

theorem scalar_combination_lipschitz {E : Type*} [NormedAddCommGroup E]
    (u v : E → ℝ) (C D a b : ℝ)
    (hu : ∀ x y, |u x-u y| ≤ C*‖x-y‖) (hv : ∀ x y, |v x-v y| ≤ D*‖x-y‖) (x y : E) :
    |(a*u x+b*v x)-(a*u y+b*v y)| ≤ (|a| * C+|b| * D)*‖x-y‖ := by
  have he : (a*u x+b*v x)-(a*u y+b*v y) = a*(u x-u y)+b*(v x-v y) := by ring
  rw [he]
  calc
    _ ≤ |a*(u x-u y)|+|b*(v x-v y)| := abs_add_le _ _
    _ = |a| * |u x-u y|+|b| * |v x-v y| := by rw [abs_mul,abs_mul]
    _ ≤ |a| * (C*‖x-y‖)+|b| * (D*‖x-y‖) := add_le_add
      (mul_le_mul_of_nonneg_left (hu x y) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (hv x y) (abs_nonneg _))
    _ = _ := by ring

theorem weak_response_integrand_lipschitz (d : ℕ) (σ : ℝ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (ψ : ℝ → ℝ) (t : ℝ)
    (G H J B : ℝ) (hG : 0 ≤ G) (hJ : 0 ≤ J) (hφ : C3TestBounds d φ G H J)
    (hψ : |ψ t| ≤ B) (hdψ : |deriv ψ t| ≤ B) (x y : EuclideanSpace ℝ (Fin d)) :
    |weakResponseIntegrand d σ φ ψ t x-weakResponseIntegrand d σ φ ψ t y| ≤
      (B*(G+(σ^2/2)*((d : ℝ)*J)))*‖x-y‖ := by
  have hb := hφ.observation_bounds
  have hh := scalar_combination_lipschitz φ (Laplacian.laplacian φ) G ((d : ℝ)*J)
    (-deriv ψ t) (-(σ^2/2)*ψ t) hb.2.1 hb.2.2.2 x y
  have hc : |-deriv ψ t| * G+|-(σ^2/2)*ψ t| * ((d : ℝ)*J) ≤ B*(G+(σ^2/2)*((d : ℝ)*J)) := by
    rw [abs_neg,abs_mul,abs_neg,abs_of_nonneg (div_nonneg (sq_nonneg σ) (by norm_num))]
    calc
      _ ≤ B*G+((σ^2/2)*B)*((d : ℝ)*J) := add_le_add
        (mul_le_mul_of_nonneg_right hdψ hG)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hψ (by positivity)) (by positivity))
      _ = _ := by ring
  exact hh.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

section Samples
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (N nt d : ℕ) [MeasurableSpace (EuclideanSpace ℝ (Fin d))] [BorelSpace (EuclideanSpace ℝ (Fin d))]
  (R q : ℝ) (D : ObservationSamples (E := EuclideanSpace ℝ (Fin d)) P N nt R q)

omit [IsProbabilityMeasure P] in
theorem discrete_response_observation_moment (hN : 0 < N) (σ : ℝ) (w τ : Fin nt → ℝ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (ψ : ℝ → ℝ)
    (G H J B : ℝ) (hG : 0 ≤ G) (hJ : 0 ≤ J) (hφ : C3TestBounds d φ G H J)
    (hψ : ∀ t, |ψ (τ t)| ≤ B) (hdψ : ∀ t, |deriv ψ (τ t)| ≤ B) :
    let F := fun ω => discreteWeakResponse N nt d σ w τ φ ψ (fun t i ω => D.pos t i ω+D.noise t i ω) ω -
      discreteWeakResponse N nt d σ w τ φ ψ D.pos ω
    MemLp F 2 P ∧ (∫ ω,(F ω)^2 ∂P) ≤
      (∑ t,|w t|)^2*(B*(G+(σ^2/2)*((d : ℝ)*J)))^2*q := by
  dsimp only
  have hc := euclidean_test_derivatives_continuous d φ (hφ.smooth.of_le (by norm_num))
  have hm t : Measurable (weakResponseIntegrand d σ φ ψ (τ t)) :=
    (hφ.smooth.continuous.measurable.const_mul _).add (hc.2.measurable.const_mul _)
  have hp t i := scalar_observation_difference_moment P (weakResponseIntegrand d σ φ ψ (τ t)) (hm t)
    (B*(G+(σ^2/2)*((d : ℝ)*J)))
    (weak_response_integrand_lipschitz d σ φ ψ (τ t) G H J B hG hJ hφ (hψ t) (hdψ t))
    (D.pos t i) (D.noise t i) (D.pos_meas t i) (D.noise_meas t i) (D.noise_lp t i) q (D.noise_moment t i)
  have hh := particle_time_average_moment P N nt hN w _ (fun t i => (hp t i).1) _ (fun t i => (hp t i).2)
  have he : (fun ω => discreteWeakResponse N nt d σ w τ φ ψ (fun t i ω => D.pos t i ω+D.noise t i ω) ω -
      discreteWeakResponse N nt d σ w τ φ ψ D.pos ω) =
      particleTimeAverage N nt w (fun t i ω => weakResponseIntegrand d σ φ ψ (τ t) (D.pos t i ω+D.noise t i ω)-
        weakResponseIntegrand d σ φ ψ (τ t) (D.pos t i ω)) := by
    funext ω
    simp [discreteWeakResponse,particleTimeAverage,Finset.sum_sub_distrib,mul_sub]
  simpa only [←he,mul_assoc] using hh

/-- Directional design perturbation uses the true kernel directly, so the
constant has no explicit support-size or coefficient-vector factor. -/
theorem discrete_kernel_observation_moment (hN : 0 < N) (hq : 0 ≤ q) (hR : 0 ≤ R)
    (w τ : Fin nt → ℝ) (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hKm : Measurable K)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (ψ : ℝ → ℝ)
    (G H J C A B : ℝ) (hG : 0 ≤ G) (hH : 0 ≤ H) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hφ : C3TestBounds d φ G H J) (hψ : ∀ t, |ψ (τ t)| ≤ B)
    (hK : ∀ x, ‖K x‖ ≤ C*(1+‖x‖)) (hKl : ∀ x y, ‖K x-K y‖ ≤ A*‖x-y‖) :
    let F := fun ω => discreteKernelDesign N nt d w τ K φ ψ (fun t i ω => D.pos t i ω+D.noise t i ω) ω -
      discreteKernelDesign N nt d w τ K φ ψ D.pos ω
    MemLp F 2 P ∧ (∫ ω,(F ω)^2 ∂P) ≤
      (∑ t,|w t|)^2*B^2*(6*(H*C)^2*(1+2*R)+8*(G*A)^2)*q := by
  classical
  dsimp only
  let Cpair := 6*(H*C)^2*(1+2*R)+8*(G*A)^2
  have hCp : 0 ≤ Cpair := by dsimp [Cpair]; positivity
  have hb := hφ.observation_bounds
  have hgc := (euclidean_test_derivatives_continuous d φ (hφ.smooth.of_le (by norm_num))).1
  let F := fun t i j ω => inner ℝ (gradient φ (D.pos t i ω+D.noise t i ω))
      (K ((D.pos t i ω+D.noise t i ω)-(D.pos t j ω+D.noise t j ω))) -
      inner ℝ (gradient φ (D.pos t i ω)) (K (D.pos t i ω-D.pos t j ω))
  have hp t i j := observed_pair_feature_difference_moment P (gradient φ) K hgc.measurable hKm
    G H C A hG hH hC hA hb.1 hb.2.2.1 hK hKl
    (D.pos t i) (D.pos t j) (D.noise t i) (D.noise t j)
    (D.pos_meas t i) (D.pos_meas t j) (D.noise_meas t i) (D.noise_meas t j)
    (D.pos_lp t i) (D.pos_lp t j) (D.noise_lp t i) (D.noise_lp t j)
    (D.independent t i i) (D.independent t i j) q R hq
    (D.pos_moment t i) (D.pos_moment t j) (D.noise_moment t i) (D.noise_moment t j)
  have hs t i j : MemLp (fun ω => ψ (τ t)*F t i j ω) 2 P ∧
      (∫ ω,(ψ (τ t)*F t i j ω)^2 ∂P) ≤ B^2*Cpair*q := by
    refine ⟨(hp t i j).1.const_mul _,?_⟩
    rw [show (fun ω => (ψ (τ t)*F t i j ω)^2) = (fun ω => (ψ (τ t))^2*(F t i j ω)^2) from funext (fun _ => mul_pow _ _ _),integral_const_mul]
    calc
      _ ≤ (ψ (τ t))^2*(Cpair*q) := mul_le_mul_of_nonneg_left (hp t i j).2 (sq_nonneg _)
      _ ≤ B^2*(Cpair*q) := mul_le_mul_of_nonneg_right (by
        have hb0 := (abs_nonneg (ψ (τ t))).trans (hψ t)
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb0).mpr (hψ t)) (mul_nonneg hCp hq)
      _ = _ := by ring
  have hh := pair_time_average_moment P N nt hN w (fun t i j ω => ψ (τ t)*F t i j ω)
    (fun t i j => (hs t i j).1) (B^2*Cpair*q) (by positivity) (fun t i j => (hs t i j).2)
  have he : (fun ω => discreteKernelDesign N nt d w τ K φ ψ (fun t i ω => D.pos t i ω+D.noise t i ω) ω -
      discreteKernelDesign N nt d w τ K φ ψ D.pos ω) = pairTimeAverage N nt w (fun t i j ω => ψ (τ t)*F t i j ω) := by
    funext ω
    have hi (i j : Fin N) (a b : ℝ) : (if i=j then 0 else a-b) =
        (if i=j then 0 else a)-(if i=j then 0 else b) := by
      by_cases h : i=j <;> simp [h]
    simp only [discreteKernelDesign,pairTimeAverage,F,mul_sub,hi,Finset.sum_sub_distrib]
  simpa only [←he,Cpair,mul_assoc] using hh
end Samples
end WMFKIExternalProbe
