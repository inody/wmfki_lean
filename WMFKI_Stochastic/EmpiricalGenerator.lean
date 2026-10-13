import WMFKI_Stochastic.EmpiricalDerivatives

open scoped BigOperators
namespace WMFKIExternalProbe

theorem linearMap_coordinate_sum {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    (∑ k, L (Pi.single k 1)*v k) = L v := by
  classical
  calc
    _ = L (∑ k, v k • Pi.single k 1) := by simp [map_sum,mul_comm]
    _ = L v := by congr 1; ext k; simp [Pi.single_apply]

theorem particlePositions_coordinateDrift (N d : ℕ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : Fin (N*d) → ℝ) (i : Fin N) :
    particlePositions N d (fun k => particleCoordinateDrift N d K k x) i =
      particleDrift K (particlePositions N d x) i := by
  change particlePositions N d (packParticles N d (particleDrift K (particlePositions N d x))) i = _
  rw [particlePositions_pack]

theorem euclidean_laplacian_trace (d : ℕ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Laplacian.laplacian φ x =
      ∑ a, fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single a 1) (EuclideanSpace.single a 1) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp [iteratedFDeriv_two_apply,EuclideanSpace.basisFun_apply]

theorem empirical_hessian_trace (N d : ℕ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (x : Fin (N*d) → ℝ) :
    (∑ k, fderiv ℝ (fderiv ℝ (empiricalObservable N d φ)) x (Pi.single k 1) (Pi.single k 1)) =
      (N : ℝ)⁻¹ * ∑ i, Laplacian.laplacian φ (particlePositions N d x i) := by
  rw [← Equiv.sum_comp finProdFinEquiv (fun k =>
    fderiv ℝ (fderiv ℝ (empiricalObservable N d φ)) x (Pi.single k 1) (Pi.single k 1))]
  rw [Fintype.sum_prod_type]
  simp_rw [empirical_hessian_diagonal N d φ hφ,euclidean_laplacian_trace,
    ← Finset.mul_sum]

theorem empirical_generator_particles (N d : ℕ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (σ : ℝ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (x : Fin (N*d) → ℝ) :
    additiveParticleGenerator N d K σ (empiricalObservable N d φ) x =
      (N : ℝ)⁻¹ * ((∑ i, inner ℝ (gradient φ (particlePositions N d x i))
        (particleDrift K (particlePositions N d x) i)) +
        σ^2/2 * ∑ i, Laplacian.laplacian φ (particlePositions N d x i)) := by
  unfold additiveParticleGenerator
  rw [linearMap_coordinate_sum,empirical_fderiv_apply N d φ (hφ.differentiable (by norm_num)),
    empirical_hessian_trace N d φ hφ]
  simp_rw [particlePositions_coordinateDrift,← inner_gradient_left]
  ring

/-- The interaction term has exactly the manuscript's off-diagonal 1/N²
normalization, including the N=1 case with a possibly nonzero K(0). -/
theorem empirical_generator_pairs (N d : ℕ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (σ : ℝ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (x : Fin (N*d) → ℝ) :
    additiveParticleGenerator N d K σ (empiricalObservable N d φ) x =
      ((N : ℝ)⁻¹)^2 * (∑ i, ∑ j, if i=j then 0 else
        inner ℝ (gradient φ (particlePositions N d x i))
          (K (particlePositions N d x i-particlePositions N d x j))) +
      (σ^2/2)*(N : ℝ)⁻¹ * ∑ i, Laplacian.laplacian φ (particlePositions N d x i) := by
  classical
  rw [empirical_generator_particles N d K σ φ hφ]
  simp_rw [particleDrift,inner_smul_right,inner_sum,apply_ite,inner_zero_right]
  simp_rw [← Finset.mul_sum]
  ring

theorem fderiv_euclidean_coordinate (d : ℕ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (a : Fin d) :
    fderiv ℝ φ x (EuclideanSpace.single a 1) = (gradient φ x : EuclideanSpace ℝ (Fin d)) a := by
  rw [← inner_gradient_left]
  simpa only [EuclideanSpace.basisFun_apply] using EuclideanSpace.inner_basisFun_real (Fin d) (gradient φ x) a

/-- Exact Euclidean gradient energy, with no loss depending on dimension or N. -/
theorem empirical_gradient_energy (N d : ℕ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : Differentiable ℝ φ)
    (x : Fin (N*d) → ℝ) :
    (∑ k, (fderiv ℝ (empiricalObservable N d φ) x (Pi.single k 1))^2) =
      ((N : ℝ)⁻¹)^2 * ∑ i, ‖gradient φ (particlePositions N d x i)‖^2 := by
  rw [← Equiv.sum_comp finProdFinEquiv (fun k =>
    (fderiv ℝ (empiricalObservable N d φ) x (Pi.single k 1))^2)]
  rw [Fintype.sum_prod_type]
  simp_rw [empirical_fderiv_coordinate N d φ hφ,fderiv_euclidean_coordinate,mul_pow,
    EuclideanSpace.real_norm_sq_eq,← Finset.mul_sum]

theorem empirical_gradient_energy_bound (N d : ℕ) (hN : 0 < N)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : Differentiable ℝ φ)
    (G : ℝ) (hbound : ∀ x, ‖gradient φ x‖ ≤ G)
    (x : Fin (N*d) → ℝ) :
    (∑ k, (fderiv ℝ (empiricalObservable N d φ) x (Pi.single k 1))^2) ≤ G^2/(N : ℝ) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  rw [empirical_gradient_energy N d φ hφ]
  calc
    _ ≤ ((N : ℝ)⁻¹)^2 * ∑ _i : Fin N, G^2 := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hbound _) 2) (sq_nonneg _)
    _ = _ := by simp; field_simp

end WMFKIExternalProbe
