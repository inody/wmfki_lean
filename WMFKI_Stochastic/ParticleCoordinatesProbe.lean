import WMFKI_Stochastic.ParticleDriftProbe

open scoped BigOperators
namespace WMFKIExternalProbe

noncomputable def particlePositions (N d : ℕ) (x : Fin (N*d) → ℝ) (i : Fin N) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun a => x (finProdFinEquiv (i,a)))

noncomputable def particleCoordinateDrift (N d : ℕ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (k : Fin (N*d)) (x : Fin (N*d) → ℝ) : ℝ :=
  particleDrift K (particlePositions N d x) (finProdFinEquiv.symm k).1
    (finProdFinEquiv.symm k).2

theorem particlePositions_sum_sq (N d : ℕ) (x y : Fin (N*d) → ℝ) :
    (∑ i, ‖particlePositions N d x i - particlePositions N d y i‖^2) =
      ∑ k, (x k - y k)^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  change (∑ i, ∑ a, (x (finProdFinEquiv (i,a)) - y (finProdFinEquiv (i,a)))^2) = _
  rw [← Equiv.sum_comp finProdFinEquiv (fun k => (x k - y k)^2),
    Fintype.sum_prod_type]

theorem particleCoordinateDrift_sum_sq (N d : ℕ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x y : Fin (N*d) → ℝ) :
    (∑ k, (particleCoordinateDrift N d K k x - particleCoordinateDrift N d K k y)^2) =
      ∑ i, ‖particleDrift K (particlePositions N d x) i -
        particleDrift K (particlePositions N d y) i‖^2 := by
  rw [← Equiv.sum_comp finProdFinEquiv
    (fun k => (particleCoordinateDrift N d K k x - particleCoordinateDrift N d K k y)^2)]
  simp [particleCoordinateDrift, Fintype.sum_prod_type, EuclideanSpace.real_norm_sq_eq]

theorem particleCoordinateDrift_lipschitz (N d : ℕ) (hN : 0 < N)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℝ) (hL : 0 ≤ L) (hK : ∀ u v, ‖K u - K v‖ ≤ L * ‖u - v‖)
    (x y : Fin (N*d) → ℝ) :
    (∑ k, (particleCoordinateDrift N d K k x - particleCoordinateDrift N d K k y)^2) ≤
      4 * L^2 * ∑ k, (x k - y k)^2 := by
  rw [particleCoordinateDrift_sum_sq, ← particlePositions_sum_sq N d]
  exact particleDrift_lipschitz_sq hN K L hL hK _ _

end WMFKIExternalProbe
#print axioms WMFKIExternalProbe.particleCoordinateDrift_lipschitz
