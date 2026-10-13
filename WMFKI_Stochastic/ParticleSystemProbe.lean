import WMFKI_Stochastic.ParticleInitialProbe
import EndToEndRandomSDEExistence
import Chapter4VectorManuscriptUniqueness

open MeasureTheory
open scoped BigOperators
open Asakura.Chapter2Complete Asakura.Chapter4

namespace WMFKIExternalProbe

theorem particle_coefficients_lipschitz (N d : ℕ) (hN : 0 < N)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℝ) (hL : 0 ≤ L) (hK : ∀ u v, ‖K u - K v‖ ≤ L * ‖u - v‖)
    (σ : ℝ) (x y : Fin (N*d) → ℝ) :
    (∑ k, (particleCoordinateDrift N d K k x - particleCoordinateDrift N d K k y)^2) +
      (∑ i : Fin (N*d), ∑ j : Fin (N*d),
        ((fun _ : Fin (N*d) → ℝ => if i = j then σ else 0) x -
         (fun _ : Fin (N*d) → ℝ => if i = j then σ else 0) y)^2) ≤
      4 * L^2 * ∑ k, (x k - y k)^2 := by
  simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Finset.sum_const_zero, add_zero] using particleCoordinateDrift_lipschitz N d hN K L hL hK x y

/-- The manuscript's off-diagonal N-particle drift, in genuine Euclidean d-dimensional
blocks, satisfies the external SDE existence interface. BrownianSystem and initial
measurability/L2 remain explicit inputs, not claimed as constructed here. -/
theorem exists_particle_system_solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N d : ℕ) (hN : 0 < N) (B : BrownianSystem P (N*d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℝ) (hL : 0 ≤ L) (hK : ∀ u v, ‖K u - K v‖ ≤ L * ‖u - v‖)
    (σ : ℝ) (ξ : Ω → Fin (N*d) → ℝ)
    (hξ : Measurable[B.F ⊥] ξ) (hξ2 : MemLp ξ 2 P) :
    ∃ X : HalfClosedTime → Ω → Fin (N*d) → ℝ,
      VectorSDESolution P B.F B.W (particleCoordinateDrift N d K)
        (fun i j _ => if i = j then σ else 0) ξ X := by
  exact Asakura.EndToEnd.random_sde_exists P B (4*L^2) (by positivity)
    (particleCoordinateDrift N d K) (fun i j _ => if i = j then σ else 0)
    (particle_coefficients_lipschitz N d hN K L hL hK σ) ξ hξ hξ2

theorem particle_system_pathwise_unique
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N d : ℕ) (hN : 0 < N) (B : BrownianSystem P (N*d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℝ) (hL : 0 ≤ L) (hK : ∀ u v, ‖K u - K v‖ ≤ L * ‖u - v‖)
    (σ : ℝ) (ξ : Ω → Fin (N*d) → ℝ) (hξ2 : MemLp ξ 2 P)
    (X Y : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hX : VectorSDESolution P B.F B.W (particleCoordinateDrift N d K)
      (fun i j _ => if i = j then σ else 0) ξ X)
    (hY : VectorSDESolution P B.F B.W (particleCoordinateDrift N d K)
      (fun i j _ => if i = j then σ else 0) ξ Y) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → X t ω = Y t ω := by
  obtain ⟨I,hI,hIc,heI⟩ := hX.integrals
  obtain ⟨J,hJ,hJc,heJ⟩ := hY.integrals
  exact Asakura.Chapter4.Vector.sde_unique_from_manuscript_hypotheses P
    (EReal.coe_lt_top 0) B.F B.mono B.le B.null B.W (fun j => B.C j j)
    B.martingale (fun j => B.cov j j) (fun j ω r hr _ => B.diagonal_clock j ω r hr)
    (particleCoordinateDrift N d K) (fun i j _ => if i = j then σ else 0)
    (4*L^2) (by positivity) (particle_coefficients_lipschitz N d hN K L hL hK σ)
    ξ (hX.initial_adapted.mono (B.le ⊥) le_rfl) hξ2
    X Y hX.adapted hY.adapted hX.path hY.path I J hI hJ hIc hJc heI heJ

/-- Fourth moments of the actual Euclidean initial particles supply the external
L2 assumption. Initial adaptedness and BrownianSystem are still explicit. -/
theorem exists_unique_particle_system_of_fourth_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N d : ℕ) (hN : 0 < N) (B : BrownianSystem P (N*d))
    [MeasurableSpace (EuclideanSpace ℝ (Fin d))] [BorelSpace (EuclideanSpace ℝ (Fin d))]
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℝ) (hL : 0 ≤ L) (hK : ∀ u v, ‖K u - K v‖ ≤ L * ‖u - v‖)
    (σ : ℝ) (ξ : Ω → Fin N → EuclideanSpace ℝ (Fin d))
    (hξ : ∀ i, Measurable[B.F ⊥] (fun ω => ξ ω i))
    (hξ4 : ∀ i, MemLp (fun ω => ξ ω i) 4 P) :
    ∃ X : HalfClosedTime → Ω → Fin (N*d) → ℝ,
      VectorSDESolution P B.F B.W (particleCoordinateDrift N d K)
        (fun i j _ => if i = j then σ else 0) (fun ω => packParticles N d (ξ ω)) X ∧
      ∀ Y, VectorSDESolution P B.F B.W (particleCoordinateDrift N d K)
        (fun i j _ => if i = j then σ else 0) (fun ω => packParticles N d (ξ ω)) Y →
        ∀ᵐ ω ∂P, ∀ t, t < ⊤ → X t ω = Y t ω := by
  have hξm := @packParticles_measurable Ω (B.F ⊥) N d _ _ ξ hξ
  have hξ2 := packParticles_memLp_two_of_four P N d ξ hξ4
  obtain ⟨X,hX⟩ := exists_particle_system_solution P N d hN B K L hL hK σ _ hξm hξ2
  exact ⟨X,hX,fun Y hY => particle_system_pathwise_unique P N d hN B K L hL hK σ _ hξ2 X Y hX hY⟩

end WMFKIExternalProbe

#print axioms WMFKIExternalProbe.exists_particle_system_solution
#print axioms WMFKIExternalProbe.particle_system_pathwise_unique
#print axioms WMFKIExternalProbe.exists_unique_particle_system_of_fourth_moments
