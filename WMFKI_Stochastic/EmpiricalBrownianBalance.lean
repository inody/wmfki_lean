import WMFKI_Stochastic.WeightedBrownianIdentity
import WMFKI_Stochastic.EmpiricalNoiseEnergy

open MeasureTheory Set
open scoped BigOperators
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
namespace WMFKIExternalProbe

/-- The expanded weak response uses actual Brownian integrals, not merely an unspecified local martingale. -/
theorem empirical_response_brownian_identity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N d : ℕ) (B : BrownianSystem P (N*d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : Continuous K)
    (σ : ℝ) (ξ : Ω → Fin (N*d) → ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hX : VectorSDESolution P B.F B.W (particleCoordinateDrift N d K)
      (fun i j _ => if i=j then σ else 0) ξ X)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ) (T : ℝ) (hT : 0 ≤ T)
    (hψ0 : ψ 0 = 0) (hψT : ψ T = 0)
    (M : Fin (N*d) → HalfClosedTime → Ω → ℝ)
    (hM : ∀ i, LocalMProcessWitness P B.F (M i))
    (hMI : ∀ i, ItoCovarianceFormula P B.F (B.W i)
      (fun z => (Iic T).indicator (fun r => empiricalNoiseIntegrand N d σ ψ φ X i (z.1,r)) z.2) (M i)) :
      (fun ω => -(∫ s in 0..T, deriv ψ s*empiricalObservable N d φ (X (realTimeClamp s) ω)) -
        (σ^2/2)*(∫ s in 0..T, ψ s*empiricalLaplacian N d φ (X (realTimeClamp s) ω))) =ᵐ[P]
      fun ω => (∫ s in 0..T, ψ s*empiricalPairInteraction N d K φ (X (realTimeClamp s) ω)) +
        (∑ i,M i (realTimeClamp T) ω) := by
  have hw := weighted_particle_brownian_identity P N d B K hK σ ξ X hX
    (empiricalObservable N d φ) (empiricalObservable_contDiff N d φ hφ) ψ hψ T hT M hM hMI
  have he : (fun ω => ∫ s in 0..T, deriv ψ s*empiricalObservable N d φ (X (realTimeClamp s) ω)+
      ψ s*additiveParticleGenerator N d K σ (empiricalObservable N d φ) (X (realTimeClamp s) ω)) =ᵐ[P]
      fun ω => -(∑ i,M i (realTimeClamp T) ω) := by
    filter_upwards [hw T ⟨hT,le_rfl⟩] with ω hω
    simp only [hψ0,hψT,zero_mul,zero_add] at hω
    linarith
  obtain ⟨hcP,hcL⟩ := empirical_pair_laplacian_continuous N d K hK φ hφ
  have hcF := (empiricalObservable_contDiff N d φ hφ).continuous
  have hcX := half_process_real_continuous X hX.path
  filter_upwards [he] with ω hω
  have hu : IntervalIntegrable (fun s => deriv ψ s*empiricalObservable N d φ (X (realTimeClamp s) ω)) volume 0 T :=
    ((hψ.continuous_deriv le_rfl).mul (hcF.comp (hcX ω))).intervalIntegrable 0 T
  have hl : IntervalIntegrable (fun s => ψ s*empiricalLaplacian N d φ (X (realTimeClamp s) ω)) volume 0 T :=
    (hψ.continuous.mul (hcL.comp (hcX ω))).intervalIntegrable 0 T
  have hp : IntervalIntegrable (fun s => ψ s*empiricalPairInteraction N d K φ (X (realTimeClamp s) ω)) volume 0 T :=
    (hψ.continuous.mul (hcP.comp (hcX ω))).intervalIntegrable 0 T
  have hg (x : Fin (N*d) → ℝ) : additiveParticleGenerator N d K σ (empiricalObservable N d φ) x =
      empiricalPairInteraction N d K φ x+(σ^2/2)*empiricalLaplacian N d φ x := by
    rw [empirical_generator_pairs N d K σ φ hφ]
    dsimp only [empiricalPairInteraction,empiricalLaplacian]
    ring
  have hi : (∫ s in 0..T, deriv ψ s*empiricalObservable N d φ (X (realTimeClamp s) ω)+
      ψ s*additiveParticleGenerator N d K σ (empiricalObservable N d φ) (X (realTimeClamp s) ω)) =
      (∫ s in 0..T, deriv ψ s*empiricalObservable N d φ (X (realTimeClamp s) ω)) +
      (σ^2/2)*(∫ s in 0..T, ψ s*empiricalLaplacian N d φ (X (realTimeClamp s) ω)) +
      (∫ s in 0..T, ψ s*empiricalPairInteraction N d K φ (X (realTimeClamp s) ω)) := by
    have hfun : (fun s => deriv ψ s*empiricalObservable N d φ (X (realTimeClamp s) ω)+
        ψ s*additiveParticleGenerator N d K σ (empiricalObservable N d φ) (X (realTimeClamp s) ω)) =
        (fun s => (deriv ψ s*empiricalObservable N d φ (X (realTimeClamp s) ω)+
          (σ^2/2)*(ψ s*empiricalLaplacian N d φ (X (realTimeClamp s) ω)))+
          ψ s*empiricalPairInteraction N d K φ (X (realTimeClamp s) ω)) := by
      funext s
      rw [hg]
      ring
    rw [hfun]
    rw [intervalIntegral.integral_add (f := fun s => deriv ψ s*empiricalObservable N d φ (X (realTimeClamp s) ω)+
        (σ^2/2)*(ψ s*empiricalLaplacian N d φ (X (realTimeClamp s) ω)))
      (hu.add (hl.const_mul (σ^2/2))) hp,
      intervalIntegral.integral_add hu (hl.const_mul (σ^2/2)),intervalIntegral.integral_const_mul]
  rw [hi] at hω
  linarith

end WMFKIExternalProbe
