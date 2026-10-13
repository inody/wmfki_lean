import WMFKI_Stochastic.WeightedParticleIto

open MeasureTheory Set
open scoped BigOperators
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
namespace WMFKIExternalProbe

/-- The already verified coordinate adapter is a genuine continuous linear map. -/
noncomputable def particleProjection (N d : ℕ) (i : Fin N) :
    (Fin (N*d) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun := fun x => particlePositions N d x i
  map_add' := by intro x y; ext a; rfl
  map_smul' := by intro c x; ext a; rfl
  cont := continuous_particlePositions N d i

noncomputable def empiricalObservable (N d : ℕ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (x : Fin (N*d) → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, φ (particlePositions N d x i)

theorem empiricalObservable_contDiff (N d : ℕ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : ContDiff ℝ 2 φ) :
    ContDiff ℝ 2 (empiricalObservable N d φ) := by
  have hs : ContDiff ℝ 2 (fun x => ∑ i, φ (particlePositions N d x i)) :=
    ContDiff.sum (fun i _ => hφ.comp (particleProjection N d i).contDiff)
  exact contDiff_const.mul hs

/-- A weak balance for the actual empirical observable of the interacting
particles. Its generator uses actual derivatives. Expansion into individual
particle gradients/Laplacians and identification of the residual integrands
are deliberately not claimed by this interface. -/
theorem empirical_particle_weak_balance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N d : ℕ) (B : BrownianSystem P (N*d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : Continuous K)
    (σ : ℝ) (ξ : Ω → Fin (N*d) → ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hX : VectorSDESolution P B.F B.W (particleCoordinateDrift N d K)
      (fun i j _ => if i=j then σ else 0) ξ X)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ) (T : ℝ) (hT : 0 ≤ T)
    (hψ0 : ψ 0 = 0) (hψT : ψ T = 0) :
    ∃ Z : HalfClosedTime → Ω → ℝ, LocalMProcessWitness P B.F Z ∧
      (fun ω => ∫ s in 0..T, deriv ψ s*empiricalObservable N d φ (X (realTimeClamp s) ω)+
        ψ s*additiveParticleGenerator N d K σ (empiricalObservable N d φ) (X (realTimeClamp s) ω)) =ᵐ[P]
      fun ω => -Z (realTimeClamp T) ω :=
  weighted_particle_weak_balance P N d B K hK σ ξ X hX (empiricalObservable N d φ)
    (empiricalObservable_contDiff N d φ hφ) ψ hψ T hT hψ0 hψT

end WMFKIExternalProbe
