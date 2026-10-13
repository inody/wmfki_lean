import WMFKI_Stochastic.EmpiricalBrownianBalance

open MeasureTheory Set Filter
open scoped BigOperators
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
namespace WMFKIExternalProbe

/-- Actual continuous-time latent weak response minus the full-pair interaction.
No residual bound or stochastic representation is included in this definition. -/
noncomputable def empiricalWeakResidual {Ω : Type*} (N d : ℕ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (σ : ℝ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (ψ : ℝ → ℝ) (T : ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ) (ω : Ω) : ℝ :=
  -(∫ s in 0..T, deriv ψ s*empiricalObservable N d φ (X (realTimeClamp s) ω)) -
    (σ^2/2)*(∫ s in 0..T, ψ s*empiricalLaplacian N d φ (X (realTimeClamp s) ω)) -
    (∫ s in 0..T, ψ s*empiricalPairInteraction N d K φ (X (realTimeClamp s) ω))

/-- Complete Brownian representation and sigma^2/N second-moment estimate
for the actual weak residual. Integrability and centering are conclusions.
The Brownian coefficients are genuine derivatives of the empirical observable,
and empirical_noise_coordinate expands them to sigma/N times particle gradients. -/
theorem empirical_weak_residual_energy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N d : ℕ) (hN : 0 < N) (B : BrownianSystem P (N*d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : Continuous K)
    (σ : ℝ) (ξ : Ω → Fin (N*d) → ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hX : VectorSDESolution P B.F B.W (particleCoordinateDrift N d K)
      (fun i j _ => if i=j then σ else 0) ξ X)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (G : ℝ) (hbound : ∀ x, ‖gradient φ x‖ ≤ G)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ) (T : ℝ) (hT : 0 ≤ T)
    (hψ0 : ψ 0 = 0) (hψT : ψ T = 0) :
    ∃ M : Fin (N*d) → HalfClosedTime → Ω → ℝ,
      (∀ k, ContinuousM2Witness P B.F (M k)) ∧
      (∀ k, ItoCovarianceFormula P B.F (B.W k)
        (fun z => (Iic T).indicator (fun r => empiricalNoiseIntegrand N d σ ψ φ X k (z.1,r)) z.2) (M k)) ∧
      ContinuousM2Witness P B.F (fun t ω => ∑ k,M k t ω) ∧
      empiricalWeakResidual N d K σ φ ψ T X =ᵐ[P] (fun ω => ∑ k,M k (realTimeClamp T) ω) ∧
      MemLp (empiricalWeakResidual N d K σ φ ψ T X) 2 P ∧
      (∫ ω, empiricalWeakResidual N d K σ φ ψ T X ω ∂P) = 0 ∧
      (∫ ω, (empiricalWeakResidual N d K σ φ ψ T X ω)^2 ∂P) ≤
        (σ^2/(N : ℝ))*G^2*(∫ s in 0..T, (ψ s)^2) := by
  obtain ⟨M,hM,hMl,hMI,hS,hmean,henergy⟩ := exists_empirical_noise_with_energy P N d hN B K σ ξ X hX
    ψ hψ.continuous φ hφ G hbound T hT
  have he := empirical_response_brownian_identity P N d B K hK σ ξ X hX φ hφ ψ hψ T hT hψ0 hψT M hMl hMI
  have hr : empiricalWeakResidual N d K σ φ ψ T X =ᵐ[P] (fun ω => ∑ k,M k (realTimeClamp T) ω) := by
    filter_upwards [he] with ω hω
    dsimp only [empiricalWeakResidual]
    linarith
  have hR : MemLp (empiricalWeakResidual N d K σ φ ψ T X) 2 P :=
    (hS.moment (realTimeClamp T)).ae_eq hr.symm
  refine ⟨M,hM,hMI,hS,hr,hR,?_,?_⟩
  · exact (integral_congr_ae hr).trans hmean
  · calc
      _ = ∫ ω, (∑ k,M k (realTimeClamp T) ω)^2 ∂P :=
        integral_congr_ae (hr.mono (fun ω hω => congrArg (fun z : ℝ => z^2) hω))
      _ ≤ _ := henergy

/-- Any previously obtained local residual with the proved expanded weak
balance equals the constructed Brownian sum at the terminal time. No moment
hypothesis on that residual is required. -/
theorem expanded_residual_identification
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N d : ℕ) (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (σ : ℝ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (ψ : ℝ → ℝ) (T : ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (Z : HalfClosedTime → Ω → ℝ) (M : Fin (N*d) → HalfClosedTime → Ω → ℝ)
    (hZ : (fun ω => -(∫ s in 0..T, deriv ψ s*empiricalObservable N d φ (X (realTimeClamp s) ω)) -
        (σ^2/2)*(∫ s in 0..T, ψ s*empiricalLaplacian N d φ (X (realTimeClamp s) ω))) =ᵐ[P]
      fun ω => (∫ s in 0..T, ψ s*empiricalPairInteraction N d K φ (X (realTimeClamp s) ω)) + Z (realTimeClamp T) ω)
    (hM : empiricalWeakResidual N d K σ φ ψ T X =ᵐ[P] (fun ω => ∑ k,M k (realTimeClamp T) ω)) :
    Z (realTimeClamp T) =ᵐ[P] (fun ω => ∑ k,M k (realTimeClamp T) ω) := by
  filter_upwards [hZ,hM] with ω hz hm
  dsimp only [empiricalWeakResidual] at hm
  linarith

end WMFKIExternalProbe
