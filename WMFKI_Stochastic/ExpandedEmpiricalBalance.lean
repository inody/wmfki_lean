import WMFKI_Stochastic.EmpiricalGenerator

open MeasureTheory Set
open scoped BigOperators
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
namespace WMFKIExternalProbe

noncomputable def empiricalPairInteraction (N d : ℕ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (x : Fin (N*d) → ℝ) : ℝ :=
  ((N : ℝ)⁻¹)^2 * ∑ i, ∑ j, if i=j then 0 else
    inner ℝ (gradient φ (particlePositions N d x i))
      (K (particlePositions N d x i-particlePositions N d x j))

noncomputable def empiricalLaplacian (N d : ℕ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (x : Fin (N*d) → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, Laplacian.laplacian φ (particlePositions N d x i)

theorem euclidean_test_derivatives_continuous (d : ℕ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : ContDiff ℝ 2 φ) :
    Continuous (gradient φ) ∧ Continuous (Laplacian.laplacian φ) := by
  constructor
  · exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.comp
      (hφ.continuous_fderiv (by norm_num))
  · have hφ1 : ContDiff ℝ 1 (fderiv ℝ φ) := (contDiff_succ_iff_fderiv (n := 1)).mp hφ |>.2.2
    change Continuous (fun x => Laplacian.laplacian φ x)
    simp_rw [euclidean_laplacian_trace]
    exact continuous_finsetSum _ (fun a _ =>
      ((hφ1.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply continuous_const)

theorem empirical_pair_laplacian_continuous (N d : ℕ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : Continuous K)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : ContDiff ℝ 2 φ) :
    Continuous (empiricalPairInteraction N d K φ) ∧ Continuous (empiricalLaplacian N d φ) := by
  classical
  obtain ⟨hg,hl⟩ := euclidean_test_derivatives_continuous d φ hφ
  have hp i := continuous_particlePositions N d i
  constructor
  · have hs : Continuous (fun x => ∑ i, ∑ j, if i=j then (0 : ℝ) else
        inner ℝ (gradient φ (particlePositions N d x i))
          (K (particlePositions N d x i-particlePositions N d x j))) := by
      apply continuous_finsetSum
      intro i _
      apply continuous_finsetSum
      intro j _
      by_cases h : i=j
      · simpa only [h,ite_true] using (continuous_const : Continuous (fun _ : Fin (N*d) → ℝ => (0 : ℝ)))
      · simpa only [h,ite_false,Function.comp_def,Pi.sub_apply] using
          (hg.comp (hp i)).inner (hK.comp ((hp i).sub (hp j)))
    exact hs.const_mul _
  · exact (continuous_finsetSum _ (fun i _ => hl.comp (hp i))).const_mul _

theorem half_process_real_continuous {Ω E : Type*} [TopologicalSpace E]
    (X : HalfClosedTime → Ω → E)
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t) :
    ∀ ω, Continuous (fun r : ℝ => X (realTimeClamp r) ω) := by
  have hf (r : ℝ) : (realTimeClamp r : HalfClosedTime) < ⊤ := by
    apply (real_time_clamp_mono (le_max_left r 0)).trans_lt
    exact real_time_below (max r 0) (le_max_right r 0) (EReal.coe_lt_top _)
  exact fun ω => continuous_iff_continuousAt.mpr
    (fun r => (hc ω _ (hf r)).comp real_time_clamp_continuous.continuousAt)

/-- The manuscript's latent weak response equals its full-pair interaction
integral plus a proved local-martingale residual. All time integrals used in
splitting the identity are first proved integrable by continuity. -/
theorem expanded_empirical_weak_response
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
      (fun ω => -(∫ s in 0..T, deriv ψ s*empiricalObservable N d φ (X (realTimeClamp s) ω)) -
        (σ^2/2)*(∫ s in 0..T, ψ s*empiricalLaplacian N d φ (X (realTimeClamp s) ω))) =ᵐ[P]
      fun ω => (∫ s in 0..T, ψ s*empiricalPairInteraction N d K φ (X (realTimeClamp s) ω)) +
        Z (realTimeClamp T) ω := by
  obtain ⟨Z,hZ,he⟩ := empirical_particle_weak_balance P N d B K hK σ ξ X hX φ hφ ψ hψ T hT hψ0 hψT
  obtain ⟨hcP,hcL⟩ := empirical_pair_laplacian_continuous N d K hK φ hφ
  have hcF := (empiricalObservable_contDiff N d φ hφ).continuous
  have hcX := half_process_real_continuous X hX.path
  refine ⟨Z,hZ,?_⟩
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
