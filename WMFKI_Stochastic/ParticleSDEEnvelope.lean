import WMFKI_Stochastic.AdditiveParticleEquation
import WMFKI_Stochastic.ParticleNormComparison
import WMFKI_Stochastic.ParticleBrownianEnvelope

open MeasureTheory Set
open scoped BigOperators
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
namespace WMFKIExternalProbe

theorem continuous_particlePositions (N d : ℕ) (i : Fin N) :
    Continuous (fun x : Fin (N*d) → ℝ => particlePositions N d x i) := by
  exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
    (continuous_pi (fun a => continuous_apply (finProdFinEquiv (i,a))))

/-- Pathwise solution envelope derived from the actual SDE, not supplied as an input. -/
theorem particle_sde_envelope
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N d : ℕ) (hN : 0 < N) (B : BrownianSystem P (N*d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hKc : Continuous K)
    (G : ℝ) (hG : 0 ≤ G) (hK : ∀ z, ‖K z‖ ≤ G*(1+‖z‖))
    (σ T : ℝ) (hT : 0 ≤ T) (ξ : Ω → Fin (N*d) → ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hX : VectorSDESolution P B.F B.W (particleCoordinateDrift N d K)
      (fun i j _ => if i = j then σ else 0) ξ X) :
    ∃ H : Fin N → Ω → ℝ,
      (∀ i, MemLp (H i) 2 P) ∧ (∀ i ω, 0 ≤ H i ω) ∧
      (∀ i, (∫ ω, (H i ω)^2 ∂P) ≤ 4*(d : ℝ)^2*T) ∧
      let a := fun i ω => ‖particlePositions N d (ξ ω) i‖ + |σ| * H i ω + (G+1)*T
      ∀ᵐ ω ∂P, ∀ i t, t ∈ Icc 0 T →
        ‖particlePositions N d (X (realTimeClamp t) ω) i‖ ≤
          (a i ω + (G+1)*T*((N : ℝ)⁻¹ * ∑ j, a j ω)*Real.exp (2*(G+1)*T))*Real.exp ((G+1)*T) := by
  obtain ⟨H,hHm,hHn,hHb,hHbound⟩ := particle_brownian_envelopes P N d B T hT
  refine ⟨H,hHm,hHn,hHb,?_⟩
  have hf (r : ℝ) : (realTimeClamp r : HalfClosedTime) < ⊤ := by
    apply (real_time_clamp_mono (le_max_left r 0)).trans_lt
    exact real_time_below (max r 0) (le_max_right r 0) (EReal.coe_lt_top _)
  have hc ω : Continuous (fun r : ℝ => X (realTimeClamp r) ω) :=
    continuous_iff_continuousAt.mpr (fun r =>
      (hX.path ω _ (hf r)).comp real_time_clamp_continuous.continuousAt)
  filter_upwards [additive_sde_equation P B (particleCoordinateDrift N d K) σ ξ X hX] with ω he
  let x := fun i r => particlePositions N d (X (realTimeClamp r) ω) i
  let w := fun i r => particlePositions N d (fun k => B.W k (realTimeClamp r) ω) i
  have hxc i : Continuous (x i) := (continuous_particlePositions N d i).comp (hc ω)
  have hvec i t (ht : t ∈ Icc 0 T) : x i t = particlePositions N d (ξ ω) i +
      (∫ s in 0..t, particleDrift K (fun j => x j s) i) + σ • w i t := by
    have hint : IntervalIntegrable (fun s => particleDrift K (fun j => x j s) i) volume 0 t :=
      (particleDrift_path_continuous K hKc x hxc i).intervalIntegrable 0 t
    ext a
    have hev := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) a).intervalIntegral_comp_comm hint
    change (∫ s in 0..t, (particleDrift K (fun j => x j s) i) a) =
      (∫ s in 0..t, particleDrift K (fun j => x j s) i) a at hev
    change X (realTimeClamp t) ω (finProdFinEquiv (i,a)) =
      ξ ω (finProdFinEquiv (i,a)) +
        (∫ s in 0..t, particleDrift K (fun j => x j s) i) a +
        σ * B.W (finProdFinEquiv (i,a)) (realTimeClamp t) ω
    rw [← hev]
    simpa only [particleCoordinateDrift, Equiv.symm_apply_apply] using he t ht.1 (finProdFinEquiv (i,a))
  exact particle_norm_comparison hN K hKc G hG hK x w (particlePositions N d (ξ ω)) σ T hT
    hxc (fun i => H i ω) (fun i => hHn i ω) (fun i t ht => hHbound i ω t ht) hvec

end WMFKIExternalProbe
#print axioms WMFKIExternalProbe.particle_sde_envelope
