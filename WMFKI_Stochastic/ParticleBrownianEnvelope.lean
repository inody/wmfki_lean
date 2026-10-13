import WMFKI_Stochastic.ParticleCoordinatesProbe
import Chapter6BrownianEnvelopeBound

open MeasureTheory Set
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
namespace WMFKIExternalProbe

/-- Select one d-coordinate Brownian block without changing the common filtration. -/
noncomputable def particleBrownianBlock
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N d : ℕ) (B : BrownianSystem P (N*d)) (i : Fin N) : BrownianSystem P d where
  F := B.F
  mono := B.mono
  le := B.le
  null := B.null
  W := fun j => B.W (finProdFinEquiv (i,j))
  C := fun j k => B.C (finProdFinEquiv (i,j)) (finProdFinEquiv (i,k))
  martingale := fun j => B.martingale _
  cov := fun j k => B.cov _ _
  clock := by
    intro j k ω t ht
    simpa using B.clock (finProdFinEquiv (i,j)) (finProdFinEquiv (i,k)) ω t ht

/-- Each particle's Brownian envelope has second moment at most 4 d² T,
not 4 (Nd)² T. No independence between the envelopes is required. -/
theorem particle_brownian_envelopes
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N d : ℕ) (B : BrownianSystem P (N*d)) (T : ℝ) (hT : 0 ≤ T) :
    ∃ H : Fin N → Ω → ℝ,
      (∀ i, MemLp (H i) 2 P) ∧ (∀ i ω, 0 ≤ H i ω) ∧
      (∀ i, (∫ ω, (H i ω)^2 ∂P) ≤ 4*(d : ℝ)^2*T) ∧
      ∀ i ω t, t ∈ Icc 0 T →
        ‖particlePositions N d (fun k => B.W k (realTimeClamp t) ω) i‖ ≤ H i ω := by
  choose H hm hn hb he using
    (fun i => Asakura.Chapter6.brownian_path_L2_envelope_bound P (particleBrownianBlock P N d B i) T hT)
  exact ⟨H,hm,hn,hb,he⟩

end WMFKIExternalProbe
#print axioms WMFKIExternalProbe.particleBrownianBlock
#print axioms WMFKIExternalProbe.particle_brownian_envelopes
