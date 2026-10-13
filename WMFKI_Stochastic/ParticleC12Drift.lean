import WMFKI_Stochastic.ParticleSDEEnvelope
import Chapter4SDEDriftRepresentation

open MeasureTheory Set
open scoped BigOperators
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
namespace WMFKIExternalProbe

theorem particleCoordinateDrift_continuous (N d : ℕ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : Continuous K)
    (k : Fin (N*d)) : Continuous (particleCoordinateDrift N d K k) := by
  classical
  let i := (finProdFinEquiv.symm k).1
  have hp j := continuous_particlePositions N d j
  have hv : Continuous (fun x => particleDrift K (particlePositions N d x) i) := by
    unfold particleDrift
    have hs : Continuous (fun x => ∑ j, if i=j then (0 : EuclideanSpace ℝ (Fin d)) else
        K (particlePositions N d x i-particlePositions N d x j)) := by
      apply continuous_finsetSum
      intro j _
      by_cases h : i = j
      · simpa only [h,ite_true] using (continuous_const : Continuous (fun _ : Fin (N*d) → ℝ => (0 : EuclideanSpace ℝ (Fin d))))
      · simpa only [h,ite_false,Function.comp_def,Pi.sub_apply] using hK.comp ((hp i).sub (hp j))
    exact hs.const_smul ((N : ℝ)⁻¹)
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) (finProdFinEquiv.symm k).2).continuous.comp hv

theorem diagonal_diffusion_trace (n : ℕ) (σ : ℝ) (A : Fin n → Fin n → ℝ) :
    (∑ i, ∑ l, A i l * (∑ j, (if i=j then σ else 0)*(if l=j then σ else 0))) =
      σ^2 * ∑ i, A i i := by
  classical
  have he (i l : Fin n) : (∑ j, (if i=j then σ else 0)*(if l=j then σ else 0)) =
      if i=l then σ^2 else 0 := by
    simp [ite_mul,mul_ite,pow_two]
  simp_rw [he]
  simp [mul_ite]
  rw [← Finset.sum_mul,mul_comm]

/-- Generator of the actual off-diagonal particle drift and isotropic
additive diffusion, using genuine Frechet derivatives. -/
noncomputable def additiveParticleGenerator (N d : ℕ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (σ : ℝ)
    (f : (Fin (N*d) → ℝ) → ℝ) (x : Fin (N*d) → ℝ) : ℝ :=
  (∑ i, fderiv ℝ f x (Pi.single i 1)*particleCoordinateDrift N d K i x) +
    σ^2/2 * ∑ i, fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single i 1)

/-- C1 in time and C2 in space suffice; no C2 time assumption is added.
The residual is proved to be a local martingale, not assumed to have that property. -/
theorem particle_c12_drift_representation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N d : ℕ) (B : BrownianSystem P (N*d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : Continuous K)
    (σ : ℝ) (ξ : Ω → Fin (N*d) → ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hX : VectorSDESolution P B.F B.W (particleCoordinateDrift N d K)
      (fun i j _ => if i=j then σ else 0) ξ X)
    (f : ℝ → (Fin (N*d) → ℝ) → ℝ) (ft : ℝ × (Fin (N*d) → ℝ) → ℝ)
    (hf : ∀ t, ContDiff ℝ 2 (f t))
    (hft : ∀ t x, HasDerivAt (fun s => f s x) (ft (t,x)) t)
    (hfc : Continuous (fun z : ℝ × (Fin (N*d) → ℝ) => f z.1 z.2))
    (hftc : Continuous ft)
    (hdf : Continuous (fun z : ℝ × (Fin (N*d) → ℝ) => fderiv ℝ (f z.1) z.2))
    (hddf : Continuous (fun z : ℝ × (Fin (N*d) → ℝ) => fderiv ℝ (fderiv ℝ (f z.1)) z.2))
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ Z : HalfClosedTime → Ω → ℝ, LocalMProcessWitness P B.F Z ∧
      ∀ t, t ∈ Icc 0 T → (fun ω => f t (X (realTimeClamp t) ω)) =ᵐ[P]
        fun ω => f 0 (X ⊥ ω)+Z (realTimeClamp t) ω+
          ∫ s in 0..t, ft (s,X (realTimeClamp s) ω)+
            additiveParticleGenerator N d K σ (f s) (X (realTimeClamp s) ω) := by
  obtain ⟨I,hI,hIc,he⟩ := hX.integrals
  have hc i := particleCoordinateDrift_continuous N d K hK i
  apply sde_drift_representation_constructed P (EReal.coe_lt_top 0) B.F B.mono B.le B.null
    B.W B.C B.martingale B.cov (fun j k ω r hr _ => B.clock j k ω r hr)
    X ξ hX.initial_adapted
    (fun i t ω => particleCoordinateDrift N d K i (X t ω))
    (fun i j _ _ => if i=j then σ else 0) I
    (fun i t ht => (hc i).measurable.comp (hX.adapted t ht))
    (fun i ω t ht => (hc i).continuousAt.comp (hX.path ω t ht)) hI
    (fun _ _ _ _ => measurable_const) (fun _ _ _ _ _ => continuousAt_const) hIc
    T hT (EReal.coe_lt_top T)
    (he.mono fun ω hω r hr i => hω r hr.1 (EReal.coe_lt_top r) i)
    f ft hf hft hfc hftc hdf hddf
    (fun z => ft (z.2,X (realTimeClamp z.2) z.1)+
      additiveParticleGenerator N d K σ (f z.2) (X (realTimeClamp z.2) z.1))
  apply Filter.Eventually.of_forall
  intro ω r _
  dsimp only [additiveParticleGenerator]
  rw [diagonal_diffusion_trace]
  ring

end WMFKIExternalProbe
