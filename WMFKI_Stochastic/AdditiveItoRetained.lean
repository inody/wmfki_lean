import WMFKI_Stochastic.SDEItoRetained
import WMFKI_Stochastic.WeightedParticleIto

open MeasureTheory Set
open scoped BigOperators
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
namespace WMFKIExternalProbe

/-- C1 in time and C2 in space suffice; no C2 time assumption is added.
The residual is proved to be a local martingale, not assumed to have that property. -/
theorem additive_c12_retained
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
    (hftc : Continuous ft)
    (hdf : Continuous (fun z : ℝ × (Fin (N*d) → ℝ) => fderiv ℝ (f z.1) z.2))
    (hddf : Continuous (fun z : ℝ × (Fin (N*d) → ℝ) => fderiv ℝ (fderiv ℝ (f z.1)) z.2))
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ Y Z : Fin (N*d) → HalfClosedTime → Ω → ℝ,
      (∀ i ω,Continuous (fun t => Y i t ω)) ∧
      (∀ᵐ ω ∂P,∀ r∈Icc 0 T,(fun i => Y i (realTimeClamp r) ω)=X (realTimeClamp r) ω) ∧
      (∀ i,LocalMProcessWitness P B.F (Z i)) ∧
      (∀ i,ItoCovarianceFormula P B.F (fun t ω => σ*B.W i (min (realTimeClamp T) t) ω)
        (fun z => fderiv ℝ (f ((finitePrefixTime (T := ⊤) T hT (realTimeClamp z.2)).val))
          (fun k => Y k (realTimeClamp z.2) z.1) (Pi.single i 1)) (Z i)) ∧
      LocalMProcessWitness P B.F (fun t ω => ∑ i,Z i t ω) ∧
      ∀ t, t ∈ Icc 0 T → (fun ω => f t (X (realTimeClamp t) ω)) =ᵐ[P]
        fun ω => f 0 (X ⊥ ω)+(∑ i,Z i (realTimeClamp t) ω)+
          ∫ s in 0..t, ft (s,X (realTimeClamp s) ω)+
            additiveParticleGenerator N d K σ (f s) (X (realTimeClamp s) ω) := by
  classical
  let I := fun (i j : Fin (N*d)) t ω => (if i=j then σ else 0)*B.W j t ω
  have hI i j : LocalMProcessWitness P B.F (I i j) := (B.martingale j).smul P B.F _
  have hIc i j := Asakura.Chapter11.constant_ito_integral P (EReal.coe_lt_top 0)
    B.F B.mono B.le B.null (B.W j) (B.martingale j) (if i=j then σ else 0)
  have he := additive_sde_equation P B (particleCoordinateDrift N d K) σ ξ X hX
  have hc i := particleCoordinateDrift_continuous N d K hK i
  have hrep := sde_drift_retained P (EReal.coe_lt_top 0) B.F B.mono B.le B.null
    B.W B.C B.martingale B.cov (fun j k ω r hr _ => B.clock j k ω r hr)
    X ξ hX.initial_adapted
    (fun i t ω => particleCoordinateDrift N d K i (X t ω))
    (fun i j _ _ => if i=j then σ else 0) I
    (fun i t ht => (hc i).measurable.comp (hX.adapted t ht))
    (fun i ω t ht => (hc i).continuousAt.comp (hX.path ω t ht)) hI
    (fun _ _ _ _ => measurable_const) (fun _ _ _ _ _ => continuousAt_const) hIc
    T hT (EReal.coe_lt_top T)
    (he.mono fun ω hω r hr i => by simpa [I,ite_mul] using hω r hr.1 i)
    f ft hf hft hftc hdf hddf
    (fun z => ft (z.2,X (realTimeClamp z.2) z.1)+
      additiveParticleGenerator N d K σ (f z.2) (X (realTimeClamp z.2) z.1))
    (Filter.Eventually.of_forall (fun ω r _ => by
      dsimp only [additiveParticleGenerator]
      rw [diagonal_diffusion_trace]
      ring))
  simpa [I,ite_mul] using hrep

end WMFKIExternalProbe
