import WMFKI_Stochastic.AdditiveItoRetained
import WMFKI_Stochastic.ItoIntegrandCommonDomain
import WMFKI_Stochastic.FiniteBrownianEnergy
import Chapter2ItoAssociativity

open MeasureTheory Set Filter
open scoped BigOperators
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
namespace WMFKIExternalProbe

/-- The actual weighted Ito identity uses the supplied, characterized
Brownian integrals. Association and common-event integrand congruence identify
the retained C1,2 integrals, with no independence or moment assumptions. -/
theorem weighted_particle_brownian_identity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N d : ℕ) (B : BrownianSystem P (N*d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : Continuous K)
    (σ : ℝ) (ξ : Ω → Fin (N*d) → ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hX : VectorSDESolution P B.F B.W (particleCoordinateDrift N d K)
      (fun i j _ => if i=j then σ else 0) ξ X)
    (f : (Fin (N*d) → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ) (T : ℝ) (hT : 0 ≤ T)
    (M : Fin (N*d) → HalfClosedTime → Ω → ℝ)
    (hM : ∀ i, LocalMProcessWitness P B.F (M i))
    (hMI : ∀ i, ItoCovarianceFormula P B.F (B.W i)
      (fun z => (Iic T).indicator (fun r => σ*ψ r*fderiv ℝ f (X (realTimeClamp r) z.1) (Pi.single i 1)) z.2) (M i)) :
    ∀ t, t ∈ Icc 0 T → (fun ω => ψ t*f (X (realTimeClamp t) ω)) =ᵐ[P]
      fun ω => ψ 0*f (X ⊥ ω)+(∑ i,M i (realTimeClamp t) ω)+
        ∫ s in 0..t, deriv ψ s*f (X (realTimeClamp s) ω)+
          ψ s*additiveParticleGenerator N d K σ f (X (realTimeClamp s) ω) := by
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := (contDiff_succ_iff_fderiv (n := 1)).mp hf |>.2.2
  have hdf t x : fderiv ℝ (fun y => ψ t*f y) x = ψ t • fderiv ℝ f x :=
    fderiv_const_mul (hf.differentiable (by norm_num) x) (ψ t)
  have hddf t x := fderiv_fderiv_const_mul f hf (ψ t) x
  have hc1 : Continuous (fun z : ℝ × (Fin (N*d) → ℝ) => fderiv ℝ (fun y => ψ z.1*f y) z.2) := by
    simp_rw [hdf]
    exact (hψ.continuous.comp continuous_fst).smul ((hf.continuous_fderiv (by norm_num)).comp continuous_snd)
  have hc2 : Continuous (fun z : ℝ × (Fin (N*d) → ℝ) => fderiv ℝ (fderiv ℝ (fun y => ψ z.1*f y)) z.2) := by
    simp_rw [hddf]
    exact (hψ.continuous.comp continuous_fst).smul ((hf1.continuous_fderiv (by norm_num)).comp continuous_snd)
  obtain ⟨Y,Z,hYc,hYX,hZ,hZI,_,he⟩ := additive_c12_retained P N d B K hK σ ξ X hX
    (fun t x => ψ t*f x) (fun z => deriv ψ z.1*f z.2)
    (fun _ => contDiff_const.mul hf)
    (fun t x => (hψ.differentiable (by norm_num) t).hasDerivAt.mul_const (f x))
    (((hψ.continuous_deriv le_rfl).comp continuous_fst).mul (hf.continuous.comp continuous_snd))
    hc1 hc2 T hT
  let A := fun z : Ω × ℝ => (Ioc 0 T).indicator (fun _ => σ) z.2
  let U := fun i (z : Ω × ℝ) =>
    fderiv ℝ (fun x => ψ ((finitePrefixTime (T := ⊤) T hT (realTimeClamp z.2)).val)*f x)
      (fun k => Y k (realTimeClamp z.2) z.1) (Pi.single i 1)
  have hUm i ω : Measurable (fun r => U i (ω,r)) := by
    have hp : Continuous (fun r : ℝ => (finitePrefixTime (T := ⊤) T hT (realTimeClamp r)).val) :=
      (continuous_subtype_val.comp (finite_prefix_time_continuous T hT)).comp real_time_clamp_continuous
    have hy : Continuous (fun r : ℝ => fun k => Y k (realTimeClamp r) ω) :=
      continuous_pi (fun k => (hYc k ω).comp real_time_clamp_continuous)
    exact ((hc1.clm_apply continuous_const).comp (hp.prodMk hy)).measurable
  have hstop t : MeasurableSet[B.F t] {ω : Ω | realTimeClamp (T := (⊤ : EReal)) T ≤ t} := by
    by_cases h : realTimeClamp (T := (⊤ : EReal)) T ≤ t <;> simp [h]
  have hL i : LocalMProcessWitness P B.F (fun t ω => σ*B.W i (min (realTimeClamp T) t) ω) :=
    ((B.martingale i).smul P B.F σ).stopped P B.F B.mono B.le (fun _ => realTimeClamp T) hstop
  have hLI i : ItoCovarianceFormula P B.F (B.W i) A
      (fun t ω => σ*B.W i (min (realTimeClamp T) t) ω) := by
    exact Asakura.Chapter5.stopped_ito_covariance_formula P (EReal.coe_lt_top 0)
      B.F B.mono B.le B.null (B.W i) (fun t ω => σ*B.W i t ω) (fun _ => σ)
      (B.martingale i) ((B.martingale i).smul P B.F σ) (fun _ => measurable_const)
      (Asakura.Chapter11.constant_ito_integral P (EReal.coe_lt_top 0) B.F B.mono B.le B.null
        (B.W i) (B.martingale i) σ) T hT
  have hproduct i : ItoCovarianceFormula P B.F (B.W i) (fun z => U i z*A z) (M i) := by
    apply ito_integrand_positive_common_ae P B.F (B.W i) (M i) _ _ (hMI i)
    filter_upwards [hYX] with ω hω
    intro r hr _
    by_cases hrT : r ≤ T
    · dsimp only [U,A]
      rw [Set.indicator_of_mem (show r ∈ Iic T from hrT),
        Set.indicator_of_mem (show r ∈ Ioc 0 T from ⟨hr,hrT⟩),
        finite_prefix_time_of_real T r hT ⟨hr.le,hrT⟩ le_top,hω r ⟨hr.le,hrT⟩,hdf]
      simp only [smul_apply,smul_eq_mul]
      ring
    · have hn : r ∉ Ioc 0 T := fun h => hrT h.2
      simp only [A,Set.indicator_of_notMem (show r ∉ Iic T from hrT),Set.indicator_of_notMem hn,mul_zero]
  have hassoc i := ito_integral_associativity P (EReal.coe_lt_top 0) B.F B.mono B.le B.null
    (B.W i) (fun t ω => σ*B.W i (min (realTimeClamp T) t) ω) (Z i) (M i) A (U i)
    (B.martingale i) (hL i) (hZ i) (hM i)
    (fun _ => measurable_const.indicator measurableSet_Ioc) (hUm i) (hLI i) (hZI i) (hproduct i)
  intro t ht
  filter_upwards [he t ht,ae_all_iff.mpr hassoc] with ω hω hi
  have hfinite := real_time_below t ht.1 (EReal.coe_lt_top t)
  have hs : (∑ i,Z i (realTimeClamp t) ω) = ∑ i,M i (realTimeClamp t) ω :=
    Finset.sum_congr rfl (fun i _ => hi i _ hfinite)
  rw [hs] at hω
  simpa only [additiveParticleGenerator_const_mul N d K σ f hf] using hω

end WMFKIExternalProbe
