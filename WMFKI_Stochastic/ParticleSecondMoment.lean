import WMFKI_Stochastic.ParticleSDEEnvelope
import WMFKI_Stochastic.ParticleEnvelopeMoments

open MeasureTheory Set
open scoped BigOperators
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
namespace WMFKIExternalProbe

/-- Explicit bound; neither the particle number N nor the label i occurs. -/
noncomputable def particleSecondMomentBound (G T σ : ℝ) (d : ℕ) (R : ℝ) : ℝ :=
  6*(Real.exp ((G+1)*T))^2 * (1+((G+1)*T*Real.exp (2*(G+1)*T))^2) *
    (R+σ^2*(4*(d : ℝ)^2*T)+((G+1)*T)^2)

theorem particle_solution_L2_envelopes
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N d : ℕ) (hN : 0 < N) (B : BrownianSystem P (N*d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hKc : Continuous K)
    (G : ℝ) (hG : 0 ≤ G) (hK : ∀ z, ‖K z‖ ≤ G*(1+‖z‖))
    (σ T R : ℝ) (hT : 0 ≤ T) (ξ : Ω → Fin (N*d) → ℝ)
    (hξ : ∀ i, MemLp (fun ω => particlePositions N d (ξ ω) i) 2 P)
    (hξb : ∀ i, (∫ ω, ‖particlePositions N d (ξ ω) i‖^2 ∂P) ≤ R)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hX : VectorSDESolution P B.F B.W (particleCoordinateDrift N d K)
      (fun i j _ => if i = j then σ else 0) ξ X) :
    ∃ F : Fin N → Ω → ℝ,
      (∀ i, MemLp (F i) 2 P) ∧ (∀ i ω, 0 ≤ F i ω) ∧
      (∀ i, (∫ ω, (F i ω)^2 ∂P) ≤ particleSecondMomentBound G T σ d R) ∧
      ∀ᵐ ω ∂P, ∀ i t, t ∈ Icc 0 T →
        ‖particlePositions N d (X (realTimeClamp t) ω) i‖ ≤ F i ω := by
  obtain ⟨H,hHm,hHn,hHb,hpath⟩ := particle_sde_envelope P N d hN B K hKc G hG hK σ T hT ξ X hX
  let a := fun i ω => ‖particlePositions N d (ξ ω) i‖ + |σ| * H i ω + (G+1)*T
  let A := 3*(R+σ^2*(4*(d : ℝ)^2*T)+((G+1)*T)^2)
  have ha i : MemLp (a i) 2 P ∧ (∫ ω, (a i ω)^2 ∂P) ≤ A := by
    have hσ : (∫ ω, (|σ| * H i ω)^2 ∂P) ≤ σ^2*(4*(d : ℝ)^2*T) := by
      simp_rw [mul_pow,sq_abs]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hHb i) (sq_nonneg σ)
    exact three_l2_moment (fun ω => ‖particlePositions N d (ξ ω) i‖)
      (fun ω => |σ| * H i ω) (fun _ => (G+1)*T)
      (hξ i).norm ((hHm i).const_mul |σ|) (memLp_const _)
      R (σ^2*(4*(d : ℝ)^2*T)) (((G+1)*T)^2) (hξb i) hσ (by simp)
  let c := (G+1)*T*Real.exp (2*(G+1)*T)
  let e := Real.exp ((G+1)*T)
  let F := fun i ω => (a i ω + c*((N : ℝ)⁻¹ * ∑ j, a j ω))*e
  have hF i := comparison_envelope_l2 hN a (fun i => (ha i).1) A (fun i => (ha i).2) c e i
  refine ⟨F,(fun i => (hF i).1),?_,?_,?_⟩
  · intro i ω
    have han j : 0 ≤ a j ω := by
      have hh := hHn j ω
      dsimp [a]
      positivity
    have hav : 0 ≤ (N : ℝ)⁻¹ * ∑ j, a j ω :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => han j)
    have hc : 0 ≤ c := by dsimp [c]; positivity
    exact mul_nonneg (add_nonneg (han i) (mul_nonneg hc hav)) (le_of_lt (Real.exp_pos _))
  · intro i
    apply (hF i).2.trans_eq
    dsimp only [A,c,e,particleSecondMomentBound]
    ring
  · filter_upwards [hpath] with ω hω
    intro i t ht
    apply (hω i t ht).trans_eq
    dsimp only [F,c,e]
    change (_ + (G+1)*T*((N : ℝ)⁻¹ * ∑ j, a j ω)*Real.exp (2*(G+1)*T))*Real.exp ((G+1)*T) = _
    ring

/-- Actual solution components are L² and obey a common N-independent bound.
Integrability is concluded from the envelope before comparing the expectations. -/
theorem particle_solution_uniform_second_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N d : ℕ) (hN : 0 < N) (B : BrownianSystem P (N*d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hKc : Continuous K)
    (G : ℝ) (hG : 0 ≤ G) (hK : ∀ z, ‖K z‖ ≤ G*(1+‖z‖))
    (σ T R : ℝ) (hT : 0 ≤ T) (ξ : Ω → Fin (N*d) → ℝ)
    (hξ : ∀ i, MemLp (fun ω => particlePositions N d (ξ ω) i) 2 P)
    (hξb : ∀ i, (∫ ω, ‖particlePositions N d (ξ ω) i‖^2 ∂P) ≤ R)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hX : VectorSDESolution P B.F B.W (particleCoordinateDrift N d K)
      (fun i j _ => if i = j then σ else 0) ξ X) :
    ∀ i t, t ∈ Icc 0 T →
      MemLp (fun ω => particlePositions N d (X (realTimeClamp t) ω) i) 2 P ∧
      (∫ ω, ‖particlePositions N d (X (realTimeClamp t) ω) i‖^2 ∂P) ≤
        particleSecondMomentBound G T σ d R := by
  obtain ⟨F,hFm,hFn,hFb,hdom⟩ :=
    particle_solution_L2_envelopes P N d hN B K hKc G hG hK σ T R hT ξ hξ hξb X hX
  intro i t ht
  have hmeas : AEStronglyMeasurable (fun ω => particlePositions N d (X (realTimeClamp t) ω) i) P :=
    (continuous_particlePositions N d i).comp_aestronglyMeasurable
      (((hX.adapted _ (real_time_below t ht.1 (EReal.coe_lt_top _))).mono (B.le _) le_rfl).aestronglyMeasurable)
  have hm := (hFm i).of_le hmeas (by
    filter_upwards [hdom] with ω hω
    simpa only [Real.norm_of_nonneg (hFn i ω)] using hω i t ht)
  refine ⟨hm,?_⟩
  apply (integral_mono_ae hm.norm.integrable_sq (hFm i).integrable_sq ?_).trans (hFb i)
  filter_upwards [hdom] with ω hω
  exact pow_le_pow_left₀ (norm_nonneg _) (hω i t ht) 2

end WMFKIExternalProbe
#print axioms WMFKIExternalProbe.particle_solution_L2_envelopes
#print axioms WMFKIExternalProbe.particle_solution_uniform_second_moment
