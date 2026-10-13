import WMFKI_Stochastic.IndependentBrownianFamilyProbe
import WMFKI_Stochastic.ParticleSystemProbe
import Chapter8IndependentInitialBrownian

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Asakura.Chapter2Complete Asakura.Chapter4
namespace WMFKIExternalProbe

/-- Independent initial randomness and the given Brownian family on their product
space. The original drivers are preserved up to one common null set. -/
theorem exists_initial_brownian_system
    {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (π : Measure E) (P : Measure Ω) [IsProbabilityMeasure π] [IsProbabilityMeasure P]
    {n : ℕ} (W : Fin n → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsBrownianReal (W i) P) (hm : ∀ i t, Measurable (W i t))
    (hI : iIndepFun (fun i ω t => W i t ω) P) :
    ∃ B : BrownianSystem (π.prod P) n,
      (∀ᵐ z ∂π.prod P, ∀ i t, B.W i t z = W i (halfTimeReal t) z.2) ∧
      (∀ t, Measurable[B.F t] (Prod.fst : E × Ω → E)) ∧
      IndepFun (Prod.fst : E × Ω → E)
        (fun z (q : Fin n × HalfClosedTime) => B.W q.1 q.2 z) (π.prod P) := by
  obtain ⟨B,hB⟩ := exists_brownian_family_system P W hW hm hI
  obtain ⟨B',hw',hf⟩ := Asakura.Chapter8.independent_initial_brownian π P B
  have hs : ∀ᵐ z ∂π.prod P, ∀ i t, B.W i t z.2 = W i (halfTimeReal t) z.2 :=
    measurePreserving_snd.quasiMeasurePreserving.ae hB
  have heq : ∀ᵐ z ∂π.prod P, ∀ i t, B'.W i t z = W i (halfTimeReal t) z.2 := by
    filter_upwards [hs] with z hz
    intro i t
    rw [hw']
    exact hz i t
  have hpath : Measurable (fun ω (q : Fin n × HalfClosedTime) => W q.1 (halfTimeReal q.2) ω) :=
    Measurable.of_eval (fun q => hm q.1 (halfTimeReal q.2))
  have hind : IndepFun (Prod.fst : E × Ω → E)
      (fun z (q : Fin n × HalfClosedTime) => W q.1 (halfTimeReal q.2) z.2) (π.prod P) :=
    indepFun_prod measurable_id hpath
  refine ⟨B',heq,hf,hind.congr Filter.EventuallyEq.rfl ?_⟩
  filter_upwards [heq] with z hz
  funext q
  exact (hz q.1 q.2).symm

/-- A genuine interacting particle solution from Brownian laws, independence and
fourth moments of initial particles. BrownianSystem and initial adaptedness are
now constructed, not supplied. This is a theorem on the explicit product model. -/
theorem exists_unique_product_particle_system
    {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (π : Measure E) (P : Measure Ω) [IsProbabilityMeasure π] [IsProbabilityMeasure P]
    (N d : ℕ) (hN : 0 < N)
    [MeasurableSpace (EuclideanSpace ℝ (Fin d))] [BorelSpace (EuclideanSpace ℝ (Fin d))]
    (W : Fin (N*d) → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsBrownianReal (W i) P) (hm : ∀ i t, Measurable (W i t))
    (hI : iIndepFun (fun i ω t => W i t ω) P)
    (ξ : E → Fin N → EuclideanSpace ℝ (Fin d))
    (hξ : ∀ i, Measurable (fun e => ξ e i))
    (hξ4 : ∀ i, MemLp (fun e => ξ e i) 4 π)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℝ) (hL : 0 ≤ L) (hK : ∀ u v, ‖K u - K v‖ ≤ L * ‖u - v‖) (σ : ℝ) :
    ∃ (B : BrownianSystem (π.prod P) (N*d))
      (X : HalfClosedTime → E × Ω → Fin (N*d) → ℝ),
      (∀ᵐ z ∂π.prod P, ∀ i t, B.W i t z = W i (halfTimeReal t) z.2) ∧
      IndepFun (Prod.fst : E × Ω → E)
        (fun z (q : Fin (N*d) × HalfClosedTime) => B.W q.1 q.2 z) (π.prod P) ∧
      VectorSDESolution (π.prod P) B.F B.W (particleCoordinateDrift N d K)
        (fun i j _ => if i = j then σ else 0) (fun z => packParticles N d (ξ z.1)) X ∧
      ∀ Y, VectorSDESolution (π.prod P) B.F B.W (particleCoordinateDrift N d K)
        (fun i j _ => if i = j then σ else 0) (fun z => packParticles N d (ξ z.1)) Y →
        ∀ᵐ z ∂π.prod P, ∀ t, t < ⊤ → X t z = Y t z := by
  obtain ⟨B,hBW,hfst,hind⟩ := exists_initial_brownian_system π P W hW hm hI
  have hinit i : Measurable[B.F ⊥] (fun z : E × Ω => ξ z.1 i) :=
    (hξ i).comp (hfst ⊥)
  have hinit4 i : MemLp (fun z : E × Ω => ξ z.1 i) 4 (π.prod P) :=
    (hξ4 i).comp_measurePreserving measurePreserving_fst
  obtain ⟨X,hX,hunique⟩ := exists_unique_particle_system_of_fourth_moments
    (π.prod P) N d hN B K L hL hK σ (fun z => ξ z.1) hinit hinit4
  exact ⟨B,X,hBW,hind,hX,hunique⟩

end WMFKIExternalProbe
#print axioms WMFKIExternalProbe.exists_initial_brownian_system
#print axioms WMFKIExternalProbe.exists_unique_product_particle_system
