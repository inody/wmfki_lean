import WMFKI_Stochastic.ObservationDerivativeBounds

open MeasureTheory ProbabilityTheory Set
namespace WMFKIExternalProbe

/-- Primitive sampled positions and additive errors. The independence field
is noise versus latent data only; errors may be mutually dependent and biased. -/
structure ObservationSamples {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E]
    (P : Measure Ω) (N nt : ℕ) (R q : ℝ) where
  pos : Fin nt → Fin N → Ω → E
  noise : Fin nt → Fin N → Ω → E
  pos_meas : ∀ t i, Measurable (pos t i)
  noise_meas : ∀ t i, Measurable (noise t i)
  pos_lp : ∀ t i, MemLp (pos t i) 2 P
  noise_lp : ∀ t i, MemLp (noise t i) 2 P
  pos_moment : ∀ t i, (∫ ω, ‖pos t i ω‖^2 ∂P) ≤ R
  noise_moment : ∀ t i, (∫ ω, ‖noise t i ω‖^2 ∂P) ≤ q
  independent : ∀ t i j, IndepFun (noise t i) (pos t j) P

/-- An arbitrary jointly distributed error family can be attached independently
to an already constructed latent realization. No within-family independence is
assumed. This does not assert transfer to an arbitrary pre-existing realization. -/
noncomputable def independentObservationSamples
    {Ω Ξ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [NormedAddCommGroup E] [MeasurableSpace E]
    (P : Measure Ω) (Q : Measure Ξ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (N nt : ℕ) (R q : ℝ) (x : Fin nt → Fin N → Ω → E) (e : Fin nt → Fin N → Ξ → E)
    (hxm : ∀ t i, Measurable (x t i)) (hem : ∀ t i, Measurable (e t i))
    (hx : ∀ t i, MemLp (x t i) 2 P) (he : ∀ t i, MemLp (e t i) 2 Q)
    (hxR : ∀ t i, (∫ ω, ‖x t i ω‖^2 ∂P) ≤ R)
    (heq : ∀ t i, (∫ ω, ‖e t i ω‖^2 ∂Q) ≤ q) :
    ObservationSamples (E := E) (P.prod Q) N nt R q where
  pos := fun t i z => x t i z.1
  noise := fun t i z => e t i z.2
  pos_meas := fun t i => (hxm t i).comp measurable_fst
  noise_meas := fun t i => (hem t i).comp measurable_snd
  pos_lp := fun t i => (hx t i).comp_measurePreserving (measurePreserving_fst (μ := P) (ν := Q))
  noise_lp := fun t i => (he t i).comp_measurePreserving (measurePreserving_snd (μ := P) (ν := Q))
  pos_moment := by
    intro t i
    rw [integral_fun_fst (fun ω => ‖x t i ω‖^2)]
    simpa using hxR t i
  noise_moment := by
    intro t i
    rw [integral_fun_snd (fun ω => ‖e t i ω‖^2)]
    simpa using heq t i
  independent := fun t i j => (indepFun_prod (μ := P) (ν := Q) (hxm t j) (hem t i)).symm

end WMFKIExternalProbe
