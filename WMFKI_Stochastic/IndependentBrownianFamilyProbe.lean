import WMFKI_Stochastic.IndependentGaussianFamilyProbe
import EndToEndGaussianBrownianSystem

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Asakura.Chapter2Complete Asakura.Chapter4
namespace WMFKIExternalProbe

/-- All given Brownian coordinates share one constructed augmented filtration.
All-path continuity is an explicit version hypothesis here; it is not inferred
silently from almost-sure continuity. -/
noncomputable def independentBrownianFamilySystem
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (W : Fin n → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P)
    (hm : ∀ i t, Measurable (W i t))
    (hc : ∀ i ω, Continuous (fun t => W i t ω))
    (hI : iIndepFun (fun i ω t => W i t ω) P) : BrownianSystem P n := by
  have hG := independent_gaussian_family P W (fun i => (hW i).isGaussianProcess) hI
  have hcov (i j : Fin n) (u v : ℝ≥0) : cov[W i u, W j v; P] =
      if i = j then ((min u v : ℝ≥0) : ℝ) else 0 := by
    by_cases hij : i = j
    · subst j
      simpa using (hW i).covariance_eval u v
    · simp only [ite_eq_right hij]
      exact ((hI.indepFun hij).comp (measurable_pi_apply u) (measurable_pi_apply v)).covariance_eq_zero
        ((hW i).isGaussianProcess.hasGaussianLaw_eval u).memLp_two
        ((hW j).isGaussianProcess.hasGaussianLaw_eval v).memLp_two
  exact Asakura.EndToEnd.gaussianBrownianSystem P (fun q => W q.1 q.2) hG
    (fun q => hm q.1 q.2) hc (fun i => (hW i).eval_zero_ae_eq_zero)
    (fun q => (hW q.1).integral_eval q.2) hcov

theorem independentBrownianFamilySystem_coordinate
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (W : Fin n → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P)
    (hm : ∀ i t, Measurable (W i t))
    (hc : ∀ i ω, Continuous (fun t => W i t ω))
    (hI : iIndepFun (fun i ω t => W i t ω) P)
    (i : Fin n) (t : HalfClosedTime) (ω : Ω) :
    (independentBrownianFamilySystem P W hW hm hc hI).W i t ω = W i (halfTimeReal t) ω := rfl

/-- Almost-sure continuity suffices. One measurable null set is removed for
all coordinates and all times at once; the resulting drivers are indistinguishable
from the original family, not merely equal at each fixed time separately. -/
theorem exists_brownian_family_system
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (W : Fin n → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsBrownianReal (W i) P)
    (hm : ∀ i t, Measurable (W i t))
    (hI : iIndepFun (fun i ω t => W i t ω) P) :
    ∃ B : BrownianSystem P n,
      ∀ᵐ ω ∂P, ∀ i t, B.W i t ω = W i (halfTimeReal t) ω := by
  classical
  have hc : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => W i t ω) :=
    ae_all_iff.mpr (fun i => (hW i).cont)
  obtain ⟨S,hsub,hSm,hS⟩ := exists_measurable_superset_of_null (ae_iff.mp hc)
  let V := fun i t ω => if ω ∈ S then (0 : ℝ) else W i t ω
  have heq : ∀ᵐ ω ∂P, ∀ i t, V i t ω = W i t ω := by
    filter_upwards [compl_mem_ae_iff.mpr hS] with ω hω
    intro i t
    simp only [V, ite_eq_right hω]
  have hVm i t : Measurable (V i t) :=
    Measurable.ite hSm measurable_const (hm i t)
  have hVc i ω : Continuous (fun t => V i t ω) := by
    by_cases hω : ω ∈ S
    · simpa only [V, ite_eq_left hω] using
        (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : ℝ)))
    · have hh : ∀ j, Continuous (fun t => W j t ω) := by
        by_contra hn
        exact hω (hsub hn)
      simpa only [V, ite_eq_right hω] using hh i
  have hVp i : IsPreBrownianReal (V i) P :=
    (hW i).toIsPreBrownianReal.congr (fun t => heq.mono fun ω hω => (hω i t).symm)
  have hVi : iIndepFun (fun i ω t => V i t ω) P := by
    apply hI.congr
    intro i
    filter_upwards [heq] with ω hω
    funext t
    exact (hω i t).symm
  refine ⟨independentBrownianFamilySystem P V hVp hVm hVc hVi, ?_⟩
  filter_upwards [heq] with ω hω
  intro i t
  exact hω i (halfTimeReal t)

end WMFKIExternalProbe
#print axioms WMFKIExternalProbe.independentBrownianFamilySystem
#print axioms WMFKIExternalProbe.independentBrownianFamilySystem_coordinate
#print axioms WMFKIExternalProbe.exists_brownian_family_system
