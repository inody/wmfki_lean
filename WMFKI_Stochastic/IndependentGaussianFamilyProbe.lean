import EndToEndIndependentGaussianPair

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace WMFKIExternalProbe

/-- Finite independent Gaussian processes are jointly Gaussian, including mixed
samples across times and coordinates. Uses the finite masked-sum construction of
Asakura.independent_copies_gaussian (Apache-2.0), without the identical-law or
countable-copy restriction. -/
theorem independent_gaussian_family
    {Ω T : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (W : Fin n → T → Ω → ℝ)
    (hW : ∀ i, IsGaussianProcess (W i) P)
    (hI : iIndepFun (fun i ω t => W i t ω) P) :
    IsGaussianProcess (fun q : Fin n × T => W q.1 q.2) P := by
  classical
  constructor
  intro S
  let A (i : Fin n) : (T → ℝ) → S → ℝ :=
    fun w q => if q.val.1 = i then w q.val.2 else 0
  have hA i : Measurable (A i) := by
    apply Measurable.of_eval
    intro q
    by_cases h : q.val.1 = i
    · simpa only [A, ite_eq_left h] using measurable_pi_apply q.val.2
    · simpa only [A, ite_eq_right h] using
        (measurable_const : Measurable (fun _ : T → ℝ => (0 : ℝ)))
  have hG i : HasGaussianLaw (A i ∘ (fun ω t => W i t ω)) P := by
    let L : (S → ℝ) →L[ℝ] (S → ℝ) := ContinuousLinearMap.pi
      (fun q => if q.val.1 = i then ContinuousLinearMap.proj q else 0)
    convert (Asakura.gaussian_finite_samples (hW i) (fun q : S => q.val.2)).map L using 1
    ext ω q
    by_cases h : q.val.1 = i <;> simp [A, L, h]
  have hs := (hI.comp A hA).hasGaussianLaw_fun_sum hG
  convert hs using 1
  ext ω q
  simp [A]

end WMFKIExternalProbe
#print axioms WMFKIExternalProbe.independent_gaussian_family
