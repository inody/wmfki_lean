import WMFKI_Stochastic.ParticleCoordinatesProbe
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

open MeasureTheory
namespace WMFKIExternalProbe

noncomputable def packParticles (N d : ℕ) (x : Fin N → EuclideanSpace ℝ (Fin d)) :
    Fin (N*d) → ℝ := fun k => x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

theorem particlePositions_pack (N d : ℕ) (x : Fin N → EuclideanSpace ℝ (Fin d)) :
    particlePositions N d (packParticles N d x) = x := by
  ext i a
  simp [particlePositions, packParticles]

theorem pack_particlePositions (N d : ℕ) (x : Fin (N*d) → ℝ) :
    packParticles N d (particlePositions N d x) = x := by
  funext k
  change x (finProdFinEquiv (finProdFinEquiv.symm k)) = x k
  rw [Equiv.apply_symm_apply]

theorem packParticles_measurable
    {Ω : Type*} [MeasurableSpace Ω] (N d : ℕ)
    [MeasurableSpace (EuclideanSpace ℝ (Fin d))] [BorelSpace (EuclideanSpace ℝ (Fin d))]
    (ξ : Ω → Fin N → EuclideanSpace ℝ (Fin d))
    (hξ : ∀ i, Measurable (fun ω => ξ ω i)) :
    Measurable (fun ω => packParticles N d (ξ ω)) := by
  apply Measurable.of_eval
  intro k
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) (finProdFinEquiv.symm k).2).continuous.measurable.comp
    (hξ (finProdFinEquiv.symm k).1)

theorem packParticles_memLp
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N d : ℕ) (p : ENNReal)
    (ξ : Ω → Fin N → EuclideanSpace ℝ (Fin d))
    (hξ : ∀ i, MemLp (fun ω => ξ ω i) p P) :
    MemLp (fun ω => packParticles N d (ξ ω)) p P := by
  apply MemLp.of_eval
  intro k
  exact (hξ (finProdFinEquiv.symm k).1).eval_piLp (finProdFinEquiv.symm k).2

theorem packParticles_memLp_two_of_four
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (N d : ℕ)
    (ξ : Ω → Fin N → EuclideanSpace ℝ (Fin d))
    (hξ : ∀ i, MemLp (fun ω => ξ ω i) 4 P) :
    MemLp (fun ω => packParticles N d (ξ ω)) 2 P := by
  exact (packParticles_memLp P N d 4 ξ hξ).mono_exponent (by norm_num)

end WMFKIExternalProbe
#print axioms WMFKIExternalProbe.packParticles_memLp_two_of_four
