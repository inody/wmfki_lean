import WMFKI_Stochastic.CouplingDriftSplit
import WMFKI_Stochastic.LinearGrowthFluctuationFourth

open MeasureTheory ProbabilityTheory
open WMFKISynchronousModel WMFKIExternalProbe WMFKIIndependentFourth
open scoped BigOperators NNReal
namespace WMFKIRealizedFluctuation

/-- 任意のタグ粒子と残りの全標本の同時法則。ペア独立だけではなく同時独立を使う。 -/
theorem tagged_copy_preserving {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (ρ : Measure E) [IsProbabilityMeasure ρ]
    {n : ℕ} (X : Fin (n+1) → Ω → E) (hm : ∀ j, Measurable (X j))
    (hI : iIndepFun X P) (hL : ∀ j, HasLaw (X j) ρ P) (i : Fin (n+1)) :
    MeasurePreserving (fun ω => (X i ω,fun j : Fin n => X (i.succAbove j) ω))
      P (ρ.prod (Measure.pi (fun _ : Fin n => ρ))) := by
  have hl := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ρ) i).hasLaw.comp (hI.hasLaw_pi hL)
  exact ⟨(hm i).prodMk (Measurable.of_eval (fun j => hm (i.succAbove j))),hl.map_eq⟩

/-- off-diagonal和は、任意タグを飛ばしたn個の和と厳密に一致する。 -/
theorem off_diagonal_succAbove {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (K : E → E) (x : Fin (n+1) → E) (i : Fin (n+1)) :
    particleDrift K x i = ((n+1 : ℕ) : ℝ)⁻¹ • ∑ j : Fin n, K (x i-x (i.succAbove j)) := by
  unfold particleDrift
  rw [Fin.sum_univ_succAbove _ i]
  simp only [ite_true,zero_add,Fin.ne_succAbove,ite_false]

/-- 静的P1の誤差を実際の粒子配列の揺らぎに同定する。自己項補正を落とさない。 -/
theorem fluctuation_tagged_eq {n d : ℕ} (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : Fin (n+1) → EuclideanSpace ℝ (Fin d)) (i : Fin (n+1)) :
    empiricalFluctuation ρ K x i = vectorKernelFluctuation (I := Fin n) d (n+1) ρ
      (fun z => K (z.1-z.2)) (x i,fun j => x (i.succAbove j)) := by
  unfold empiricalFluctuation vectorKernelFluctuation
  rw [off_diagonal_succAbove]

/-- 任意の実際のiid配列へのP1移送。Cは核の二粒子L4積分を上から抑える値。 -/
theorem iid_fluctuation_fourth {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n d : ℕ}
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ρ]
    (X : Fin (n+1) → Ω → EuclideanSpace ℝ (Fin d)) (hm : ∀ j, Measurable (X j))
    (hI : iIndepFun X P) (hL : ∀ j, HasLaw (X j) ρ P)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hKm : Measurable (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => K (z.1-z.2)))
    (hK4 : MemLp (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => K (z.1-z.2)) 4 (ρ.prod ρ))
    (C : ℝ) (hC : 0 ≤ C) (hb : (∫ z, ‖K (z.1-z.2)‖^4 ∂ρ.prod ρ) ≤ C) (i : Fin (n+1)) :
    MemLp (fun ω => empiricalFluctuation ρ K (fun j => X j ω) i) 4 P ∧
    (∫ ω, ‖empiricalFluctuation ρ K (fun j => X j ω) i‖^4 ∂P) ≤
      392*(d : ℝ)^2*C/((n+1 : ℕ) : ℝ)^2 := by
  have hp := tagged_copy_preserving P ρ X hm hI hL i
  obtain ⟨hf,hb'⟩ := vector_kernel_fluctuation_fourth_bound (I := Fin n) ρ ρ d (n+1)
    (by simp) (fun z => K (z.1-z.2)) hKm hK4 C hC hb
  simp_rw [fluctuation_tagged_eq]
  refine ⟨hf.comp_measurePreserving hp,?_⟩
  exact (hp.hasLaw.integral_comp (hf.aestronglyMeasurable.norm.pow 4)).trans_le hb'

end WMFKIRealizedFluctuation
