import WMFKI_Stochastic.MeanFieldCopyFiltration
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace WMFKIMeanFieldCopies
variable {Ω Ω' I J : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype I]
  {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

omit [IsProbabilityMeasure P] in
/-- 有限族の同時独立性を、その全同時法則を通じて移送する。 -/
theorem independent_family_pullback {E : I → Type*} [∀ i, MeasurableSpace (E i)]
    {φ : Ω' → Ω} (hφ : MeasurePreserving φ Q P) (X : ∀ i, Ω → E i)
    (hm : ∀ i, Measurable (X i)) (hI : iIndepFun X P) :
    iIndepFun (fun i ω => X i (φ ω)) Q := by
  have hL (i : I) := (hasLaw_map (hm i).aemeasurable).comp hφ.hasLaw
  apply (iIndepFun_iff_hasLaw_pi_pi hL).mpr
  exact (hI.hasLaw_pi (fun i => hasLaw_map (hm i).aemeasurable)).comp hφ.hasLaw

omit [IsProbabilityMeasure P] [IsProbabilityMeasure Q] in
/-- 各時刻の等分布だけでなく、a.s.連続性も同時に引き戻す。 -/
theorem brownian_pullback {φ : Ω' → Ω} (hφ : MeasurePreserving φ Q P)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    IsBrownianReal (fun t ω => B t (φ ω)) Q :=
  ⟨⟨fun S => (hB.hasLaw S).comp hφ.hasLaw⟩,hφ.quasiMeasurePreserving.ae hB.cont⟩

/-- 独立なブロックの内部にも独立な座標があれば、全(i,j)座標は同時独立。
    相互作用過程の独立性をここから推論してはいけない。 -/
theorem replicated_brownian_family [Fintype J] (B : J → ℝ≥0 → Ω → ℝ)
    (hB : ∀ j, IsBrownianReal (B j) P) (hm : ∀ j t, Measurable (B j t))
    (hI : iIndepFun (fun j ω t => B j t ω) P) :
    (∀ p : I × J, IsBrownianReal (fun t (ω : I → Ω) => B p.2 t (ω p.1)) (Measure.pi (fun _ : I => P))) ∧
    (∀ (p : I × J) t, Measurable (fun ω : I → Ω => B p.2 t (ω p.1))) ∧
    iIndepFun (fun (p : I × J) (ω : I → Ω) t => B p.2 t (ω p.1)) (Measure.pi (fun _ : I => P)) := by
  refine ⟨fun p => brownian_pullback (measurePreserving_eval (fun _ : I => P) p.1) (B p.2) (hB p.2),
    fun p t => (hm p.2 t).comp (measurable_pi_apply p.1),?_⟩
  have hpath (j : J) : Measurable (fun ω t => B j t ω) := Measurable.of_eval (hm j)
  apply iIndepFun_uncurry'
    (X := fun (i : I) (j : J) (ω : I → Ω) t => B j t (ω i))
    (fun i j => (hpath j).comp (measurable_pi_apply i))
  · exact iIndepFun_pi (fun _ => (Measurable.of_eval hpath).aemeasurable)
  · intro i
    exact independent_family_pullback (measurePreserving_eval (fun _ : I => P) i)
      (fun j ω t => B j t ω) hpath hI

end WMFKIMeanFieldCopies
