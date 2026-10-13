import WMFKI_Stochastic.MeanFieldPicardPullback

open MeasureTheory ProbabilityTheory Set
open WMFKIMeanFieldPicard WMFKIMeanFieldAdapted
open scoped NNReal

namespace WMFKIMeanFieldCopies
variable {Ω E I : Type*} [MeasurableSpace Ω] [Fintype I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℝ} {X Z : ℝ → Ω → E}

/-- コピーは独立な標本の座標評価で明示的に定義する。 -/
def copyProcess (X : ℝ → Ω → E) (i : I) (t : ℝ) (ω : I → Ω) : E := X t (ω i)

/-- 対象有限区間の経路全体。可測空間は各時刻評価で生成される。 -/
def finiteTrajectory (T : ℝ) (X : ℝ → Ω → E) (ω : Ω) (t : Icc (0 : ℝ) T) : E := X t ω

omit [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure P] in
theorem finite_trajectory_measurable (hX : FiniteL4Paths P T X) : Measurable (finiteTrajectory T X) :=
  Measurable.of_eval (fun t => hX.measurable t t.property)

omit [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
/-- 各コピーの法則は実際の同じ周辺法則。 -/
theorem copy_hasLaw (hX : FiniteL4Paths P T X) (i : I) (t : ℝ) (ht : t ∈ Icc 0 T) :
    HasLaw (copyProcess X i t) (P.map (X t)) (Measure.pi (fun _ : I => P)) :=
  pullback_hasLaw (measurePreserving_eval (fun _ : I => P) i) (hX.measurable t ht)

omit [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
/-- 時刻ごとの独立性だけでなく、各コピーの有限区間経路全体の独立性。 -/
theorem copies_independent_paths (hX : FiniteL4Paths P T X) :
    iIndepFun (fun i : I => finiteTrajectory T (copyProcess X i)) (Measure.pi (fun _ : I => P)) :=
  iIndepFun_pi (fun _ => (finite_trajectory_measurable hX).aemeasurable)

omit [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
/-- 経路全体の同一法則と同時積法則。 -/
theorem copies_joint_path_law (hX : FiniteL4Paths P T X) :
    HasLaw (fun ω : I → Ω => fun i => finiteTrajectory T (copyProcess X i) ω)
      (Measure.pi (fun _ : I => P.map (finiteTrajectory T X))) (Measure.pi (fun _ : I => P)) :=
  (copies_independent_paths hX).hasLaw_pi (fun i =>
    (hasLaw_map (finite_trajectory_measurable hX).aemeasurable).comp
      (measurePreserving_eval (fun _ : I => P) i).hasLaw)

omit [NormedSpace ℝ E] in
/-- 第4モーメントの定数をNとラベルと時刻より先に選ぶ。 -/
theorem copies_uniform_fourth (hX : FiniteL4Paths P T X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ i : Fin N, ∀ t ∈ Icc 0 T,
      MemLp (copyProcess X i t) 4 (Measure.pi (fun _ : Fin N => P)) ∧
      (∫ ω, ‖copyProcess X i t ω‖^4 ∂(Measure.pi (fun _ : Fin N => P))) ≤ C := by
  obtain ⟨C,hC,hb⟩ := hX.uniform_fourth
  refine ⟨C,hC,fun N i t ht => ?_⟩
  have hp := measurePreserving_eval (fun _ : Fin N => P) i
  refine ⟨(hX.memLp t ht).comp_measurePreserving hp,?_⟩
  have he : (∫ ω, ‖copyProcess X i t ω‖^4 ∂(Measure.pi (fun _ : Fin N => P))) =
      ∫ ω, ‖X t ω‖^4 ∂P := hp.hasLaw.integral_comp ((hX.measurable t ht).norm.pow_const 4).aestronglyMeasurable
  rw [he]
  exact hb t ht

/-- 全ラベル・全時刻の共通確率1集合上で、コピー自身の法則を用いた方程式が成立。 -/
theorem copies_common_equation (hX : FiniteL4Paths P T X) {K : E → E} {L : ℝ≥0}
    (hK : LipschitzWith L K) (he : MeanFieldEquation P K T Z X) :
    ∀ᵐ ω ∂(Measure.pi (fun _ : I => P)), ∀ i : I, ∀ t ∈ Icc 0 T,
      copyProcess X i t ω = copyProcess Z i t ω + ∫ s in (0 : ℝ)..t,
        lawDrift (Measure.pi (fun _ : I => P)) K (copyProcess X i s) (copyProcess X i s ω) :=
  ae_all_iff.mpr (fun i => mean_field_equation_pullback
    (measurePreserving_eval (fun _ : I => P) i) hK hX he)

omit [BorelSpace E] [SecondCountableTopology E] in
/-- 全コピーで共通の元の母集団法則による実際の方程式。 -/
theorem copies_population_equation {K : E → E}
    (he : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, X t ω = Z t ω +
      ∫ s in (0 : ℝ)..t, ∫ y, K (X s ω-y) ∂(P.map (X s))) :
    ∀ᵐ ω ∂(Measure.pi (fun _ : I => P)), ∀ i : I, ∀ t ∈ Icc 0 T,
      copyProcess X i t ω = copyProcess Z i t ω + ∫ s in (0 : ℝ)..t,
        ∫ y, K (copyProcess X i s ω-y) ∂(P.map (X s)) :=
  ae_all_iff.mpr (fun i => (measurePreserving_eval (fun _ : I => P) i).quasiMeasurePreserving.ae he)

omit [Fintype I] [NormedSpace ℝ E] in
/-- 構成後の全経路連続版について、時間と標本の共同強可測性。 -/
theorem copy_jointly_measurable (hm : ∀ t, Measurable (X t))
    (hc : ∀ ω, Continuous (fun t => X t ω)) (i : I) :
    StronglyMeasurable (fun z : ℝ × (I → Ω) => copyProcess X i z.1 z.2) :=
  stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable (fun ω : I → Ω => hc (ω i))
    (fun t => ((hm t).comp (measurable_pi_apply i)).stronglyMeasurable)

end WMFKIMeanFieldCopies
