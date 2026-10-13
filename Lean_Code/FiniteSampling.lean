import Lean_Code.SamplingVariance
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace WMFKI

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {A I : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Fintype I]

noncomputable def uniformPopulation (A : Type*) [Fintype A] [Nonempty A]
    [MeasurableSpace A] : Measure A := (PMF.uniformOfFintype A).toMeasure

instance : IsProbabilityMeasure (uniformPopulation A) := by
  unfold uniformPopulation
  infer_instance

noncomputable def populationMean (h : A → ℝ) : ℝ := (∑ a, h a) / Fintype.card A

noncomputable def independentDraws (I A : Type*) [Fintype I] [Fintype A] [Nonempty A]
    [MeasurableSpace A] : Measure (I → A) := Measure.pi (fun _ : I => uniformPopulation A)

instance : IsProbabilityMeasure (independentDraws I A) := by
  unfold independentDraws
  infer_instance

theorem integral_uniformPopulation (h : A → ℝ) :
    (∫ a, h a ∂uniformPopulation A) = populationMean h := by
  rw [uniformPopulation, PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply, populationMean, ← Finset.sum_mul, div_eq_mul_inv,
    mul_comm]

theorem finite_memLp_two {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) :
    MemLp f 2 μ :=
  (memLp_two_iff_integrable_sq (measurable_of_finite f).aestronglyMeasurable).mpr
    Integrable.of_finite

theorem integral_draw_eval (h : A → ℝ) (i : I) :
    (∫ ω, h (ω i) ∂independentDraws I A) = populationMean h := by
  have hp := measurePreserving_eval (fun _ : I => uniformPopulation A) i
  have he := integral_map (μ := independentDraws I A) hp.measurable.aemeasurable
    (measurable_of_finite h).aestronglyMeasurable
  rw [independentDraws, hp.map_eq] at he
  exact he.symm.trans (integral_uniformPopulation h)

theorem draws_independent (h : I → A → ℝ) :
    iIndepFun (fun i ω => h i (ω i)) (independentDraws I A) :=
  iIndepFun_pi (fun i => (measurable_of_finite (h i)).aemeasurable)

theorem centered_draw_mean (h : A → ℝ) (i : I) :
    (∫ ω, (h (ω i) - populationMean h) ∂independentDraws I A) = 0 := by
  rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_draw_eval]
  simp

theorem centered_draw_variance (h : A → ℝ) (i : I) :
    variance (fun ω => h (ω i) - populationMean h) (independentDraws I A) ≤
      populationMean (fun a => h a ^ 2) := by
  rw [variance_sub_const (measurable_of_finite _).aestronglyMeasurable]
  calc
    _ ≤ ∫ ω, h (ω i) ^ 2 ∂independentDraws I A :=
      variance_le_expectation_sq (measurable_of_finite _).aestronglyMeasurable
    _ = _ := integral_draw_eval (fun a => h a ^ 2) i

/-- 一様復元抽出の中心化誤差。平均0も独立性も入力仮定ではない。 -/
noncomputable def samplingError {T P : ℕ} (h : Fin T → A → ℝ) (w : Fin T → ℝ)
    (ω : (Fin T × Fin P) → A) : ℝ :=
  ∑ i : Fin T × Fin P, (w i.1 / P) * (h i.1 (ω i) - populationMean (h i.1))

theorem samplingError_mean {T P : ℕ} (h : Fin T → A → ℝ) (w : Fin T → ℝ) :
    (∫ ω, samplingError h w ω ∂independentDraws (Fin T × Fin P) A) = 0 := by
  classical
  unfold samplingError
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_const_mul, centered_draw_mean, mul_zero]

theorem samplingError_second_moment {T P : ℕ} (hP : 0 < P)
    (h : Fin T → A → ℝ) (w : Fin T → ℝ) (C : ℝ)
    (hC : ∀ t, populationMean (fun a => h t a ^ 2) ≤ C) :
    (∫ ω, samplingError h w ω ^ 2 ∂independentDraws (Fin T × Fin P) A) ≤
      C * (∑ t, w t ^ 2) / P := by
  classical
  have hm := samplingError_mean (P := P) h w
  have hv := variance_eq_sub (finite_memLp_two
    (independentDraws (Fin T × Fin P) A) (samplingError h w))
  simp only [hm, Pi.pow_apply] at hv
  norm_num at hv
  rw [← hv]
  apply refreshed_sampling_variance (μ := independentDraws (Fin T × Fin P) A) hP
    (fun i ω => h i.1 (ω i) - populationMean (h i.1)) w C
    (fun _ => finite_memLp_two _ _)
  · exact fun _ _ hij => (draws_independent
      (fun i : Fin T × Fin P => fun a => h i.1 a - populationMean (h i.1))).indepFun hij
  · intro i
    exact (centered_draw_variance (I := Fin T × Fin P) (h i.1) i).trans (hC i.1)

/-- 時刻ごとの二乗平均を保つ形。観測依存の一様上界を追加しない。 -/
theorem samplingError_second_moment_weighted {T P : ℕ} (hP : 0 < P)
    (h : Fin T → A → ℝ) (w : Fin T → ℝ) :
    (∫ ω, samplingError h w ω ^ 2 ∂independentDraws (Fin T × Fin P) A) ≤
      (∑ t, w t ^ 2 * populationMean (fun a => h t a ^ 2)) / P := by
  classical
  let μ := independentDraws (Fin T × Fin P) A
  let X := fun (i : Fin T × Fin P) (ω : (Fin T × Fin P) → A) =>
    h i.1 (ω i) - populationMean (h i.1)
  have hv := variance_eq_sub (finite_memLp_two μ (samplingError h w))
  have hm := samplingError_mean (P := P) h w
  change (∫ ω, samplingError h w ω ∂μ) = 0 at hm
  simp only [hm, Pi.pow_apply] at hv
  norm_num at hv
  rw [← hv]
  have hind : Pairwise (fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ) :=
    fun _ _ hij => (draws_independent
      (fun i : Fin T × Fin P => fun a => h i.1 a - populationMean (h i.1))).indepFun hij
  change ProbabilityTheory.variance (fun ω => ∑ i, (w i.1 / P) * X i ω) μ ≤ _
  rw [weighted_independent_variance X _ (fun _ => finite_memLp_two μ _) hind]
  have hp : (P : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hP)
  calc
    _ ≤ ∑ i : Fin T × Fin P,
        (w i.1 / P) ^ 2 * populationMean (fun a => h i.1 a ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (centered_draw_variance (h i.1) i) (sq_nonneg _)
    _ = _ := by
      simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro t _
      field_simp

omit [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem populationMean_linear_combination {J : Type*} [Fintype J]
    (v : J → ℝ) (h : J → A → ℝ) :
    populationMean (fun a => ∑ j, v j * h j a) = ∑ j, v j * populationMean (h j) := by
  classical
  unfold populationMean
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum, mul_div_assoc]

omit [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- 全成分で同じ抽出を共有したとき、辞書係数との線形結合を抽出の内側へ移せる。 -/
theorem samplingError_linear_combination {J : Type*} [Fintype J] {T P : ℕ}
    (v : J → ℝ) (h : J → Fin T → A → ℝ) (w : Fin T → ℝ)
    (ω : (Fin T × Fin P) → A) :
    samplingError (fun t a => ∑ j, v j * h j t a) w ω =
      ∑ j, v j * samplingError (h j) w ω := by
  classical
  simp only [samplingError, populationMean_linear_combination]
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- 中心化和が、標本平均と全母集団平均の差そのものであることを確認する。 -/
theorem samplingError_eq_sampled_sub_full {T P : ℕ} (hP : 0 < P)
    (h : Fin T → A → ℝ) (w : Fin T → ℝ) (ω : (Fin T × Fin P) → A) :
    samplingError h w ω =
      (∑ t, w t * (∑ p, h t (ω (t, p))) / P) - ∑ t, w t * populationMean (h t) := by
  classical
  have hp : (P : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hP)
  rw [samplingError, Fintype.sum_prod_type, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  field_simp

end WMFKI
