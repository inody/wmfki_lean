import Showcase
import Lean_Code.Main

/-! 証明と独立に読める定義照合、および推移的公理依存の監査。 -/

namespace WMFKI.HumanCheck

open MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

example (A : E →L[ℝ] F) (γ : ℝ) :
    LowerBound A γ ↔ ∀ u, γ * ‖u‖ ≤ ‖A u‖ := Iff.rfl

example (B : E →L[ℝ] F) (y : F) (θhat : E) :
    IsLeastSquares B y θhat ↔ ∀ θ, ‖B θhat - y‖ ^ 2 ≤ ‖B θ - y‖ ^ 2 := Iff.rfl

/-- 有限次元の実Euclidean空間で同じ仕様が成立する。 -/
example (s L : ℕ) :
    OracleRecoveryStatement (E := EuclideanSpace ℝ (Fin s))
      (F := EuclideanSpace ℝ (Fin L)) :=
  Showcase.oracle_recovery

/-- 下界仮定は零写像・正のγに対して成立しない（空虚な定義ではない）。 -/
example : ¬ LowerBound (0 : ℝ →L[ℝ] ℝ) 1 := by
  intro h
  have hx := h 1
  norm_num at hx

/-- 恒等写像には正の下界がある。 -/
example : LowerBound (ContinuousLinearMap.id ℝ ℝ) 1 := by
  intro u
  simp

/-- 真の係数が厳密に応答を再現すると、実装した最小化条件を満たす。 -/
example (B : E →L[ℝ] F) (θ : E) : IsLeastSquares B (B θ) θ := by
  intro v
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  exact sq_nonneg _

/-- 全入力仮定を満たす具体例。c=0とc≠0の両方を含む。 -/
example (c : ℝ) : ∃ G : Set Unit, MeasurableSet G ∧
    (1 / 2 : ℝ) ≤ (MeasureTheory.Measure.dirac ()).real G ∧
    ∀ ω ∈ G, ‖c‖ ^ 2 ≤ 16 * c ^ 2 := by
  let μ : MeasureTheory.Measure Unit := MeasureTheory.Measure.dirac ()
  let A := ContinuousLinearMap.id ℝ ℝ
  have h := Showcase.oracle_recovery (E := ℝ) (F := ℝ)
    Unit inferInstance μ inferInstance (fun _ => A) A (fun _ => c) 0 (fun _ => c)
    1 (1 / 4) (1 / 4) 0 (c ^ 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (sq_nonneg c)
    (by intro u; simp [A])
    (by fun_prop) (by fun_prop)
    (by simp)
    (by simp)
    (by simp)
    (by simp [Real.norm_eq_abs, sq_abs])
    (by norm_num)
    (by intro ω v; simpa [A, Real.norm_eq_abs, sq_abs] using sq_nonneg (v - c))
  norm_num [μ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] at h ⊢
  exact h

/-- 最小化条件は半二乗損失と非標準化L1ペナルティそのもの。 -/
example {M : ℕ} (B : Coeff M →L[ℝ] F) (y : F) (lam : ℝ) (θhat : Coeff M) :
    IsLasso B y lam θhat ↔ ∀ θ,
      (1 / 2 : ℝ) * ‖B θhat - y‖ ^ 2 + lam * l1Norm θhat ≤
      (1 / 2 : ℝ) * ‖B θ - y‖ ^ 2 + lam * l1Norm θ := Iff.rfl

/-- 1次元の非零ペナルティ例。応答2に対して係数1が実際の最小化解。 -/
example : IsLasso (ContinuousLinearMap.id ℝ (Coeff 1))
    (EuclideanSpace.single 0 2) 1 (EuclideanSpace.single 0 1) := by
  intro θ
  simp [lassoObjective, l1Norm, partialL1, EuclideanSpace.real_norm_sq_eq]
  nlinarith [le_abs_self (θ 0), sq_nonneg (θ 0 - 1)]

/-- 正のペナルティ条件を外すと、零デザインではcone結論が崩れる。 -/
example : IsLasso (0 : Coeff 1 →L[ℝ] ℝ) 0 0 (EuclideanSpace.single 0 1) ∧
    ¬ SparseCone (∅ : Finset (Fin 1)) (EuclideanSpace.single 0 1) := by
  constructor
  · intro θ
    simp [lassoObjective]
  · simp [SparseCone, partialL1]

/-- 横長・階数落ち行列でも擬似逆が存在し、最小化解を与える。 -/
example (A : Matrix (Fin 1) (Fin 2) ℝ) (y : EuclideanSpace ℝ (Fin 1)) :
    IsLeastSquares (matrixMap A) y (moorePenrose (matrixMap A) y) :=
  moorePenrose_minimizes _ _

/-- Euclideanノルムと、誤って使いやすい成分最大値ノルムを区別する例。 -/
example : ‖(WithLp.toLp 2 ![3, 4] : Coeff 2)‖ ^ 2 = 25 := by
  norm_num [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]

/-- Frobeniusノルムは行列成分の二乗和の平方根。 -/
example : frobenius (!![3, 4] : Matrix (Fin 1) (Fin 2) ℝ) = 5 := by
  norm_num [frobenius, Fin.sum_univ_succ]

/-- 有向ペアの個数とN=1の退化を具体値で照合。 -/
example : Fintype.card (OrderedPair 3) = 6 ∧
    Fintype.card (OrderedPair 1) = 0 ∧ pairCorrection 1 = 0 := by
  norm_num [orderedPair_card, pairCorrection]

/-- 二点一様分布の平均。 -/
example : (∫ i : Fin 2, (2 * (i.val : ℝ) + 2) ∂uniformPopulation (Fin 2)) = 3 := by
  rw [integral_uniformPopulation]
  norm_num [populationMean, Fin.sum_univ_two]

/-- 非零の分散を持つ抽出例。 -/
example : ProbabilityTheory.variance (fun i : Fin 2 => (i.val : ℝ))
    (uniformPopulation (Fin 2)) = 1 / 4 := by
  rw [ProbabilityTheory.variance_eq_sub (finite_memLp_two _ _)]
  norm_num [Pi.pow_apply, integral_uniformPopulation, populationMean, Fin.sum_univ_two]

example {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    populationMean (fun _ : A => c) = c := by
  simp [populationMean, Fintype.card_ne_zero]

/-- 定数特徴では、抽出列が何であっても行列の標本誤差は0。 -/
example {Y : Type*} {L M T P : ℕ} (c : ℝ) (w : Fin T → ℝ)
    (z : Y × ((Fin T × Fin P) → OrderedPair 2)) :
    pairDesignError (fun _ _ _ _ _ => c) w z = (0 : Matrix (Fin L) (Fin M) ℝ) := by
  ext a m
  simp [pairDesignError, pairRowError, samplingError, populationMean]

/-- 完全に相関した加法ノイズでも二乗平均評価は使える。交差項は0ではない。 -/
example : (∫ i : Fin 2, ‖(i.val : ℝ) + i.val‖ ^ 2 ∂uniformPopulation (Fin 2)) = 2 := by
  rw [integral_uniformPopulation]
  norm_num [populationMean, Fin.sum_univ_two]

/-- 応答の符号、粒子数正規化、拡散係数σ²/2を具体値で照合。 -/
example (Y : Unit → Fin 2 → Fin 1 → ℝ) :
    observedWeakResponse (L := 1) Y (fun _ _ => 2) (fun _ _ => 3)
      (fun _ _ => 5) (fun _ _ => 7) (fun _ => 1) 2 () 0 = -44 := by
  norm_num [observedWeakResponse, Fin.sum_univ_two, Fin.sum_univ_one]

/-- 同一原子の反対係数は厳密に相殺され、合成特徴は0になる。 -/
example (Y : Unit → Fin 2 → Fin 1 → ℝ) (p : OrderedPair 2) :
    (∑ m : Fin 2, ![1, -1] m * observedPairFeature (L := 1) Y (fun _ _ => 1)
      (fun _ _ => 1) (fun _ z => z) () 0 m 0 p) = 0 := by
  rw [observedPairFeature_realizable Y (fun _ _ => 1) (fun _ _ => 1)
    (fun _ z => z) ![1, -1] (fun _ => 0) (by intro z; simp [Fin.sum_univ_two])]
  simp

/-- 誤差の振幅が観測に依存する例。無条件独立性なしで二乗平均は5となる。 -/
example :
    let μ := uniformPopulation (Fin 2)
    let g := fun (y : Fin 2) (_ : Fin 1) => 1 + (y.val : ℝ)
    let f := fun (z : Fin 2 × Fin 2) (_ : Fin 1) =>
      (1 + (z.1.val : ℝ)) * (2 * (z.2.val : ℝ) - 1)
    (∫ z, ‖(WithLp.toLp 2 (fun a => g z.1 a - f z a) : EuclideanSpace ℝ (Fin 1))‖ ^ 2
      ∂μ.prod μ) = 5 := by
  let μ := uniformPopulation (Fin 2)
  let g := fun (y : Fin 2) (_ : Fin 1) => 1 + (y.val : ℝ)
  let f := fun (z : Fin 2 × Fin 2) (_ : Fin 1) =>
    (1 + (z.1.val : ℝ)) * (2 * (z.2.val : ℝ) - 1)
  have hc (a : Fin 1) : (μ.prod μ)[(fun z => f z a) |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ.prod μ] 0 := by
    apply product_conditional_centered μ μ _ Integrable.of_finite
    intro y
    rw [integral_uniformPopulation]
    simp [populationMean, f, Fin.sum_univ_two]
    ring
  have hp := finite_observation_pythagoras μ μ g f
    (fun _ => measurable_of_finite _) (fun _ => finite_memLp_two μ _)
    (fun _ => finite_memLp_two (μ.prod μ) _) hc
  have hgi : (∫ y, ‖(WithLp.toLp 2 (g y) : EuclideanSpace ℝ (Fin 1))‖ ^ 2 ∂μ) = 5 / 2 := by
    rw [integral_uniformPopulation]
    norm_num [populationMean, g, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, Fin.sum_univ_one]
  have hfi : (∫ z, ‖(WithLp.toLp 2 (f z) : EuclideanSpace ℝ (Fin 1))‖ ^ 2 ∂μ.prod μ) = 5 / 2 := by
    rw [integral_prod _ Integrable.of_finite]
    simp only [μ]
    simp_rw [integral_uniformPopulation]
    norm_num [populationMean, f, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, Fin.sum_univ_one]
  change (∫ z, ‖(WithLp.toLp 2 (fun a => g z.1 a - f z a) : EuclideanSpace ℝ (Fin 1))‖ ^ 2 ∂μ.prod μ) = 5
  rw [hp, hgi, hfi]
  norm_num

/-- 重みの和の二乗ではなく、符号を含む各重みの二乗和を使う。 -/
example : designSamplingBudget 3 2 ![-1, 2] 7 4 = 37 ∧
    residualSamplingBudget 2 ![-1, 2] 11 6 = 26 := by
  norm_num [designSamplingBudget, residualSamplingBudget, Fin.sum_univ_two]

/-- 全列には正の下界がなくても、既知supportの一列には下界がある。 -/
example :
    LowerBound (matrixMap ((!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ).submatrix id (fun _ : Fin 1 => 0))) 1 ∧
    ¬ LowerBound (matrixMap (!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ)) 1 := by
  constructor
  · intro u
    have heq : matrixMap ((!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ).submatrix id
        (fun _ : Fin 1 => 0)) u = u := by
      ext a
      fin_cases a
      simp [matrixMap_apply]
    simp [heq]
  · intro h
    have hh := h (WithLp.toLp 2 ![0, 1])
    norm_num [EuclideanSpace.norm_eq, matrixMap_apply, Fin.sum_univ_two, Fin.sum_univ_one] at hh

/-- 決定論的な非零バイアスと平均0誤差のFrobenius二乗平均。 -/
example : (∫ i : Fin 2, frobenius (!![3, 2 * (i.val : ℝ) - 1] : Matrix (Fin 1) (Fin 2) ℝ) ^ 2
      ∂uniformPopulation (Fin 2)) = 10 ∧
    frobenius (!![3, 0] : Matrix (Fin 1) (Fin 2) ℝ) ^ 2 +
      (∫ i : Fin 2, frobenius (!![0, 2 * (i.val : ℝ) - 1] : Matrix (Fin 1) (Fin 2) ℝ) ^ 2
        ∂uniformPopulation (Fin 2)) = 10 := by
  constructor <;> simp_rw [integral_uniformPopulation, frobenius_sq_sum] <;>
    norm_num [populationMean, Fin.sum_univ_two, Fin.sum_univ_one]

section ConcretePairRecovery
local instance : Fact (2 ≤ 2) := ⟨le_rfl⟩

/-- 実際の一様ペア抽出・横長辞書・既知一列supportで、回復定理の全入力を満たす例。 -/
example :
    let μ : Measure Unit := Measure.dirac ()
    let h := fun (_ : Unit) (_ : Fin 1) (m : Fin 2) (_ : Fin 1) (_ : OrderedPair 2) =>
      if m = 0 then (2 : ℝ) else 0
    let w := fun _ : Fin 1 => (1 : ℝ)
    ∃ G : Set (Unit × ((Fin 1 × Fin 128) → OrderedPair 2)), MeasurableSet G ∧
      (1 / 2 : ℝ) ≤ (μ.prod (independentDraws (Fin 1 × Fin 128) (OrderedPair 2))).real G ∧
      ∀ z ∈ G, ‖moorePenrose (matrixMap ((sampledPairDesign h w z).submatrix id (fun _ : Fin 1 => 0)))
        (WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ))) - WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ))‖ ^ 2 ≤ 1 / 2 := by
  let μ : Measure Unit := Measure.dirac ()
  let h := fun (_ : Unit) (_ : Fin 1) (m : Fin 2) (_ : Fin 1) (_ : OrderedPair 2) =>
    if m = 0 then (2 : ℝ) else 0
  let w := fun _ : Fin 1 => (1 : ℝ)
  let b := fun (_ : Unit) (_ : Fin 1) => (1 : ℝ)
  let θ := fun _ : Fin 1 => (1 : ℝ)
  let A : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]
  let e := fun _ : Fin 1 => (0 : Fin 2)
  have hfull (y : Unit) : fullPairDesign h w y = A := by
    ext a m
    fin_cases a
    fin_cases m <;> norm_num [fullPairDesign, h, w, A, Fin.sum_univ_one, orderedPair_card]
  have hr (y : Unit) : fullRegressionResidual (selectPairFeatures h e) w b θ y = 0 := by
    ext a
    change (1 - ∑ j : Fin 1, fullPairDesign h w y a (e j) * 1) = 0
    rw [hfull]
    fin_cases a
    simp [A, e]
  have hA : LowerBound (matrixMap (A.submatrix id e)) 1 := by
    intro u
    have heq : matrixMap (A.submatrix id e) u = u := by
      ext a
      fin_cases a
      simp [matrixMap_apply, A, e]
    simp [heq]
  have hout := sampled_oracle_recovery (P := 128) (by norm_num) (by norm_num) μ h w b θ A e
    (by intro i j _; exact Subsingleton.elim i j)
    (by intros; exact measurable_of_finite _) (by intros; exact finite_memLp_two μ _)
    (by intros; exact measurable_of_finite _) (by intros; exact finite_memLp_two μ _)
    0 0 4 4 1 (1 / 4) (1 / 4) (by norm_num) (by norm_num)
    (by simp [hfull, frobenius]) (by simp [hr])
    (by intro a m t p; fin_cases m <;> norm_num [h, μ])
    (by intro a t p; norm_num [h, e, θ, μ, Fin.sum_univ_one])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA
    (by norm_num [designSamplingBudget, w, Fin.sum_univ_one])
  norm_num [residualSamplingBudget, w, b, θ, Fin.sum_univ_one] at hout
  simpa only [Prod.forall] using hout

end ConcretePairRecovery
end WMFKI.HumanCheck

#print axioms WMFKI.lowerBound_perturb
#print axioms WMFKI.leastSquares_orthogonal
#print axioms WMFKI.leastSquares_prediction_sq_bound
#print axioms WMFKI.leastSquares_error_bound
#print axioms WMFKI.secondMoment_good_event
#print axioms WMFKI.good_event_intersection
#print axioms WMFKI.oracle_recovery_of_moments
#print axioms WMFKI.Showcase.oracle_recovery
#print axioms WMFKI.matrixMap_apply
#print axioms WMFKI.matrixMap_norm_le_frobenius
#print axioms WMFKI.frobenius_restrict_columns
#print axioms WMFKI.matrixMap_restrict_norm_le
#print axioms WMFKI.matrixMap_sub
#print axioms WMFKI.matrixMap_transpose
#print axioms WMFKI.frobenius_eq_vector_norm
#print axioms WMFKI.matrixMap_secondMoment_transfer
#print axioms WMFKI.isLeastSquares_of_orthogonal
#print axioms WMFKI.moorePenrose_isLeastSquares
#print axioms WMFKI.moorePenrose_error_bound
#print axioms WMFKI.exists_moorePenrose
#print axioms WMFKI.moorePenrose_spec
#print axioms WMFKI.moorePenrose_minimizes
#print axioms WMFKI.partialL1_nonneg
#print axioms WMFKI.partialL1_decomp
#print axioms WMFKI.partialL1_sq_le
#print axioms WMFKI.l1_support_difference
#print axioms WMFKI.score_inner_bound
#print axioms WMFKI.lasso_basic_inequality
#print axioms WMFKI.lasso_deterministic
#print axioms WMFKI.coneLowerBound_perturb
#print axioms WMFKI.columnBound_perturb
#print axioms WMFKI.score_of_column_and_residual
#print axioms WMFKI.lasso_recovery_of_moments
#print axioms WMFKI.lasso_penalty_normalization
#print axioms WMFKI.norm_le_l1Norm
#print axioms WMFKI.lassoObjective_continuous
#print axioms WMFKI.exists_lasso
#print axioms WMFKI.lassoEstimator_minimizes
#print axioms WMFKI.oracle_moorePenrose_recovery
#print axioms WMFKI.lasso_estimator_recovery
#print axioms WMFKI.l2_norm_sq_eq_integral
#print axioms WMFKI.conditional_centered_inner_zero
#print axioms WMFKI.conditional_centered_second_moment
#print axioms WMFKI.weighted_independent_variance
#print axioms WMFKI.refreshed_sampling_variance
#print axioms WMFKI.integral_uniformPopulation
#print axioms WMFKI.finite_memLp_two
#print axioms WMFKI.integral_draw_eval
#print axioms WMFKI.draws_independent
#print axioms WMFKI.centered_draw_mean
#print axioms WMFKI.centered_draw_variance
#print axioms WMFKI.samplingError_mean
#print axioms WMFKI.samplingError_second_moment
#print axioms WMFKI.samplingError_second_moment_weighted
#print axioms WMFKI.populationMean_linear_combination
#print axioms WMFKI.samplingError_linear_combination
#print axioms WMFKI.samplingError_eq_sampled_sub_full
#print axioms WMFKI.orderedPair_card
#print axioms WMFKI.pairCorrection_bounds
#print axioms WMFKI.corrected_pair_average
#print axioms WMFKI.pairPrefactor_sq_le
#print axioms WMFKI.pairRowError_mean
#print axioms WMFKI.pairRowError_second_moment
#print axioms WMFKI.single_particle_no_pairs
#print axioms WMFKI.product_conditional_centered
#print axioms WMFKI.pairRowError_conditional_mean
#print axioms WMFKI.integrable_finite_fibers
#print axioms WMFKI.samplingError_observable
#print axioms WMFKI.samplingError_observation_memLp
#print axioms WMFKI.samplingError_joint_memLp
#print axioms WMFKI.samplingError_joint_second_moment
#print axioms WMFKI.pairRowError_joint_memLp
#print axioms WMFKI.pairRowError_conditional_mean_of_moments
#print axioms WMFKI.pairRowError_joint_second_moment
#print axioms WMFKI.pairDesignError_second_moment
#print axioms WMFKI.pairDesignError_mul_coefficients
#print axioms WMFKI.pairDesignError_direction_second_moment
#print axioms WMFKI.pairDesignError_eq_difference
#print axioms WMFKI.assembled_design_conditional_centered
#print axioms WMFKI.assembled_design_second_moment
#print axioms WMFKI.assembled_design_direction_second_moment
#print axioms WMFKI.pairFeature_sq_bound
#print axioms WMFKI.pairFeature_second_moment
#print axioms WMFKI.norm_add_sq_le_twice
#print axioms WMFKI.observation_second_moment
#print axioms WMFKI.observedPairFeature_measurable
#print axioms WMFKI.observedPairFeature_moments
#print axioms WMFKI.observed_design_second_moment
#print axioms WMFKI.noisy_observed_design_second_moment
#print axioms WMFKI.observedPairFeature_realizable
#print axioms WMFKI.observed_direction_second_moment
#print axioms WMFKI.conditional_centered_second_moment_fun
#print axioms WMFKI.finite_observation_pythagoras
#print axioms WMFKI.sampledResidual_decomposition
#print axioms WMFKI.fullPairDesign_entry_measurable
#print axioms WMFKI.fullPairDesign_entry_memLp
#print axioms WMFKI.fullResidual_entry_regular
#print axioms WMFKI.sampledResidual_second_moment_identity
#print axioms WMFKI.sampledResidual_second_moment_bound
#print axioms WMFKI.observed_residual_second_moment_bound
#print axioms WMFKI.observedWeakResponse_regular
#print axioms WMFKI.weak_pair_moment_bounds
#print axioms WMFKI.continuous_matrixMap
#print axioms WMFKI.frobenius_sq_sum
#print axioms WMFKI.finite_vector_norm_sq_regular
#print axioms WMFKI.frobenius_sq_regular
#print axioms WMFKI.matrix_operator_moment_regular
#print axioms WMFKI.sampledPairDesign_entry_regular
#print axioms WMFKI.sampledResidual_eq_regression
#print axioms WMFKI.sampledResidual_norm_sq_regular
#print axioms WMFKI.matrix_observation_pythagoras
#print axioms WMFKI.sampledDesign_second_moment_identity
#print axioms WMFKI.sampledDesign_operator_moments
#print axioms WMFKI.sampled_moorePenrose_recovery
#print axioms WMFKI.sampled_lasso_recovery
#print axioms WMFKI.frobenius_select_sq_le
#print axioms WMFKI.full_design_selected_second_moment_le
#print axioms WMFKI.sampled_oracle_recovery
#print axioms WMFKI.WeakAssemblyData.radius_nonneg
#print axioms WMFKI.WeakAssemblyData.atomBound_nonneg
#print axioms WMFKI.WeakAssemblyData.kernelBound_nonneg
#print axioms WMFKI.WeakAssemblyData.position_moments
#print axioms WMFKI.WeakAssemblyData.regular
#print axioms WMFKI.WeakAssemblyData.selected_direction_bound
#print axioms WMFKI.WeakAssemblyData.oracle_recovery
#print axioms WMFKI.WeakAssemblyData.lasso_recovery
