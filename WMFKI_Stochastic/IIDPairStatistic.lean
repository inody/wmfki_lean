import WMFKI_Stochastic.PairArrayVariance

open MeasureTheory ProbabilityTheory

namespace WMFKIIIDPairs

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- 対角を除く順序付きペア。核の対称性は要求しない。 -/
noncomputable def offDiagonalKernel {N : ℕ} (X : Fin N → Ω → E)
    (G : E × E → ℝ) (p : Fin N × Fin N) (ω : Ω) : ℝ :=
  if p.1 = p.2 then 0 else G (X p.1 ω, X p.2 ω)

omit [MeasurableSpace Ω] [MeasurableSpace E] in
theorem offDiagonalKernel_eq {N : ℕ} (X : Fin N → Ω → E)
    (G : E × E → ℝ) (p : Fin N × Fin N) :
    offDiagonalKernel X G p = if p.1 = p.2 then (fun _ => 0) else (fun ω => G (X p.1 ω, X p.2 ω)) := by
  funext ω
  unfold offDiagonalKernel
  split_ifs <;> rfl

noncomputable def iidPairStatistic {N : ℕ} (X : Fin N → Ω → E)
    (G : E × E → ℝ) : Ω → ℝ := pairArrayAverage N (offDiagonalKernel X G)

/-- 原始的な独立性と共通の法則から、異なる二粒子の積法則を導く。 -/
theorem iid_pair_hasLaw {N : ℕ} {X : Fin N → Ω → E} {ρ : Measure E}
    (hX : iIndepFun X P) (hLaw : ∀ i, HasLaw (X i) ρ P)
    {i j : Fin N} (hij : i ≠ j) :
    HasLaw (fun ω => (X i ω, X j ω)) (ρ.prod ρ) P :=
  (hX.indepFun hij).hasLaw_prod (hLaw i) (hLaw j)

/-- 母集団の核のL²性から各対角除外項のL²性を証明。 -/
theorem off_diagonal_memLp {N : ℕ} {X : Fin N → Ω → E} {ρ : Measure E}
    (hX : iIndepFun X P) (hLaw : ∀ i, HasLaw (X i) ρ P)
    {G : E × E → ℝ} (hG : MemLp G 2 (ρ.prod ρ)) (p : Fin N × Fin N) :
    MemLp (offDiagonalKernel X G p) 2 P := by
  by_cases hp : p.1 = p.2
  · simp [offDiagonalKernel_eq, hp]
  · simpa [offDiagonalKernel_eq, hp] using (iid_pair_hasLaw hX hLaw hp).memLp_fun_comp hG

theorem off_diagonal_mean {N : ℕ} {X : Fin N → Ω → E} {ρ : Measure E}
    (hX : iIndepFun X P) (hLaw : ∀ i, HasLaw (X i) ρ P)
    {G : E × E → ℝ} (hG : Measurable G) (p : Fin N × Fin N) :
    (∫ ω, offDiagonalKernel X G p ω ∂P) =
      if p.1 = p.2 then 0 else ∫ z, G z ∂(ρ.prod ρ) := by
  by_cases hp : p.1 = p.2
  · simp [offDiagonalKernel, hp]
  · simp only [offDiagonalKernel, ite_eq_right hp]
    exact (iid_pair_hasLaw hX hLaw hp).integral_comp hG.aestronglyMeasurable

theorem off_diagonal_second_moment {N : ℕ} {X : Fin N → Ω → E} {ρ : Measure E}
    (hX : iIndepFun X P) (hLaw : ∀ i, HasLaw (X i) ρ P)
    {G : E × E → ℝ} (hG : Measurable G) {C : ℝ} (hC : 0 ≤ C)
    (hGC : (∫ z, G z ^ 2 ∂(ρ.prod ρ)) ≤ C) (p : Fin N × Fin N) :
    (∫ ω, offDiagonalKernel X G p ω ^ 2 ∂P) ≤ C := by
  by_cases hp : p.1 = p.2
  · simpa [offDiagonalKernel, hp] using hC
  · simp only [offDiagonalKernel, ite_eq_right hp]
    have he := (iid_pair_hasLaw hX hLaw hp).integral_comp (hG.pow_const 2).aestronglyMeasurable
    exact he.trans_le hGC

/-- 原始的な粒子独立性から重ならないペア項の無相関を導く。 -/
theorem off_diagonal_disjoint_covariance {N : ℕ} {X : Fin N → Ω → E} {ρ : Measure E}
    (hX : iIndepFun X P) (hm : ∀ i, Measurable (X i))
    (hLaw : ∀ i, HasLaw (X i) ρ P) {G : E × E → ℝ}
    (hG : Measurable G) (hGL : MemLp G 2 (ρ.prod ρ))
    (p q : Fin N × Fin N) (h1 : p.1 ≠ q.1) (h2 : p.1 ≠ q.2)
    (h3 : p.2 ≠ q.1) (h4 : p.2 ≠ q.2) :
    cov[offDiagonalKernel X G p, offDiagonalKernel X G q; P] = 0 := by
  by_cases hp : p.1 = p.2
  · simp [offDiagonalKernel_eq, hp]
  by_cases hq : q.1 = q.2
  · simp [offDiagonalKernel_eq, hq]
  have hi := (hX.indepFun_prodMk_prodMk hm p.1 p.2 q.1 q.2 h1 h2 h3 h4).comp hG hG
  simp only [offDiagonalKernel_eq, ite_eq_right hp, ite_eq_right hq]
  exact hi.covariance_eq_zero ((iid_pair_hasLaw hX hLaw hp).memLp_fun_comp hGL)
    ((iid_pair_hasLaw hX hLaw hq).memLp_fun_comp hGL)

theorem iid_pair_statistic_mean {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → E} {ρ : Measure E} (hX : iIndepFun X P)
    (hLaw : ∀ i, HasLaw (X i) ρ P) {G : E × E → ℝ}
    (hG : Measurable G) (hGL : MemLp G 2 (ρ.prod ρ)) :
    (∫ ω, iidPairStatistic X G ω ∂P) =
      (1 - (N : ℝ)⁻¹) * ∫ z, G z ∂(ρ.prod ρ) := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  unfold iidPairStatistic pairArrayAverage
  rw [integral_const_mul, integral_finsetSum Finset.univ
    (fun p _ => (off_diagonal_memLp hX hLaw hGL p).integrable (by norm_num))]
  simp_rw [off_diagonal_mean hX hLaw hG]
  rw [sum_off_diagonal_constant]
  field_simp

/-- iid法則と核L²だけから、平均・分散・母集団に対する二乗誤差を導く。
    相互作用粒子の独立性を仮定する定理ではなく、独立な平均場コピー用。 -/
theorem iid_pair_statistic_budget {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → E} {ρ : Measure E}
    (hX : iIndepFun X P) (hm : ∀ i, Measurable (X i))
    (hLaw : ∀ i, HasLaw (X i) ρ P) {G : E × E → ℝ}
    (hG : Measurable G) (hGL : MemLp G 2 (ρ.prod ρ))
    {C : ℝ} (hC : 0 ≤ C) (hGC : (∫ z, G z ^ 2 ∂(ρ.prod ρ)) ≤ C) :
    MemLp (iidPairStatistic X G) 2 P ∧
    (∫ ω, iidPairStatistic X G ω ∂P) = (1 - (N : ℝ)⁻¹) * (∫ z, G z ∂(ρ.prod ρ)) ∧
    Var[iidPairStatistic X G; P] ≤ 4 * C / (N : ℝ) ∧
    (∫ ω, (iidPairStatistic X G ω - ∫ z, G z ∂(ρ.prod ρ)) ^ 2 ∂P) ≤
      4 * C / (N : ℝ) + (∫ z, G z ∂(ρ.prod ρ)) ^ 2 / (N : ℝ) ^ 2 := by
  have hL : MemLp (iidPairStatistic X G) 2 P :=
    pair_array_memLp (off_diagonal_memLp hX hLaw hGL)
  have hM := iid_pair_statistic_mean hN hX hLaw hG hGL
  have hV := pair_array_variance_bound hN hC (off_diagonal_memLp hX hLaw hGL)
    (off_diagonal_second_moment hX hLaw hG hC hGC)
    (off_diagonal_disjoint_covariance hX hm hLaw hG hGL)
  refine ⟨hL, hM, hV, ?_⟩
  rw [mean_square_error_eq_variance_bias hL, hM]
  have he (a : ℝ) : ((1 - (N : ℝ)⁻¹) * a - a) ^ 2 = a ^ 2 / (N : ℝ) ^ 2 := by
    simp only [div_eq_mul_inv]
    ring
  rw [he]
  exact add_le_add hV (le_refl _)

/-- 母集団の平均に対する実際の誤差はL²で、二乗期待値は5C/N以下。
    Cは粒子数に依存しない母集団核の二次モーメント上界。 -/
theorem iid_pair_statistic_rate {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → E} {ρ : Measure E} [IsProbabilityMeasure ρ]
    (hX : iIndepFun X P) (hm : ∀ i, Measurable (X i))
    (hLaw : ∀ i, HasLaw (X i) ρ P) {G : E × E → ℝ}
    (hG : Measurable G) (hGL : MemLp G 2 (ρ.prod ρ))
    {C : ℝ} (hC : 0 ≤ C) (hGC : (∫ z, G z ^ 2 ∂(ρ.prod ρ)) ≤ C) :
    MemLp (fun ω => iidPairStatistic X G ω - ∫ z, G z ∂(ρ.prod ρ)) 2 P ∧
    (∫ ω, (iidPairStatistic X G ω - ∫ z, G z ∂(ρ.prod ρ)) ^ 2 ∂P) ≤ 5 * C / (N : ℝ) := by
  obtain ⟨hL, _, _, hB⟩ := iid_pair_statistic_budget hN hX hm hLaw hG hGL hC hGC
  refine ⟨hL.sub (memLp_const _), hB.trans ?_⟩
  have hmean : (∫ z, G z ∂(ρ.prod ρ)) ^ 2 ≤ C := by
    have hv := variance_nonneg G (ρ.prod ρ)
    rw [variance_eq_sub hGL] at hv
    change 0 ≤ (∫ z, G z ^ 2 ∂(ρ.prod ρ)) - (∫ z, G z ∂(ρ.prod ρ)) ^ 2 at hv
    linarith
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hp : (0 : ℝ) < N := by positivity
  have hb : (∫ z, G z ∂(ρ.prod ρ)) ^ 2 / (N : ℝ) ^ 2 ≤ C / (N : ℝ) :=
    (div_le_div_of_nonneg_right hmean (sq_nonneg _)).trans
      (div_le_div_of_nonneg_left hC hp (by nlinarith))
  calc
    _ ≤ 4 * C / (N : ℝ) + C / (N : ℝ) := add_le_add (le_refl _) hb
    _ = _ := by ring

omit [MeasurableSpace Ω] [MeasurableSpace E] in
theorem iid_pair_statistic_one (X : Fin 1 → Ω → E) (G : E × E → ℝ) :
    iidPairStatistic X G = 0 := by
  funext ω
  simp [iidPairStatistic, pairArrayAverage, offDiagonalKernel, Fintype.sum_prod_type]

end WMFKIIIDPairs
