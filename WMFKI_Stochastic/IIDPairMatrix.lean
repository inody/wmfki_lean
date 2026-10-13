import WMFKI_Stochastic.IIDPairStatistic
import Lean_Code.MatrixBridge
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

open MeasureTheory ProbabilityTheory

namespace WMFKIIIDPairs

/-- 行数Lの平方根で正規化する。列数Mでは正規化しない。 -/
noncomputable def iidPairMatrix {Ω E : Type*} {N : ℕ} (L M : ℕ)
    (X : Fin N → Ω → E) (G : Fin L → Fin M → E × E → ℝ)
    (ω : Ω) : Matrix (Fin L) (Fin M) ℝ :=
  fun a m => (Real.sqrt (L : ℝ))⁻¹ * iidPairStatistic X (G a m) ω

noncomputable def populationPairMatrix {E : Type*} [MeasurableSpace E]
    (ρ : Measure E) (L M : ℕ) (G : Fin L → Fin M → E × E → ℝ) : Matrix (Fin L) (Fin M) ℝ :=
  fun a m => (Real.sqrt (L : ℝ))⁻¹ * ∫ z, G a m z ∂(ρ.prod ρ)

/-- iidペア設計と母集団設計のFrobenius誤差。行/列間の独立性は不要。
    時間積分を核に含める場合、その可測性とL²性は別途実際に証明する必要がある。 -/
theorem iid_pair_matrix_frobenius_rate
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (ρ : Measure E) [IsProbabilityMeasure ρ]
    (N L M : ℕ) (hN : 0 < N) (hL : 0 < L)
    (X : Fin N → Ω → E) (hX : iIndepFun X P) (hm : ∀ i, Measurable (X i))
    (hLaw : ∀ i, HasLaw (X i) ρ P) (G : Fin L → Fin M → E × E → ℝ)
    (hG : ∀ a m, Measurable (G a m)) (hGL : ∀ a m, MemLp (G a m) 2 (ρ.prod ρ))
    (C : ℝ) (hC : 0 ≤ C) (hGC : ∀ a m, (∫ z, G a m z ^ 2 ∂(ρ.prod ρ)) ≤ C) :
    let A := fun ω => iidPairMatrix L M X G ω - populationPairMatrix ρ L M G
    MemLp (fun ω => (WithLp.toLp 2 (fun am : Fin L × Fin M => A ω am.1 am.2) :
      EuclideanSpace ℝ (Fin L × Fin M))) 2 P ∧
    (∫ ω, WMFKI.frobenius (A ω) ^ 2 ∂P) ≤ 5 * (M : ℝ) * C / (N : ℝ) := by
  dsimp only
  let r := fun (am : Fin L × Fin M) ω =>
    iidPairStatistic X (G am.1 am.2) ω - ∫ z, G am.1 am.2 z ∂(ρ.prod ρ)
  have hr (am : Fin L × Fin M) :=
    iid_pair_statistic_rate hN hX hm hLaw (hG am.1 am.2) (hGL am.1 am.2) hC (hGC am.1 am.2)
  have he ω a m : (iidPairMatrix L M X G ω - populationPairMatrix ρ L M G) a m =
      (Real.sqrt (L : ℝ))⁻¹ * r (a,m) ω := by
    simp [iidPairMatrix, populationPairMatrix, r, mul_sub]
  have hLp : MemLp (fun ω => (WithLp.toLp 2 (fun am : Fin L × Fin M =>
      (iidPairMatrix L M X G ω - populationPairMatrix ρ L M G) am.1 am.2) :
      EuclideanSpace ℝ (Fin L × Fin M))) 2 P := by
    apply MemLp.of_eval_piLp
    intro am
    change MemLp (fun ω => (iidPairMatrix L M X G ω - populationPairMatrix ρ L M G) am.1 am.2) 2 P
    simp_rw [he]
    exact (hr am).1.const_mul _
  have hn ω : WMFKI.frobenius (iidPairMatrix L M X G ω - populationPairMatrix ρ L M G) ^ 2 =
      (L : ℝ)⁻¹ * ∑ am, r am ω ^ 2 := by
    rw [WMFKI.frobenius_eq_vector_norm, EuclideanSpace.real_norm_sq_eq]
    change (∑ am : Fin L × Fin M, ((iidPairMatrix L M X G ω - populationPairMatrix ρ L M G) am.1 am.2)^2) = _
    simp_rw [he, mul_pow]
    rw [← Finset.mul_sum, inv_pow, Real.sq_sqrt (Nat.cast_nonneg L)]
  refine ⟨hLp, ?_⟩
  simp_rw [hn]
  rw [integral_const_mul, integral_finsetSum _ (fun am _ => (hr am).1.integrable_sq)]
  calc
    _ ≤ (L : ℝ)⁻¹ * ∑ _am : Fin L × Fin M, 5 * C / (N : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun am _ => (hr am).2))
        (inv_nonneg.mpr (Nat.cast_nonneg L))
    _ = _ := by
      have hl : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hL)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul]
      field_simp

end WMFKIIIDPairs
