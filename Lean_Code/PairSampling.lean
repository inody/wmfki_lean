import Lean_Code.FiniteSampling
import Lean_Code.MatrixBridge
import Mathlib.Data.Finset.Prod

namespace WMFKI

open MeasureTheory
open scoped BigOperators

abbrev OrderedPair (N : ℕ) := ↥((Finset.univ : Finset (Fin N)).offDiag)

instance {N : ℕ} : MeasurableSpace (OrderedPair N) := ⊤
instance {N : ℕ} : MeasurableSingletonClass (OrderedPair N) := ⟨fun _ => trivial⟩

theorem orderedPair_card (N : ℕ) : Fintype.card (OrderedPair N) = N * (N - 1) := by
  change Fintype.card ↥((Finset.univ : Finset (Fin N)).offDiag) = _
  rw [Fintype.card_coe, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  simp [Nat.mul_sub_left_distrib]

instance {N : ℕ} [Fact (2 ≤ N)] : Nonempty (OrderedPair N) := by
  apply Fintype.card_pos_iff.mp
  rw [orderedPair_card]
  have h := Fact.out (p := 2 ≤ N)
  exact Nat.mul_pos (by omega) (by omega)

noncomputable def pairCorrection (N : ℕ) : ℝ := ((N : ℝ) - 1) / N
noncomputable def pairPrefactor (L N : ℕ) : ℝ := (1 / Real.sqrt L) * pairCorrection N

theorem pairCorrection_bounds {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ pairCorrection N ∧ pairCorrection N ≤ 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold pairCorrection
  constructor
  · positivity
  · apply (div_le_one hn).mpr
    linarith

/-- N(N−1)での平均に(N−1)/Nを掛けると、全ペアのN²正規化と一致。 -/
theorem corrected_pair_average {N : ℕ} (hN : 2 ≤ N) (h : OrderedPair N → ℝ) :
    pairCorrection N * populationMean h = (∑ a, h a) / (N : ℝ) ^ 2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hn1 : (N : ℝ) - 1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  simp only [pairCorrection, populationMean, orderedPair_card, Nat.cast_mul,
    Nat.cast_sub (show 1 ≤ N by omega), Nat.cast_one]
  field_simp

theorem pairPrefactor_sq_le {L N : ℕ} (hL : 0 < L) (hN : 1 ≤ N) :
    pairPrefactor L N ^ 2 ≤ 1 / (L : ℝ) := by
  obtain ⟨hc0, hc1⟩ := pairCorrection_bounds hN
  have hc2 : pairCorrection N ^ 2 ≤ 1 := by nlinarith
  unfold pairPrefactor
  rw [mul_pow, div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg L)]
  simpa using mul_le_mul_of_nonneg_left hc2 (by positivity : 0 ≤ 1 / (L : ℝ))

noncomputable def pairRowError {T P N : ℕ} (L : ℕ)
    (h : Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ)
    (ω : (Fin T × Fin P) → OrderedPair N) : ℝ :=
  pairPrefactor L N * samplingError h w ω

theorem pairRowError_mean {T P N : ℕ} [Fact (2 ≤ N)] (L : ℕ)
    (h : Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ) :
    (∫ ω, pairRowError (P := P) L h w ω ∂independentDraws (Fin T × Fin P) (OrderedPair N)) = 0 := by
  unfold pairRowError
  rw [integral_const_mul, samplingError_mean, mul_zero]

theorem pairRowError_second_moment {T P N L : ℕ} [Fact (2 ≤ N)]
    (hP : 0 < P) (hL : 0 < L) (h : Fin T → OrderedPair N → ℝ)
    (w : Fin T → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t, populationMean (fun a => h t a ^ 2) ≤ C) :
    (∫ ω, pairRowError L h w ω ^ 2 ∂independentDraws (Fin T × Fin P) (OrderedPair N)) ≤
      C * (∑ t, w t ^ 2) / ((L : ℝ) * P) := by
  simp only [pairRowError, mul_pow]
  rw [integral_const_mul]
  have hn : 1 ≤ N := by have := Fact.out (p := 2 ≤ N); omega
  calc
    _ ≤ pairPrefactor L N ^ 2 * (C * (∑ t, w t ^ 2) / P) :=
      mul_le_mul_of_nonneg_left (samplingError_second_moment hP h w C hC) (sq_nonneg _)
    _ ≤ (1 / (L : ℝ)) * (C * (∑ t, w t ^ 2) / P) :=
      mul_le_mul_of_nonneg_right (pairPrefactor_sq_le hL hn) (by positivity)
    _ = _ := by ring

/-- N=1には非自己ペアがなく、補正係数も0。空集合上の一様確率は作らない。 -/
theorem single_particle_no_pairs : Fintype.card (OrderedPair 1) = 0 ∧ pairCorrection 1 = 0 := by
  norm_num [orderedPair_card, pairCorrection]

end WMFKI
