import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Integration

open MeasureTheory ProbabilityTheory

namespace WMFKIIndependentFourth
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- 第4モーメントから低次の実際の可積分性を導く。 -/
theorem l4_integrable_power {X : Ω → ℝ} (hX : MemLp X 4 P) (k : ℕ) (hk : k ≤ 4) :
    Integrable (fun ω => X ω ^ k) P := by
  have hi := integrable_norm_pow_of_le hX.aestronglyMeasurable hk
    (hX.integrable_norm_pow (p := 4) (by decide))
  apply hi.mono' (hX.aestronglyMeasurable.pow k)
  exact ae_of_all _ (fun ω => by simp only [Pi.pow_apply, norm_pow, le_refl])

/-- 二次モーメントの二乗を第4モーメントで抑える。L²性を先に確保する。 -/
theorem second_moment_sq_le_fourth {X : Ω → ℝ} (hX : MemLp X 4 P) :
    (∫ ω, X ω ^ 2 ∂P)^2 ≤ ∫ ω, X ω ^ 4 ∂P := by
  have hs : MemLp (fun ω => X ω^2) 2 P := by
    apply (memLp_two_iff_integrable_sq (hX.aestronglyMeasurable.pow 2)).mpr
    simpa only [Pi.pow_apply, ← pow_mul] using l4_integrable_power hX 4 le_rfl
  have hv := variance_nonneg (fun ω => X ω^2) P
  rw [variance_eq_sub hs] at hv
  change 0 ≤ (∫ ω, (X ω^2)^2 ∂P) - (∫ ω, X ω^2 ∂P)^2 at hv
  simpa only [← pow_mul] using (sub_nonneg.mp hv)

/-- 独立な中心化変数の和について正確な4次モーメント展開。
    積の可積分性は各変数のL4と独立性から証明する。 -/
theorem independent_centered_fourth_add {X Y : Ω → ℝ}
    (hX : MemLp X 4 P) (hY : MemLp Y 4 P) (hI : IndepFun X Y P)
    (hX0 : (∫ ω, X ω ∂P) = 0) (hY0 : (∫ ω, Y ω ∂P) = 0) :
    (∫ ω, (X ω + Y ω)^4 ∂P) = (∫ ω, X ω^4 ∂P) +
      6*(∫ ω, X ω^2 ∂P)*(∫ ω, Y ω^2 ∂P) + (∫ ω, Y ω^4 ∂P) := by
  have hind (k l : ℕ) : IndepFun (fun ω => X ω^k) (fun ω => Y ω^l) P :=
    hI.comp (measurable_id.pow_const k) (measurable_id.pow_const l)
  have hint (k l : ℕ) (hk : k ≤ 4) (hl : l ≤ 4) :
      Integrable (fun ω => X ω^k * Y ω^l) P :=
    (hind k l).integrable_mul (l4_integrable_power hX k hk) (l4_integrable_power hY l hl)
  have hfactor (k l : ℕ) : (∫ ω, X ω^k * Y ω^l ∂P) =
      (∫ ω, X ω^k ∂P)*(∫ ω, Y ω^l ∂P) :=
    (hind k l).integral_fun_mul_eq_mul_integral (hX.aestronglyMeasurable.pow k)
      (hY.aestronglyMeasurable.pow l)
  have he : (fun ω => (X ω + Y ω)^4) = fun ω =>
      ((X ω^4 + 4*(X ω^3*Y ω^1)) + 6*(X ω^2*Y ω^2)) +
      (4*(X ω^1*Y ω^3) + Y ω^4) := by funext ω; ring
  rw [he]
  have hi4 := l4_integrable_power hX 4 le_rfl
  have hj4 := l4_integrable_power hY 4 le_rfl
  have hi31 := (hint 3 1 (by omega) (by omega)).const_mul 4
  have hi22 := (hint 2 2 (by omega) (by omega)).const_mul 6
  have hi13 := (hint 1 3 (by omega) (by omega)).const_mul 4
  rw [integral_add (f := fun ω => X ω^4 + 4*(X ω^3*Y ω^1) + 6*(X ω^2*Y ω^2))
    (g := fun ω => 4*(X ω^1*Y ω^3) + Y ω^4) ((hi4.add hi31).add hi22) (hi13.add hj4),
    integral_add (f := fun ω => X ω^4 + 4*(X ω^3*Y ω^1)) (hi4.add hi31) hi22,
    integral_add hi4 hi31, integral_add hi13 hj4]
  simp_rw [integral_const_mul, hfactor]
  simp [hX0, hY0]
  ring

/-- 同じ仮定での2次モーメント展開。 -/
theorem independent_centered_second_add {X Y : Ω → ℝ}
    (hX : MemLp X 4 P) (hY : MemLp Y 4 P) (hI : IndepFun X Y P)
    (hX0 : (∫ ω, X ω ∂P) = 0) (hY0 : (∫ ω, Y ω ∂P) = 0) :
    (∫ ω, (X ω + Y ω)^2 ∂P) = (∫ ω, X ω^2 ∂P) + (∫ ω, Y ω^2 ∂P) := by
  have hx2 : MemLp X 2 P := hX.mono_exponent (by norm_num)
  have hy2 : MemLp Y 2 P := hY.mono_exponent (by norm_num)
  have hm : (∫ ω, X ω + Y ω ∂P) = 0 := by
    rw [integral_add (hx2.integrable (by norm_num)) (hy2.integrable (by norm_num)), hX0, hY0]
    simp
  have h := hI.variance_fun_add hx2 hy2
  rw [variance_of_integral_eq_zero (X := fun ω => X ω + Y ω) (hx2.add hy2).aemeasurable hm,
    variance_of_integral_eq_zero hx2.aemeasurable hX0,
    variance_of_integral_eq_zero hy2.aemeasurable hY0] at h
  exact h

end WMFKIIndependentFourth
