import WMFKI_Stochastic.SynchronousFourthRate
import WMFKI_Stochastic.ObservationFeaturePerturbation

open MeasureTheory ProbabilityTheory
open WMFKIIndependentFourth
open scoped NNReal ENNReal
namespace WMFKIFeatureCoupling

/-- 位置差と位置は依存してよい。L4を先に使い積のL2を確保してからCSを適用。 -/
theorem dependent_norm_product_l2 {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedAddCommGroup F] (P : Measure Ω)
    (e : Ω → E) (x : Ω → F) (he : MemLp e 4 P) (hx : MemLp x 4 P)
    (q R : ℝ) (heq : (∫ ω, ‖e ω‖^4 ∂P) ≤ q) (hxR : (∫ ω, ‖x ω‖^4 ∂P) ≤ R) :
    MemLp (fun ω => ‖e ω‖*‖x ω‖) 2 P ∧
    (∫ ω, (‖e ω‖*‖x ω‖)^2 ∂P) ≤ Real.sqrt q*Real.sqrt R := by
  have hp : MemLp (fun ω => ‖e ω‖*‖x ω‖) 2 P := he.norm.mul hx.norm
  have he2 : MemLp (fun ω => ‖e ω‖^2) 2 P := by
    apply (memLp_two_iff_integrable_sq (he.aestronglyMeasurable.norm.pow 2)).mpr
    simpa only [Pi.pow_apply,← pow_mul] using he.integrable_norm_pow (p := 4) (by decide)
  have hx2 : MemLp (fun ω => ‖x ω‖^2) 2 P := by
    apply (memLp_two_iff_integrable_sq (hx.aestronglyMeasurable.norm.pow 2)).mpr
    simpa only [Pi.pow_apply,← pow_mul] using hx.integrable_norm_pow (p := 4) (by decide)
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ (fun ω => sq_nonneg ‖e ω‖)) (ae_of_all _ (fun ω => sq_nonneg ‖x ω‖))
    (by norm_num;exact he2) (by norm_num;exact hx2)
  have hb : (∫ ω, (‖e ω‖*‖x ω‖)^2 ∂P) ≤
      Real.sqrt (∫ ω, ‖e ω‖^4 ∂P)*Real.sqrt (∫ ω, ‖x ω‖^4 ∂P) := by
    simpa only [Real.rpow_two,← Real.sqrt_eq_rpow,← pow_mul,mul_pow] using hcs
  exact ⟨hp,hb.trans (mul_le_mul (Real.sqrt_le_sqrt heq) (Real.sqrt_le_sqrt hxR)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))⟩

/-- 確率測度でのL4→L2。q=0でも割り算しない。 -/
theorem fourth_to_second {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) [IsProbabilityMeasure P] (e : Ω → E) (he : MemLp e 4 P)
    (q : ℝ) (hq : 0 ≤ q) (hb : (∫ ω, ‖e ω‖^4 ∂P) ≤ q) :
    MemLp e 2 P ∧ (∫ ω, ‖e ω‖^2 ∂P) ≤ Real.sqrt q := by
  refine ⟨he.mono_exponent (by norm_num),?_⟩
  exact (Real.le_sqrt (integral_nonneg (fun _ => sq_nonneg _)) hq).mpr
    ((second_moment_sq_le_fourth he.norm).trans hb)

/-- N^-2の第4モーメントはsqrtによってN^-1へ移る。零エネルギーを許す。 -/
theorem sqrt_fourth_rate (C : ℝ) (hC : 0 ≤ C) (N : ℕ) :
    Real.sqrt (C/(N : ℝ)^2) = Real.sqrt C/(N : ℝ) := by
  rw [Real.sqrt_div hC,Real.sqrt_sq (by positivity)]

end WMFKIFeatureCoupling
