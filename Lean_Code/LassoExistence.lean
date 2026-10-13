import Lean_Code.LassoGeometry
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

namespace WMFKI

open Filter
open scoped Topology

variable {M : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem norm_le_l1Norm (u : Coeff M) : ‖u‖ ≤ l1Norm u := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun i : Fin M => |u i|) (fun i _ => abs_nonneg (u i))
  simp only [sq_abs] at hs
  have hn : 0 ≤ l1Norm u := partialL1_nonneg _ _
  apply (sq_le_sq₀ (norm_nonneg _) hn).mp
  simpa only [l1Norm, partialL1, EuclideanSpace.real_norm_sq_eq] using hs

theorem lassoObjective_continuous (B : Coeff M →L[ℝ] F) (y : F) (lam : ℝ) :
    Continuous (lassoObjective B y lam) := by
  unfold lassoObjective l1Norm partialL1
  fun_prop

/-- 正のペナルティにより目的関数が無限遠で発散し、最小化解が存在する。 -/
theorem exists_lasso (B : Coeff M →L[ℝ] F) (y : F) (lam : ℝ) (hlam : 0 < lam) :
    ∃ θhat, IsLasso B y lam θhat := by
  have hlo (θ : Coeff M) : lam * ‖θ‖ ≤ lassoObjective B y lam θ := by
    have h := mul_le_mul_of_nonneg_left (norm_le_l1Norm θ) hlam.le
    unfold lassoObjective
    nlinarith [sq_nonneg ‖B θ - y‖]
  have hlim : Tendsto (fun θ : Coeff M => lam * ‖θ‖) (cocompact (Coeff M)) atTop :=
    Tendsto.const_mul_atTop hlam tendsto_norm_cocompact_atTop
  exact (lassoObjective_continuous B y lam).exists_forall_le (tendsto_atTop_mono hlo hlim)

noncomputable def lassoEstimator (B : Coeff M →L[ℝ] F) (y : F) (lam : ℝ) (hlam : 0 < lam) :
    Coeff M := Classical.choose (exists_lasso B y lam hlam)

theorem lassoEstimator_minimizes (B : Coeff M →L[ℝ] F) (y : F) (lam : ℝ) (hlam : 0 < lam) :
    IsLasso B y lam (lassoEstimator B y lam hlam) :=
  Classical.choose_spec (exists_lasso B y lam hlam)

end WMFKI
