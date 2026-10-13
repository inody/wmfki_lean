import Lean_Code.Deterministic
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace WMFKI

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]

/-- 最小化性を定義に含めず、Moore–Penroseの四つの作用素等式を使う。 -/
structure IsMoorePenrose (B : E →L[ℝ] F) (P : F →L[ℝ] E) : Prop where
  bpb : (B.comp P).comp B = B
  pbp : (P.comp B).comp P = P
  bp_selfadjoint : (B.comp P).adjoint = B.comp P
  pb_selfadjoint : (P.comp B).adjoint = P.comp B

omit [CompleteSpace E] [CompleteSpace F] in
/-- 正規方程式の直交性から最小化性を導く。 -/
theorem isLeastSquares_of_orthogonal (B : E →L[ℝ] F) (y : F) (θhat : E)
    (ho : ∀ u, inner ℝ (B θhat - y) (B u) = 0) : IsLeastSquares B y θhat := by
  intro θ
  have heq : B θ - y = (B θhat - y) + B (θ - θhat) := by
    simp only [map_sub]
    abel
  rw [heq, norm_add_sq_real, ho]
  nlinarith [sq_nonneg ‖B (θ - θhat)‖]

theorem moorePenrose_isLeastSquares (B : E →L[ℝ] F) (P : F →L[ℝ] E)
    (h : IsMoorePenrose B P) (y : F) : IsLeastSquares B y (P y) := by
  apply isLeastSquares_of_orthogonal
  intro u
  have hfix : (B.comp P) (B u) = B u :=
    congrArg (fun T : E →L[ℝ] F => T u) h.bpb
  change inner ℝ ((B.comp P) y - y) (B u) = 0
  rw [inner_sub_left, ← (B.comp P).adjoint_inner_right y (B u),
    h.bp_selfadjoint, hfix, sub_self]

/-- 擬似逆で定義した推定量に、先に証明したOLS評価を直接適用できる。 -/
theorem moorePenrose_error_bound (B : E →L[ℝ] F) (P : F →L[ℝ] E)
    (h : IsMoorePenrose B P) (y : F) (θstar : E)
    (g : ℝ) (hg : 0 < g) (hB : LowerBound B g) :
    g ^ 2 * ‖P y - θstar‖ ^ 2 ≤ ‖y - B θstar‖ ^ 2 :=
  leastSquares_error_bound B y θstar (P y) g hg hB (moorePenrose_isLeastSquares B P h y)

end WMFKI
