import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real

/-! 原稿との対応・未形式化の上流仮定は Blueprint.md を参照。 -/

namespace WMFKI

open MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- 全方向の下界。非零特異値だけの最小値とは異なる。 -/
def LowerBound (A : E →L[ℝ] F) (γ : ℝ) : Prop :=
  ∀ u, γ * ‖u‖ ≤ ‖A u‖

/-- 二乗Euclidean損失の任意の最小化解。 -/
def IsLeastSquares (B : E →L[ℝ] F) (y : F) (θhat : E) : Prop :=
  ∀ θ, ‖B θhat - y‖ ^ 2 ≤ ‖B θ - y‖ ^ 2

/-- 定理4.12(i)の抽象回帰部分。SDEからのモーメント評価は仮定であり証明ではない。 -/
def OracleRecoveryStatement : Prop :=
  ∀ (Ω : Type*) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
    (B : Ω → E →L[ℝ] F) (A : E →L[ℝ] F)
    (y : Ω → F) (θstar : E) (θhat : Ω → E)
    (γ δ ε D V : ℝ),
    0 < γ → 0 < δ → 0 < ε → δ + ε < 1 → 0 ≤ V →
    LowerBound A γ →
    Measurable (fun ω => ‖B ω - A‖ ^ 2) →
    Measurable (fun ω => ‖y ω - B ω θstar‖ ^ 2) →
    Integrable (fun ω => ‖B ω - A‖ ^ 2) μ →
    Integrable (fun ω => ‖y ω - B ω θstar‖ ^ 2) μ →
    (∫ ω, ‖B ω - A‖ ^ 2 ∂μ) ≤ D →
    (∫ ω, ‖y ω - B ω θstar‖ ^ 2 ∂μ) ≤ V →
    D ≤ δ * γ ^ 2 / 4 →
    (∀ ω, IsLeastSquares (B ω) (y ω) (θhat ω)) →
    ∃ G : Set Ω, MeasurableSet G ∧ 1 - δ - ε ≤ μ.real G ∧
      ∀ ω ∈ G, ‖θhat ω - θstar‖ ^ 2 ≤ 4 * V / (ε * γ ^ 2)

end WMFKI
