import Lean_Code.Definitions
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace WMFKI

open scoped BigOperators
open MeasureTheory

abbrev Coeff (M : ℕ) := EuclideanSpace ℝ (Fin M)

noncomputable def partialL1 {M : ℕ} (S : Finset (Fin M)) (u : Coeff M) : ℝ :=
  ∑ i ∈ S, |u i|

noncomputable def l1Norm {M : ℕ} (u : Coeff M) : ℝ := partialL1 Finset.univ u

def SparseCone {M : ℕ} (S : Finset (Fin M)) (u : Coeff M) : Prop :=
  partialL1 Sᶜ u ≤ 3 * partialL1 S u

variable {M : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

noncomputable def lassoObjective (B : Coeff M →L[ℝ] F) (y : F) (lam : ℝ) (θ : Coeff M) : ℝ :=
  (1 / 2 : ℝ) * ‖B θ - y‖ ^ 2 + lam * l1Norm θ

def IsLasso (B : Coeff M →L[ℝ] F) (y : F) (lam : ℝ) (θhat : Coeff M) : Prop :=
  ∀ θ, lassoObjective B y lam θhat ≤ lassoObjective B y lam θ

def ConeLowerBound (B : Coeff M →L[ℝ] F) (S : Finset (Fin M)) (g : ℝ) : Prop :=
  ∀ u, SparseCone S u → g * ‖u‖ ≤ ‖B u‖

def ColumnBound (B : Coeff M →L[ℝ] F) (R : ℝ) : Prop :=
  ∀ i, ‖B (EuclideanSpace.single i 1)‖ ≤ R

variable [CompleteSpace F]

/-- 2‖B*ξ‖∞≤λを座標ごとの不等式として記述する。 -/
def ScoreBound (B : Coeff M →L[ℝ] F) (ξ : F) (lam : ℝ) : Prop :=
  ∀ i, 2 * |(B.adjoint ξ) i| ≤ lam

def LassoDeterministicStatement (M : ℕ) (F : Type*)
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] : Prop :=
  ∀ (B : Coeff M →L[ℝ] F) (y : F) (θstar θhat : Coeff M)
    (S : Finset (Fin M)) (lam g : ℝ),
    0 < lam → 0 < g → (∀ i ∉ S, θstar i = 0) →
    IsLasso B y lam θhat → ScoreBound B (y - B θstar) lam → ConeLowerBound B S g →
    SparseCone S (θhat - θstar) ∧
      ‖θhat - θstar‖ ^ 2 ≤ 9 * (S.card : ℝ) * lam ^ 2 / g ^ 4

/-- 原稿4.12(ii)の抽象回帰部分。V,Dの粒子解析は入力仮定として残る。 -/
def LassoRecoveryStatement (M : ℕ) (F : Type*)
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] : Prop :=
  ∀ (Ω : Type*) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
    (B : Ω → Coeff M →L[ℝ] F) (A : Coeff M →L[ℝ] F)
    (y : Ω → F) (θstar : Coeff M) (θhat : Ω → Coeff M)
    (S : Finset (Fin M)) (γ R δ ε D V lam : ℝ),
    0 < γ → 0 ≤ R → 0 < δ → 0 < ε → δ + ε < 1 → 0 ≤ V → 0 < lam →
    (∀ i ∉ S, θstar i = 0) → ConeLowerBound A S γ → ColumnBound A R →
    Measurable (fun ω => ‖B ω - A‖ ^ 2) →
    Measurable (fun ω => ‖y ω - B ω θstar‖ ^ 2) →
    Integrable (fun ω => ‖B ω - A‖ ^ 2) μ →
    Integrable (fun ω => ‖y ω - B ω θstar‖ ^ 2) μ →
    (∫ ω, ‖B ω - A‖ ^ 2 ∂μ) ≤ D →
    (∫ ω, ‖y ω - B ω θstar‖ ^ 2 ∂μ) ≤ V →
    D ≤ δ * γ ^ 2 / 4 →
    2 * (R + γ / 2) * Real.sqrt (V / ε) ≤ lam →
    (∀ ω, IsLasso (B ω) (y ω) lam (θhat ω)) →
    ∃ G : Set Ω, MeasurableSet G ∧ 1 - δ - ε ≤ μ.real G ∧
      ∀ ω ∈ G, SparseCone S (θhat ω - θstar) ∧
        ‖θhat ω - θstar‖ ^ 2 ≤ 144 * (S.card : ℝ) * lam ^ 2 / γ ^ 4

end WMFKI
