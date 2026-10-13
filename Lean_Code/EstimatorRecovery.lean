import Lean_Code.MoorePenroseConstruction
import Lean_Code.MainTheorem
import Lean_Code.LassoExistence
import Lean_Code.LassoRecovery

namespace WMFKI

open MeasureTheory

/-- 最小化性を仮定せず、構成した擬似逆推定量にOLS回復定理を適用する。 -/
theorem oracle_moorePenrose_recovery
    {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [FiniteDimensional ℝ E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Ω → E →L[ℝ] F) (A : E →L[ℝ] F) (y : Ω → F) (θstar : E)
    (γ δ ε D V : ℝ) (hγ : 0 < γ) (hδ : 0 < δ) (hε : 0 < ε)
    (hprob : δ + ε < 1) (hV : 0 ≤ V) (hA : LowerBound A γ)
    (hBm : Measurable (fun ω => ‖B ω - A‖ ^ 2))
    (hym : Measurable (fun ω => ‖y ω - B ω θstar‖ ^ 2))
    (hBi : Integrable (fun ω => ‖B ω - A‖ ^ 2) μ)
    (hyi : Integrable (fun ω => ‖y ω - B ω θstar‖ ^ 2) μ)
    (hBD : (∫ ω, ‖B ω - A‖ ^ 2 ∂μ) ≤ D)
    (hyV : (∫ ω, ‖y ω - B ω θstar‖ ^ 2 ∂μ) ≤ V)
    (hsmall : D ≤ δ * γ ^ 2 / 4) :
    ∃ G : Set Ω, MeasurableSet G ∧ 1 - δ - ε ≤ μ.real G ∧
      ∀ ω ∈ G, ‖moorePenrose (B ω) (y ω) - θstar‖ ^ 2 ≤ 4 * V / (ε * γ ^ 2) :=
  oracle_recovery_of_moments Ω inferInstance μ inferInstance B A y θstar
    (fun ω => moorePenrose (B ω) (y ω)) γ δ ε D V hγ hδ hε hprob hV hA
    hBm hym hBi hyi hBD hyV hsmall (fun ω => moorePenrose_minimizes (B ω) (y ω))

/-- LASSO解の存在を含め、最小化性の入力仮定を除いた抽象回復定理。 -/
theorem lasso_estimator_recovery
    {Ω F : Type*} {M : ℕ} [MeasurableSpace Ω]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Ω → Coeff M →L[ℝ] F) (A : Coeff M →L[ℝ] F)
    (y : Ω → F) (θstar : Coeff M) (S : Finset (Fin M))
    (γ R δ ε D V lam : ℝ) (hγ : 0 < γ) (hR : 0 ≤ R) (hδ : 0 < δ) (hε : 0 < ε)
    (hprob : δ + ε < 1) (hV : 0 ≤ V) (hlam : 0 < lam)
    (hsupp : ∀ i ∉ S, θstar i = 0) (hA : ConeLowerBound A S γ) (hcol : ColumnBound A R)
    (hBm : Measurable (fun ω => ‖B ω - A‖ ^ 2))
    (hym : Measurable (fun ω => ‖y ω - B ω θstar‖ ^ 2))
    (hBi : Integrable (fun ω => ‖B ω - A‖ ^ 2) μ)
    (hyi : Integrable (fun ω => ‖y ω - B ω θstar‖ ^ 2) μ)
    (hBD : (∫ ω, ‖B ω - A‖ ^ 2 ∂μ) ≤ D)
    (hyV : (∫ ω, ‖y ω - B ω θstar‖ ^ 2 ∂μ) ≤ V)
    (hsmall : D ≤ δ * γ ^ 2 / 4)
    (hpen : 2 * (R + γ / 2) * Real.sqrt (V / ε) ≤ lam) :
    ∃ G : Set Ω, MeasurableSet G ∧ 1 - δ - ε ≤ μ.real G ∧
      ∀ ω ∈ G, SparseCone S (lassoEstimator (B ω) (y ω) lam hlam - θstar) ∧
        ‖lassoEstimator (B ω) (y ω) lam hlam - θstar‖ ^ 2 ≤
          144 * (S.card : ℝ) * lam ^ 2 / γ ^ 4 :=
  lasso_recovery_of_moments Ω inferInstance μ inferInstance B A y θstar
    (fun ω => lassoEstimator (B ω) (y ω) lam hlam) S γ R δ ε D V lam
    hγ hR hδ hε hprob hV hlam hsupp hA hcol hBm hym hBi hyi hBD hyV hsmall hpen
    (fun ω => lassoEstimator_minimizes (B ω) (y ω) lam hlam)

end WMFKI
