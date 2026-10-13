import Lean_Code.LassoTransfer
import Lean_Code.Probability

namespace WMFKI

open MeasureTheory

theorem lasso_recovery_of_moments {M : ℕ} {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] : LassoRecoveryStatement M F := by
  intro Ω m μ hprob B A y θstar θhat S γ R δ ε D V lam hγ hR hδ hε _hprob_sum hV
    hlam hsupp hA hcol hBm hym hBi hyi hBD hyV hsmall hpen hfit
  let := m
  let := hprob
  let s : Set Ω := {ω | ‖B ω - A‖ ^ 2 ≤ (γ / 2) ^ 2}
  let t : Set Ω := {ω | ‖y ω - B ω θstar‖ ^ 2 ≤ V / ε}
  have hs : MeasurableSet s := measurableSet_le hBm measurable_const
  have ht : MeasurableSet t := measurableSet_le hym measurable_const
  have hdesign : (∫ ω, ‖B ω - A‖ ^ 2 ∂μ) ≤ δ * (γ / 2) ^ 2 := by
    calc
      _ ≤ D := hBD
      _ ≤ δ * γ ^ 2 / 4 := hsmall
      _ = δ * (γ / 2) ^ 2 := by ring
  have hds := secondMoment_good_event μ (fun ω => ‖B ω - A‖ ^ 2)
    (δ * (γ / 2) ^ 2) δ hBm hBi (fun _ => sq_nonneg _) (by positivity) hδ hdesign
  have hcancel : δ * (γ / 2) ^ 2 / δ = (γ / 2) ^ 2 := by field_simp
  rw [hcancel] at hds
  have hts := secondMoment_good_event μ (fun ω => ‖y ω - B ω θstar‖ ^ 2)
    V ε hym hyi (fun _ => sq_nonneg _) hV hε hyV
  have hsc : μ.real sᶜ ≤ δ := by simpa only [s, Set.compl_ofPred, not_le] using hds
  have htc : μ.real tᶜ ≤ ε := by simpa only [t, Set.compl_ofPred, not_le] using hts
  refine ⟨s ∩ t, hs.inter ht, good_event_intersection μ s t δ ε hs ht hsc htc, ?_⟩
  intro ω hω
  have hsq : ‖B ω - A‖ ^ 2 ≤ (γ / 2) ^ 2 := hω.1
  have hpert : ‖B ω - A‖ ≤ γ / 2 := by nlinarith [norm_nonneg (B ω - A)]
  have hb := coneLowerBound_perturb A (B ω) S γ (γ / 2) hA hpert
  have hgap : γ - γ / 2 = γ / 2 := by ring
  rw [hgap] at hb
  have hcolumn := columnBound_perturb A (B ω) R (γ / 2) hcol hpert
  have hres : ‖y ω - B ω θstar‖ ≤ Real.sqrt (V / ε) := by
    have hh : ‖y ω - B ω θstar‖ ^ 2 ≤ V / ε := hω.2
    nlinarith [Real.sq_sqrt (div_nonneg hV hε.le), Real.sqrt_nonneg (V / ε)]
  have hscore := score_of_column_and_residual (B ω) (y ω - B ω θstar)
    (R + γ / 2) (Real.sqrt (V / ε)) lam (by positivity) hcolumn hres hpen
  obtain ⟨hc, he⟩ := lasso_deterministic (B ω) (y ω) θstar (θhat ω) S lam
    (γ / 2) hlam (by positivity) hsupp (hfit ω) hscore hb
  refine ⟨hc, ?_⟩
  have hn : 9 * (S.card : ℝ) * lam ^ 2 / (γ / 2) ^ 4 =
      144 * (S.card : ℝ) * lam ^ 2 / γ ^ 4 := by ring
  rwa [hn] at he

/-- 下限と等しいペナルティの代入。定数576と全ての分母を検証する。 -/
theorem lasso_penalty_normalization (s R γ V ε : ℝ) (hV : 0 ≤ V) (hε : 0 < ε) :
    144 * s * (2 * (R + γ / 2) * Real.sqrt (V / ε)) ^ 2 / γ ^ 4 =
      576 * s * (R + γ / 2) ^ 2 * V / (ε * γ ^ 4) := by
  rw [mul_pow, Real.sq_sqrt (div_nonneg hV hε.le)]
  ring

end WMFKI
