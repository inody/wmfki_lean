import Lean_Code.Deterministic
import Lean_Code.Probability

namespace WMFKI

open MeasureTheory

/-- 二乗平均仮定からのOLS回復。粒子モデルのモーメント評価は含まない。 -/
theorem oracle_recovery_of_moments
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    OracleRecoveryStatement (E := E) (F := F) := by
  intro Ω m μ hprob B A y θstar θhat γ δ ε D V hγ hδ hε _hprob_sum hV
    hA hBm hym hBi hyi hBD hyV hsmall hfit
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
  have hsc : μ.real sᶜ ≤ δ := by
    simpa only [s, Set.compl_ofPred, not_le] using hds
  have htc : μ.real tᶜ ≤ ε := by
    simpa only [t, Set.compl_ofPred, not_le] using hts
  refine ⟨s ∩ t, hs.inter ht, good_event_intersection μ s t δ ε hs ht hsc htc, ?_⟩
  intro ω hω
  have hsq : ‖B ω - A‖ ^ 2 ≤ (γ / 2) ^ 2 := hω.1
  have hpert : ‖B ω - A‖ ≤ γ / 2 := by nlinarith [norm_nonneg (B ω - A)]
  have hb := lowerBound_perturb A (B ω) γ (γ / 2) hA hpert
  have hgap : γ - γ / 2 = γ / 2 := by ring
  rw [hgap] at hb
  have herr := leastSquares_error_bound (B ω) (y ω) θstar (θhat ω)
    (γ / 2) (by positivity) hb (hfit ω)
  have hres : ‖y ω - B ω θstar‖ ^ 2 ≤ V / ε := hω.2
  have hmul := mul_le_mul_of_nonneg_right (herr.trans hres) hε.le
  rw [div_mul_cancel₀ V hε.ne'] at hmul
  apply (le_div_iff₀ (mul_pos hε (sq_pos_of_pos hγ))).mpr
  nlinarith

end WMFKI
