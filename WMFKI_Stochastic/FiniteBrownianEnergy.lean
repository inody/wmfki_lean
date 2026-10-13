import Chapter11FiniteIsometry
import Chapter5ItoOrthogonality
import Chapter3OrthogonalSum
import EndToEndBrownianPathMoments

open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter11
namespace WMFKIExternalProbe

/-- No independence of the random integrands or their integrals is used. -/
theorem finite_brownian_integrals_energy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (B : BrownianSystem P n) (T : ℝ) (hT : 0 ≤ T)
    (H : Fin n → Ω × ℝ → ℝ) (hm : ∀ i, Measurable (H i))
    (hp : ∀ i, @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) T => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) T => H i (z.1,z.2.val)))
    (hi : ∀ i, Integrable (fun z => H i z^2) (P.prod (volume.restrict (Ioo 0 T)))) :
    ∃ M : Fin n → HalfClosedTime → Ω → ℝ,
      (∀ i, ContinuousM2Witness P B.F (M i)) ∧
      (∀ i, LocalMProcessWitness P B.F (M i)) ∧
      (∀ i, ItoCovarianceFormula P B.F (B.W i)
        (fun z => (Iic T).indicator (fun r => H i (z.1,r)) z.2) (M i)) ∧
      ContinuousM2Witness P B.F (fun t ω => ∑ i, M i t ω) ∧
      (∫ ω, (∑ i, M i (realTimeClamp T) ω)^2 ∂P) =
        ∑ i, ∫ z, H i z^2 ∂P.prod (volume.restrict (Ioo 0 T)) := by
  classical
  choose M hM hMl hI using fun i => finite_energy_integral_constructed P
    (Asakura.EndToEnd.coordinateBrownianSystem B i) (H i) (hm i) T hT (hp i) (hi i)
  let G := fun i (z : Ω × ℝ) => (Iic T).indicator (fun r => H i (z.1,r)) z.2
  have hG i : Measurable (G i) := by
    change Measurable ((Prod.snd ⁻¹' Iic T).indicator (H i))
    exact (hm i).indicator (measurableSet_Iic.preimage measurable_snd)
  have hstop t : MeasurableSet[B.F t] {ω : Ω | realTimeClamp (T := (⊤ : EReal)) T ≤ t} := by
    by_cases h : realTimeClamp (T := (⊤ : EReal)) T ≤ t <;> simp [h]
  have hMs i := continuous_m2_stopped P B.F B.mono B.le (M i) (hM i)
    (fun _ => realTimeClamp T) hstop
  have hIs i := stopped_ito_covariance_formula P (by simp : (0 : EReal) < ⊤)
    B.F B.mono B.le B.null (B.W i) (M i) (G i) (B.martingale i) (hMl i)
    (fun _ => (hG i).comp measurable_prodMk_left) (hI i) T hT
  have hcross i j (hij : i ≠ j) : LocalCovarianceWitness P B.F (B.W i) (B.W j) (fun _ _ => 0) := by
    apply (B.cov i j).congr_values_before_terminal P B.F
    intro t ht
    obtain ⟨r,hr,_,he⟩ := finite_closed_time_real t ht
    rw [← he]
    funext ω
    simpa only [hij,ite_false] using B.clock i j ω r hr
  have horth i j (hij : i ≠ j) : (∫ ω, M i (realTimeClamp T) ω*M j (realTimeClamp T) ω ∂P) = 0 := by
    have hh := ito_integrals_terminal_orthogonal P (by simp : (0 : EReal) < ⊤)
      B.F B.mono B.le (B.W i) (B.W j)
      (fun t ω => M i (min (realTimeClamp T) t) ω)
      (fun t ω => M j (min (realTimeClamp T) t) ω)
      (B.martingale i) (B.martingale j) (hMs i) (hMs j) (hcross i j hij)
      (fun z => (Ioc 0 T).indicator (fun r => G i (z.1,r)) z.2)
      (fun z => (Ioc 0 T).indicator (fun r => G j (z.1,r)) z.2)
      (fun _ => ((hG i).comp measurable_prodMk_left).indicator measurableSet_Ioc)
      (fun _ => ((hG j).comp measurable_prodMk_left).indicator measurableSet_Ioc) (hIs i) (hIs j)
    simpa only [min_top_right] using hh
  refine ⟨M,hM,hMl,hI,finite_sum_m2 P B.F Finset.univ M (fun i _ => hM i),?_⟩
  rw [orthogonal_sum_energy P Finset.univ (fun i => M i (realTimeClamp T))
    (fun i _ => (hM i).moment _) (fun i _ j _ hij => horth i j hij)]
  apply Finset.sum_congr rfl
  intro i _
  exact (finite_ito_isometry P (Asakura.EndToEnd.coordinateBrownianSystem B i)
    (H i) (hm i) T hT (hp i) (hi i) (M i) (hM i) (hI i)).symm

theorem continuous_m2_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (M : HalfClosedTime → Ω → ℝ) (hM : ContinuousM2Witness P F M) (t : HalfClosedTime) :
    Integrable (M t) P ∧ (∫ ω, M t ω ∂P) = 0 := by
  refine ⟨(hM.moment t).integrable (by norm_num),?_⟩
  calc
    (∫ ω, M t ω ∂P) = ∫ ω, P[M t | F ⊥] ω ∂P := (integral_condExp (hle ⊥)).symm
    _ = ∫ ω, M ⊥ ω ∂P := integral_congr_ae (hM.martingale ⊥ t bot_le)
    _ = 0 := by rw [integral_congr_ae hM.initial]; simp

end WMFKIExternalProbe
