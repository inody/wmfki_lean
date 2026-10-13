import WMFKI_Stochastic.FiniteMeasureSecondIntegral

open MeasureTheory Set
open WMFKIExternalProbe
open scoped BigOperators
namespace WMFKIFeatureCoupling
variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def offDiagonalAverage (N : ℕ) (f : Fin N → Fin N → Ω → ℝ) (ω : Ω) : ℝ :=
  (N : ℝ)⁻¹^2*∑ i,∑ j,if i=j then 0 else f i j ω

noncomputable def continuousPairAverage (N : ℕ) (T : ℝ)
    (f : ℝ → Fin N → Fin N → Ω → ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..T, offDiagonalAverage N (f s) ω

theorem off_diagonal_average_second (P : Measure Ω) (N : ℕ) (hN : 0 < N)
    (f : Fin N → Fin N → Ω → ℝ) (hf : ∀ i j, MemLp (f i j) 2 P)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ i j, (∫ ω, (f i j ω)^2 ∂P) ≤ C) :
    MemLp (offDiagonalAverage N f) 2 P ∧ (∫ ω, (offDiagonalAverage N f ω)^2 ∂P) ≤ C := by
  have he : pairTimeAverage N 1 (fun _ => 1) (fun _ => f) = offDiagonalAverage N f := by
    funext ω
    simp [offDiagonalAverage,pairTimeAverage]
  simpa only [he,Fin.sum_univ_one,abs_one,one_pow,one_mul] using
    pair_time_average_moment P N 1 hN (fun _ => 1) (fun _ => f) (fun _ => hf) C hC (fun _ => hb)

theorem off_diagonal_average_measurable (N : ℕ) (f : Fin N → Fin N → Ω → ℝ)
    (hf : ∀ i j, StronglyMeasurable (f i j)) : StronglyMeasurable (offDiagonalAverage N f) := by
  apply Measurable.stronglyMeasurable
  unfold offDiagonalAverage
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  by_cases h : i=j
  · simp only [h,ite_true]
    exact measurable_const
  · simp only [h,ite_false]
    exact (hf i j).measurable

omit [MeasurableSpace Ω] in
theorem off_diagonal_average_sub (N : ℕ) (f g : Fin N → Fin N → Ω → ℝ) (ω : Ω) :
    offDiagonalAverage N (fun i j ω => f i j ω-g i j ω) ω =
      offDiagonalAverage N f ω-offDiagonalAverage N g ω := by
  have he (i j : Fin N) : (if i=j then 0 else f i j ω-g i j ω) =
      (if i=j then 0 else f i j ω)-(if i=j then 0 else g i j ω) := by
    by_cases h : i=j <;> simp [h]
  simp only [offDiagonalAverage,he,Finset.sum_sub_distrib,mul_sub]

/-- 時間と粒子対の独立性は一切使わない。T^2とN^-2の全ペア正規化を保持。 -/
theorem continuous_pair_average_second (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ) (hN : 0 < N) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → Fin N → Fin N → Ω → ℝ)
    (hm : ∀ i j, StronglyMeasurable (fun z : ℝ × Ω => f z.1 i j z.2))
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ s ∈ Icc 0 T, ∀ i j, MemLp (f s i j) 2 P ∧ (∫ ω, (f s i j ω)^2 ∂P) ≤ C) :
    MemLp (continuousPairAverage N T f) 2 P ∧
    (∫ ω, (continuousPairAverage N T f ω)^2 ∂P) ≤ T^2*C ∧
    (∀ᵐ ω ∂P, IntervalIntegrable (fun s => offDiagonalAverage N (f s) ω) volume 0 T) := by
  let μ := volume.restrict (Ioc (0 : ℝ) T)
  have hj : StronglyMeasurable (fun z : ℝ × Ω => offDiagonalAverage N (f z.1) z.2) :=
    off_diagonal_average_measurable N (fun i j (z : ℝ × Ω) => f z.1 i j z.2) hm
  have hs : ∀ᵐ s ∂μ, MemLp (fun ω => offDiagonalAverage N (f s) ω) 2 P ∧
      (∫ ω, (offDiagonalAverage N (f s) ω)^2 ∂P) ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact off_diagonal_average_second P N hN (f s) (fun i j => (hf s ⟨hs.1.le,hs.2⟩ i j).1)
      C hC (fun i j => (hf s ⟨hs.1.le,hs.2⟩ i j).2)
  obtain ⟨hi,hL,hB⟩ := finite_integral_second_moment μ P _ hj C hs
  have hμ : μ.real univ = T := by
    simp [μ,measureReal_def,Real.volume_Ioc,ENNReal.toReal_ofReal hT]
  have he : (fun ω => ∫ s, offDiagonalAverage N (f s) ω ∂μ) = continuousPairAverage N T f := by
    funext ω
    rw [continuousPairAverage,intervalIntegral.integral_of_le hT]
  refine ⟨?_,?_,?_⟩
  · simpa only [he] using hL
  · simpa only [continuousPairAverage,intervalIntegral.integral_of_le hT,hμ] using hB
  · filter_upwards [hi.prod_left_ae] with ω hω
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr hω

/-- 両方の時間積分の可積分性を得てから、実際の設計差と差の積分を同定。 -/
theorem continuous_pair_average_sub (P : Measure Ω) (N : ℕ) (T : ℝ)
    (f g : ℝ → Fin N → Fin N → Ω → ℝ)
    (hf : ∀ᵐ ω ∂P, IntervalIntegrable (fun s => offDiagonalAverage N (f s) ω) volume 0 T)
    (hg : ∀ᵐ ω ∂P, IntervalIntegrable (fun s => offDiagonalAverage N (g s) ω) volume 0 T) :
    (fun ω => continuousPairAverage N T f ω-continuousPairAverage N T g ω) =ᵐ[P]
      continuousPairAverage N T (fun s i j ω => f s i j ω-g s i j ω) := by
  filter_upwards [hf,hg] with ω hω kω
  unfold continuousPairAverage
  simp_rw [off_diagonal_average_sub]
  exact (intervalIntegral.integral_sub hω kω).symm

end WMFKIFeatureCoupling
