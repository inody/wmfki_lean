import WMFKI_Stochastic.ActualFeatureProcesses

open MeasureTheory Set
namespace WMFKIFeatureCoupling

/-- 有限測度上の二乗Jensen。零時間測度を含み、積分の存在を先に要求。 -/
theorem finite_measure_second_jensen {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] {f : S → ℝ} (hf : MemLp f 2 μ) :
    (∫ s, f s ∂μ)^2 ≤ μ.real univ*(∫ s, (f s)^2 ∂μ) := by
  by_cases hz : μ = 0
  · subst μ
    simp
  have : NeZero μ := ⟨hz⟩
  have hpos : 0 < μ.real univ := measureReal_univ_pos
  have hc : ConvexOn ℝ univ (fun x : ℝ => ‖x‖^2) :=
    convexOn_univ_norm.pow (fun x _ => norm_nonneg x) 2
  have hi : Integrable ((fun x : ℝ => ‖x‖^2) ∘ f) μ := hf.integrable_norm_pow (p := 2) (by decide)
  have hj := hc.map_average_le (continuous_norm.pow 2).continuousOn isClosed_univ
    (ae_of_all _ (fun _ => mem_univ _)) (hf.integrable (by norm_num)) hi
  simp only [average_eq,smul_eq_mul,Real.norm_eq_abs,sq_abs,mul_pow] at hj
  have hh := mul_le_mul_of_nonneg_left hj (sq_nonneg (μ.real univ))
  convert hh using 1 <;> field_simp

/-- 各時間断面のL2評価から、二乗の積空間可積分性を導く。 -/
theorem product_second_integrable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (μ : Measure S) (P : Measure Ω) [IsFiniteMeasure μ] [IsProbabilityMeasure P]
    (f : S × Ω → ℝ) (hm : StronglyMeasurable f) (C : ℝ)
    (hf : ∀ᵐ s ∂μ, MemLp (fun ω => f (s,ω)) 2 P ∧ (∫ ω, f (s,ω)^2 ∂P) ≤ C) :
    Integrable (fun z => f z^2) (μ.prod P) := by
  have hsm : StronglyMeasurable (fun z => f z^2) := hm.pow 2
  apply (integrable_prod_iff hsm.aestronglyMeasurable).mpr
  refine ⟨hf.mono (fun _ hs => hs.1.integrable_sq),?_⟩
  apply (integrable_const C).mono' hsm.norm.integral_prod_right'.aestronglyMeasurable
  filter_upwards [hf] with s hs
  rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  simpa only [Real.norm_eq_abs,abs_pow,sq_abs] using hs.2

/-- Fubiniの前提となるf自体の可積分性も結論に含め、後の積分差の同定に使う。 -/
theorem finite_integral_second_moment {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (μ : Measure S) (P : Measure Ω) [IsFiniteMeasure μ] [IsProbabilityMeasure P]
    (f : S × Ω → ℝ) (hm : StronglyMeasurable f) (C : ℝ)
    (hf : ∀ᵐ s ∂μ, MemLp (fun ω => f (s,ω)) 2 P ∧ (∫ ω, f (s,ω)^2 ∂P) ≤ C) :
    Integrable f (μ.prod P) ∧ MemLp (fun ω => ∫ s, f (s,ω) ∂μ) 2 P ∧
    (∫ ω, (∫ s, f (s,ω) ∂μ)^2 ∂P) ≤ (μ.real univ)^2*C := by
  have h2 := product_second_integrable μ P f hm C hf
  have hLp := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr h2
  have hH := hm.integral_prod_left' (μ := μ)
  have hb : ∀ᵐ ω ∂P, (∫ s, f (s,ω) ∂μ)^2 ≤ μ.real univ*(∫ s, f (s,ω)^2 ∂μ) := by
    filter_upwards [h2.prod_left_ae] with ω hω
    exact finite_measure_second_jensen μ ((memLp_two_iff_integrable_sq
      (hm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hω)
  have hHi : Integrable (fun ω => (∫ s, f (s,ω) ∂μ)^2) P := by
    apply (h2.integral_prod_right.const_mul (μ.real univ)).mono' (hH.pow 2).aestronglyMeasurable
    filter_upwards [hb] with ω hω
    simpa only [Pi.pow_apply,Real.norm_eq_abs,abs_pow,sq_abs] using hω
  refine ⟨hLp.integrable (by norm_num),(memLp_two_iff_integrable_sq hH.aestronglyMeasurable).mpr hHi,?_⟩
  calc
    _ ≤ ∫ ω, μ.real univ*(∫ s, f (s,ω)^2 ∂μ) ∂P :=
      integral_mono_ae hHi (h2.integral_prod_right.const_mul _) hb
    _ = μ.real univ*(∫ s, ∫ ω, f (s,ω)^2 ∂P ∂μ) := by
      rw [integral_const_mul,← integral_prod_symm _ h2,integral_prod _ h2]
    _ ≤ μ.real univ*(∫ _s, C ∂μ) :=
      mul_le_mul_of_nonneg_left (integral_mono_ae h2.integral_prod_left (integrable_const C)
        (hf.mono (fun _ h => h.2))) (by positivity)
    _ = _ := by simp only [integral_const,smul_eq_mul];ring

end WMFKIFeatureCoupling
