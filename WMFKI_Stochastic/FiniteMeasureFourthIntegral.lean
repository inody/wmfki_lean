import WMFKI_Stochastic.FluctuationJointMeasurable
import Mathlib.Analysis.Convex.Integral

open MeasureTheory Set
open WMFKIIndependentFourth
namespace WMFKIRealizedFluctuation

/-- 有限測度版の第4乗Jensen。不等式の前にL4を要求し、零測度も含む。 -/
theorem finite_measure_fourth_jensen {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] {f : S → ℝ} (hf : MemLp f 4 μ) :
    (∫ s, f s ∂μ)^4 ≤ (μ.real univ)^3*(∫ s, (f s)^4 ∂μ) := by
  by_cases hz : μ = 0
  · subst μ
    simp
  have : NeZero μ := ⟨hz⟩
  have hpos : 0 < μ.real univ := measureReal_univ_pos
  have hc : ConvexOn ℝ univ (fun x : ℝ => ‖x‖^4) :=
    convexOn_univ_norm.pow (fun x _ => norm_nonneg x) 4
  have hi : Integrable ((fun x : ℝ => ‖x‖^4) ∘ f) μ := hf.integrable_norm_pow (p := 4) (by decide)
  have hj := hc.map_average_le (continuous_norm.pow 4).continuousOn isClosed_univ
    (ae_of_all _ (fun _ => mem_univ _)) (hf.integrable (by norm_num)) hi
  simp only [average_eq,smul_eq_mul,Real.norm_eq_abs,
    (show Even (4 : ℕ) from by decide).pow_abs,mul_pow] at hj
  have hh := mul_le_mul_of_nonneg_left hj (le_of_lt (pow_pos hpos 4))
  convert hh using 1 <;> field_simp

/-- 二変数関数の各断面L4と一様モーメントから、積空間での可積分性を先に導く。 -/
theorem product_fourth_integrable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (μ : Measure S) (P : Measure Ω) [IsFiniteMeasure μ] [IsProbabilityMeasure P]
    (f : S × Ω → ℝ) (hm : StronglyMeasurable f) (C : ℝ)
    (hf : ∀ᵐ s ∂μ, MemLp (fun ω => f (s,ω)) 4 P ∧ (∫ ω, f (s,ω)^4 ∂P) ≤ C) :
    Integrable (fun z => f z^4) (μ.prod P) := by
  have hsm : StronglyMeasurable (fun z => f z^4) := hm.pow 4
  apply (integrable_prod_iff hsm.aestronglyMeasurable).mpr
  refine ⟨hf.mono (fun s hs => ?_),?_⟩
  · simpa only [Real.norm_eq_abs,(show Even (4 : ℕ) from by decide).pow_abs] using
      hs.1.integrable_norm_pow (p := 4) (by decide)
  · apply (integrable_const C).mono' hsm.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hf] with s hs
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simpa only [Real.norm_eq_abs,abs_pow,(show Even (4 : ℕ) from by decide).pow_abs] using hs.2

/-- Fubiniと有限測度Jensen。時間積分そのもののL4と期待値評価を同時に得る。 -/
theorem finite_integral_fourth_moment {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (μ : Measure S) (P : Measure Ω) [IsFiniteMeasure μ] [IsProbabilityMeasure P]
    (f : S × Ω → ℝ) (hm : StronglyMeasurable f) (C : ℝ)
    (hf : ∀ᵐ s ∂μ, MemLp (fun ω => f (s,ω)) 4 P ∧ (∫ ω, f (s,ω)^4 ∂P) ≤ C) :
    MemLp (fun ω => ∫ s, f (s,ω) ∂μ) 4 P ∧
    (∫ ω, (∫ s, f (s,ω) ∂μ)^4 ∂P) ≤ (μ.real univ)^4*C := by
  have h4 := product_fourth_integrable μ P f hm C hf
  have hH := hm.integral_prod_left' (μ := μ)
  have hb : ∀ᵐ ω ∂P, (∫ s, f (s,ω) ∂μ)^4 ≤ (μ.real univ)^3*(∫ s, f (s,ω)^4 ∂μ) := by
    filter_upwards [h4.prod_left_ae] with ω hω
    exact finite_measure_fourth_jensen μ (l4_of_integrable_fourth μ
      (hm.measurable.comp (measurable_id.prodMk measurable_const)) hω)
  have hHi : Integrable (fun ω => (∫ s, f (s,ω) ∂μ)^4) P := by
    apply (h4.integral_prod_right.const_mul ((μ.real univ)^3)).mono' (hH.pow 4).aestronglyMeasurable
    filter_upwards [hb] with ω hω
    simpa only [Pi.pow_apply,Real.norm_eq_abs,abs_pow,(show Even (4 : ℕ) from by decide).pow_abs] using hω
  refine ⟨l4_of_integrable_fourth P hH.measurable hHi,?_⟩
  calc
    _ ≤ ∫ ω, (μ.real univ)^3*(∫ s, f (s,ω)^4 ∂μ) ∂P :=
      integral_mono_ae hHi (h4.integral_prod_right.const_mul _) hb
    _ = (μ.real univ)^3*(∫ s, ∫ ω, f (s,ω)^4 ∂P ∂μ) := by
      rw [integral_const_mul,← integral_prod_symm _ h4,integral_prod _ h4]
    _ ≤ (μ.real univ)^3*(∫ _s, C ∂μ) :=
      mul_le_mul_of_nonneg_left (integral_mono_ae h4.integral_prod_left (integrable_const C)
        (hf.mono (fun _ h => h.2))) (by positivity)
    _ = _ := by simp only [integral_const,smul_eq_mul];ring

end WMFKIRealizedFluctuation
