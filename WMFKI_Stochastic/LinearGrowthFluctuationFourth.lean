import WMFKI_Stochastic.VectorFluctuationFourth

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace WMFKIIndependentFourth

theorem l4_of_integrable_norm_fourth {Ω V : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup V] (P : Measure Ω) {f : Ω → V}
    (hf : AEStronglyMeasurable f P) (hi : Integrable (fun ω => ‖f ω‖^4) P) : MemLp f 4 P := by
  apply (integrable_norm_rpow_iff hf (p := 4) (by norm_num) (by norm_num)).mp
  rw [show (4 : ℝ≥0∞).toReal = ((4 : ℕ) : ℝ) by norm_num]
  simpa only [Real.rpow_natCast] using hi

theorem fourth_three_bound (a b c : ℝ) : (a+b+c)^4 ≤ 27*(a^4+b^4+c^4) := by
  have h : (a+b+c)^2 ≤ 3*(a^2+b^2+c^2) := by
    nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (b-c)]
  have hh := pow_le_pow_left₀ (sq_nonneg (a+b+c)) h 2
  have ht : (a^2+b^2+c^2)^2 ≤ 3*(a^4+b^4+c^4) := by
    nlinarith [sq_nonneg (a^2-b^2), sq_nonneg (a^2-c^2), sq_nonneg (b^2-c^2)]
  nlinarith only [hh,ht]

/-- 原稿の線形成長条件から、実際の差分核の積空間L4を導く。 -/
theorem linear_growth_pair_fourth (d : ℕ)
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hx : MemLp (id : EuclideanSpace ℝ (Fin d) → _) 4 μ)
    (hy : MemLp (id : EuclideanSpace ℝ (Fin d) → _) 4 ν)
    (Rx Ry : ℝ) (hRx : (∫ x, ‖x‖^4 ∂μ) ≤ Rx) (hRy : (∫ y, ‖y‖^4 ∂ν) ≤ Ry)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : Measurable K)
    (G : ℝ) (hG : 0 ≤ G) (hKG : ∀ x, ‖K x‖ ≤ G*(1+‖x‖)) :
    Measurable (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => K (z.1-z.2)) ∧
    MemLp (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => K (z.1-z.2)) 4 (μ.prod ν) ∧
    (∫ z, ‖K (z.1-z.2)‖^4 ∂(μ.prod ν)) ≤ 27*G^4*(1+Rx+Ry) := by
  have hm := hK.comp (measurable_fst.sub measurable_snd)
  have hxi : Integrable (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => ‖z.1‖^4)
      (μ.prod ν) := (hx.integrable_norm_pow (p := 4) (by decide)).comp_fst ν
  have hyi : Integrable (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => ‖z.2‖^4)
      (μ.prod ν) := (hy.integrable_norm_pow (p := 4) (by decide)).comp_snd μ
  have hb (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
      ‖K (z.1-z.2)‖^4 ≤ 27*G^4*(1+‖z.1‖^4+‖z.2‖^4) := by
    have h : ‖K (z.1-z.2)‖ ≤ G*(1+‖z.1‖+‖z.2‖) := by
      apply (hKG _).trans
      apply mul_le_mul_of_nonneg_left _ hG
      linarith [norm_sub_le z.1 z.2]
    have h4 := pow_le_pow_left₀ (norm_nonneg _) h 4
    have ht := mul_le_mul_of_nonneg_left (fourth_three_bound 1 ‖z.1‖ ‖z.2‖)
      (by positivity : 0 ≤ G^4)
    nlinarith only [h4, ht]
  have henv : Integrable (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      27*G^4*(1+‖z.1‖^4+‖z.2‖^4)) (μ.prod ν) :=
    (((integrable_const 1).add hxi).add hyi).const_mul _
  have hi : Integrable (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ‖K (z.1-z.2)‖^4) (μ.prod ν) := by
    apply henv.mono' (hm.aestronglyMeasurable.norm.pow 4)
    exact ae_of_all _ (fun z => by
      change ‖‖K (z.1-z.2)‖^4‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖K (z.1-z.2)‖^4)]
      exact hb z)
  refine ⟨hm, l4_of_integrable_norm_fourth _ hm.aestronglyMeasurable hi, ?_⟩
  calc
    _ ≤ ∫ z, 27*G^4*(1+‖z.1‖^4+‖z.2‖^4) ∂(μ.prod ν) := integral_mono hi henv hb
    _ = 27*G^4*(1+(∫ x, ‖x‖^4 ∂μ)+(∫ y, ‖y‖^4 ∂ν)) := by
      rw [integral_const_mul,
        integral_add (f := fun z => 1+‖z.1‖^4) ((integrable_const 1).add hxi) hyi,
        integral_add (integrable_const 1) hxi, integral_fun_fst (fun x => ‖x‖^4),
        integral_fun_snd (fun y => ‖y‖^4)]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- 全域Lipschitzから線形成長。K(0)=0を要求しない。 -/
theorem lipschitz_growth_with_origin (d : ℕ) {L : ℝ≥0}
    {K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hK : LipschitzWith L K)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖K x‖ ≤ (‖K 0‖+(L : ℝ))*(1+‖x‖) := by
  have h := hK.norm_sub_le x 0
  have ht := norm_add_le (K x-K 0) (K 0)
  simp only [sub_add_cancel, sub_zero] at h ht
  nlinarith [mul_nonneg (norm_nonneg (K 0)) (norm_nonneg x), L.coe_nonneg]

/-- 母集団法則と空間次元を固定し、定数をNより先に選ぶ。
    各Nについて、タグ粒子とN-1個の独立コピーを積空間上に実際に構成する。
    これは既存の相互作用粒子の独立性を主張する定理ではない。 -/
theorem lipschitz_fluctuation_uniform_fourth (d : ℕ)
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ρ]
    (hρ : MemLp (id : EuclideanSpace ℝ (Fin d) → _) 4 ρ)
    (R : ℝ) (hR : (∫ x, ‖x‖^4 ∂ρ) ≤ R)
    {L : ℝ≥0} (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : LipschitzWith L K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N →
      let P := ρ.prod (Measure.pi (fun _ : Fin (N-1) => ρ))
      let F := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => K (z.1-z.2)
      MemLp (vectorKernelFluctuation (I := Fin (N-1)) d N ρ F) 4 P ∧
      (∫ z, ‖vectorKernelFluctuation (I := Fin (N-1)) d N ρ F z‖^4 ∂P) ≤ C/(N : ℝ)^2 := by
  have hr : 0 ≤ R := (integral_nonneg (fun x : EuclideanSpace ℝ (Fin d) =>
    show 0 ≤ ‖x‖^4 from by positivity)).trans hR
  let G : ℝ := ‖K 0‖+(L : ℝ)
  let A : ℝ := 27*G^4*(1+R+R)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨hm,hp,hb⟩ := linear_growth_pair_fourth d ρ ρ hρ hρ R R hR hR K
    hK.continuous.measurable G hG (lipschitz_growth_with_origin d hK)
  refine ⟨392*(d : ℝ)^2*A, by positivity, ?_⟩
  intro N hN
  exact vector_kernel_fluctuation_fourth_bound ρ ρ d N
    (by simp only [Fintype.card_fin]; omega)
    (fun z => K (z.1-z.2)) hm hp A hA hb

end WMFKIIndependentFourth
