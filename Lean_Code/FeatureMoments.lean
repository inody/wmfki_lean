import Lean_Code.PairAssembly

namespace WMFKI
open MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- 有界テスト勾配と線形成長する辞書原子の特徴は、位置の二乗だけで制御できる。 -/
theorem pairFeature_sq_bound (g Φ : F → F) (ψ B G K : ℝ)
    (hB : 0 ≤ B) (hG : 0 ≤ G) (hK : 0 ≤ K) (hψ : |ψ| ≤ B)
    (hg : ∀ x, ‖g x‖ ≤ G) (hΦ : ∀ z, ‖Φ z‖ ≤ K * (1 + ‖z‖)) (x y : F) :
    (ψ * inner ℝ (g x) (Φ (x - y))) ^ 2 ≤
      3 * (B * G * K) ^ 2 * (1 + ‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hz : ‖Φ (x - y)‖ ≤ K * (1 + ‖x‖ + ‖y‖) := by
    have hxy := norm_sub_le x y
    calc
      _ ≤ K * (1 + ‖x - y‖) := hΦ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hK
  have hb : |ψ * inner ℝ (g x) (Φ (x - y))| ≤
      (B * G * K) * (1 + ‖x‖ + ‖y‖) := by
    rw [abs_mul]
    calc
      _ ≤ B * (‖g x‖ * ‖Φ (x - y)‖) :=
        mul_le_mul hψ (abs_real_inner_le_norm _ _) (abs_nonneg _) hB
      _ ≤ B * (G * (K * (1 + ‖x‖ + ‖y‖))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (hg x) hz (norm_nonneg _) hG) hB
      _ = _ := by ring
  have hq : (1 + ‖x‖ + ‖y‖) ^ 2 ≤ 3 * (1 + ‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    nlinarith [sq_nonneg (‖x‖ - 1), sq_nonneg (‖y‖ - 1), sq_nonneg (‖x‖ - ‖y‖)]
  have hs := sq_le_sq₀ (abs_nonneg _) (by positivity :
    0 ≤ (B * G * K) * (1 + ‖x‖ + ‖y‖)) |>.mpr hb
  rw [sq_abs, mul_pow] at hs
  nlinarith [mul_le_mul_of_nonneg_left hq (sq_nonneg (B * G * K))]

/-- 特徴の可積分性と二乗平均を、二つの観測位置の二乗平均から供給する。 -/
theorem pairFeature_second_moment {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → F)
    (hX : Measurable X) (hY : Measurable Y)
    (hiX : Integrable (fun ω => ‖X ω‖ ^ 2) μ)
    (hiY : Integrable (fun ω => ‖Y ω‖ ^ 2) μ)
    (R : ℝ) (hRX : (∫ ω, ‖X ω‖ ^ 2 ∂μ) ≤ R) (hRY : (∫ ω, ‖Y ω‖ ^ 2 ∂μ) ≤ R)
    (g Φ : F → F) (hgm : Continuous g) (hΦm : Continuous Φ)
    (ψ B G K : ℝ) (hB : 0 ≤ B) (hG : 0 ≤ G) (hK : 0 ≤ K)
    (hψ : |ψ| ≤ B) (hg : ∀ x, ‖g x‖ ≤ G) (hΦ : ∀ z, ‖Φ z‖ ≤ K * (1 + ‖z‖)) :
    MemLp (fun ω => ψ * inner ℝ (g (X ω)) (Φ (X ω - Y ω))) 2 μ ∧
    (∫ ω, (ψ * inner ℝ (g (X ω)) (Φ (X ω - Y ω))) ^ 2 ∂μ) ≤
      3 * (B * G * K) ^ 2 * (1 + 2 * R) := by
  let c := 3 * (B * G * K) ^ 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hm : Measurable (fun ω => ψ * inner ℝ (g (X ω)) (Φ (X ω - Y ω))) := by
    fun_prop
  have hb := pairFeature_sq_bound g Φ ψ B G K hB hG hK hψ hg hΦ
  have hright : Integrable (fun ω => c * (1 + ‖X ω‖ ^ 2 + ‖Y ω‖ ^ 2)) μ :=
    (((integrable_const 1).add hiX).add hiY).const_mul c
  have hs : Integrable (fun ω => (ψ * inner ℝ (g (X ω)) (Φ (X ω - Y ω))) ^ 2) μ := by
    apply hright.mono' (hm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hb (X ω) (Y ω)
  constructor
  · exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hs
  · calc
      _ ≤ ∫ ω, c * (1 + ‖X ω‖ ^ 2 + ‖Y ω‖ ^ 2) ∂μ :=
        integral_mono hs hright (fun ω => hb (X ω) (Y ω))
      _ = c * (1 + (∫ ω, ‖X ω‖ ^ 2 ∂μ) + ∫ ω, ‖Y ω‖ ^ 2 ∂μ) := by
        have hx : Integrable (fun ω => (1 : ℝ) + ‖X ω‖ ^ 2) μ :=
          (integrable_const 1).add hiX
        rw [integral_const_mul, integral_add hx hiY,
          integral_add (integrable_const (1 : ℝ)) hiX]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hc

end WMFKI
