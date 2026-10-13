import WMFKI_Stochastic.DependentFourthProducts

open MeasureTheory Set
open WMFKIExternalProbe
namespace WMFKIFeatureCoupling
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

noncomputable def pairFeature (b : ℝ) (g K : E → E) (x y : E) : ℝ :=
  b*inner ℝ (g x) (K (x-y))

noncomputable def featureMomentFactor (G H C D R : ℝ) : ℝ :=
  6*(H*C)^2*(1+2*Real.sqrt R)+8*(G*D)^2

theorem feature_moment_factor_nonneg (G H C D R : ℝ) : 0 ≤ featureMomentFactor G H C D R := by
  unfold featureMomentFactor
  positivity

/-- 同期差と非線形コピーは依存する。独立性なしのL4積評価を使う。 -/
theorem coupled_pair_feature_moment (P : Measure Ω) [IsProbabilityMeasure P]
    (g K : E → E) (hgm : Measurable g) (hKm : Measurable K)
    (G H C D : ℝ) (hG : 0 ≤ G) (hH : 0 ≤ H) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hg : ∀ x, ‖g x‖ ≤ G) (hgl : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖)
    (hK : ∀ x, ‖K x‖ ≤ C*(1+‖x‖)) (hKl : ∀ x y, ‖K x-K y‖ ≤ D*‖x-y‖)
    (x y e f : Ω → E) (hxm : Measurable x) (hym : Measurable y) (hem : Measurable e) (hfm : Measurable f)
    (hx : MemLp x 4 P) (hy : MemLp y 4 P) (he : MemLp e 4 P) (hf : MemLp f 4 P)
    (q R : ℝ) (hq : 0 ≤ q)
    (hxR : (∫ ω, ‖x ω‖^4 ∂P) ≤ R) (hyR : (∫ ω, ‖y ω‖^4 ∂P) ≤ R)
    (heq : (∫ ω, ‖e ω‖^4 ∂P) ≤ q) (hfq : (∫ ω, ‖f ω‖^4 ∂P) ≤ q) :
    let F := fun ω => inner ℝ (g (x ω+e ω)) (K ((x ω+e ω)-(y ω+f ω)))-inner ℝ (g (x ω)) (K (x ω-y ω))
    MemLp F 2 P ∧ (∫ ω,(F ω)^2 ∂P) ≤ featureMomentFactor G H C D R*Real.sqrt q := by
  dsimp only
  obtain ⟨he2,heB⟩ := fourth_to_second P e he q hq heq
  obtain ⟨hf2,hfB⟩ := fourth_to_second P f hf q hq hfq
  obtain ⟨hexL,hexB⟩ := dependent_norm_product_l2 P e x he hx q R heq hxR
  obtain ⟨heyL,heyB⟩ := dependent_norm_product_l2 P e y he hy q R heq hyR
  obtain ⟨hu,huB⟩ := three_l2_moment (P := P) (fun ω => ‖e ω‖) (fun ω => ‖e ω‖*‖x ω‖)
    (fun ω => ‖e ω‖*‖y ω‖) he2.norm hexL heyL (Real.sqrt q) (Real.sqrt q*Real.sqrt R)
    (Real.sqrt q*Real.sqrt R) heB hexB heyB
  have hv := two_vector_l2_moment P (fun ω => ‖e ω‖) (fun ω => ‖f ω‖) he2.norm hf2.norm
    (Real.sqrt q) (Real.sqrt q)
    (by simpa only [Real.norm_eq_abs,abs_norm] using heB)
    (by simpa only [Real.norm_eq_abs,abs_norm] using hfB)
  have hvB : (∫ ω,(‖e ω‖+‖f ω‖)^2 ∂P) ≤ 2*(Real.sqrt q+Real.sqrt q) := by
    simpa only [Real.norm_eq_abs,sq_abs] using hv.2
  let U := fun ω => (H*C)*(‖e ω‖+‖e ω‖*‖x ω‖+‖e ω‖*‖y ω‖)
  let V := fun ω => (G*D)*(‖e ω‖+‖f ω‖)
  have hU : MemLp U 2 P := hu.const_mul _
  have hV : MemLp V 2 P := hv.1.const_mul _
  have hUB : (∫ ω, ‖U ω‖^2 ∂P) ≤ (H*C)^2*(3*(Real.sqrt q+Real.sqrt q*Real.sqrt R+Real.sqrt q*Real.sqrt R)) := by
    simp only [U,Real.norm_eq_abs,sq_abs,mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left huB (by positivity)
  have hVB : (∫ ω, ‖V ω‖^2 ∂P) ≤ (G*D)^2*(2*(Real.sqrt q+Real.sqrt q)) := by
    simp only [V,Real.norm_eq_abs,sq_abs,mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hvB (by positivity)
  obtain ⟨hUV,hUVB⟩ := two_vector_l2_moment P U V hU hV _ _ hUB hVB
  have hEnv : (∫ ω,(U ω+V ω)^2 ∂P) ≤ featureMomentFactor G H C D R*Real.sqrt q := by
    simp only [Real.norm_eq_abs,sq_abs] at hUVB
    convert hUVB using 1
    unfold featureMomentFactor
    ring
  apply real_l2_domination P _ (fun ω => U ω+V ω) _ hUV _ _ hEnv
  · exact ((hgm.comp (hxm.add hem)).inner (hKm.comp ((hxm.add hem).sub (hym.add hfm)))).sub
      ((hgm.comp hxm).inner (hKm.comp (hxm.sub hym)))
  · intro ω
    exact observed_pair_feature_difference_bound g K G H C D hG hH hC hD hg hgl hK hKl _ _ _ _

/-- 時間試験値bを含む実際の特徴差。Bはその絶対値の上界。 -/
theorem weighted_coupled_feature_moment (P : Measure Ω) [IsProbabilityMeasure P]
    (b B : ℝ) (hb : |b| ≤ B) (g K : E → E) (hgm : Measurable g) (hKm : Measurable K)
    (G H C D : ℝ) (hG : 0 ≤ G) (hH : 0 ≤ H) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hg : ∀ x, ‖g x‖ ≤ G) (hgl : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖)
    (hK : ∀ x, ‖K x‖ ≤ C*(1+‖x‖)) (hKl : ∀ x y, ‖K x-K y‖ ≤ D*‖x-y‖)
    (x y e f : Ω → E) (hxm : Measurable x) (hym : Measurable y) (hem : Measurable e) (hfm : Measurable f)
    (hx : MemLp x 4 P) (hy : MemLp y 4 P) (he : MemLp e 4 P) (hf : MemLp f 4 P)
    (q R : ℝ) (hq : 0 ≤ q)
    (hxR : (∫ ω, ‖x ω‖^4 ∂P) ≤ R) (hyR : (∫ ω, ‖y ω‖^4 ∂P) ≤ R)
    (heq : (∫ ω, ‖e ω‖^4 ∂P) ≤ q) (hfq : (∫ ω, ‖f ω‖^4 ∂P) ≤ q) :
    let F := fun ω => pairFeature b g K (x ω+e ω) (y ω+f ω)-pairFeature b g K (x ω) (y ω)
    MemLp F 2 P ∧ (∫ ω,(F ω)^2 ∂P) ≤ B^2*featureMomentFactor G H C D R*Real.sqrt q := by
  obtain ⟨hL,hBound⟩ := coupled_pair_feature_moment P g K hgm hKm G H C D hG hH hC hD
    hg hgl hK hKl x y e f hxm hym hem hfm hx hy he hf q R hq hxR hyR heq hfq
  have hEq : (fun ω => pairFeature b g K (x ω+e ω) (y ω+f ω)-pairFeature b g K (x ω) (y ω)) =
      fun ω => b*(inner ℝ (g (x ω+e ω)) (K ((x ω+e ω)-(y ω+f ω)))-inner ℝ (g (x ω)) (K (x ω-y ω))) := by
    funext ω
    unfold pairFeature
    ring
  rw [hEq]
  refine ⟨hL.const_mul b,?_⟩
  simp_rw [mul_pow]
  rw [integral_const_mul]
  have hb2 : b^2 ≤ B^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg b) hb 2
  calc
    _ ≤ b^2*(featureMomentFactor G H C D R*Real.sqrt q) := mul_le_mul_of_nonneg_left hBound (sq_nonneg b)
    _ ≤ B^2*(featureMomentFactor G H C D R*Real.sqrt q) :=
      mul_le_mul_of_nonneg_right hb2 (mul_nonneg (feature_moment_factor_nonneg _ _ _ _ _) (Real.sqrt_nonneg _))
    _ = _ := by ring

end WMFKIFeatureCoupling
