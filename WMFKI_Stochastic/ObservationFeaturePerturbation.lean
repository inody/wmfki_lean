import WMFKI_Stochastic.StableMomentAlgebra
import WMFKI_Stochastic.ParticleEnvelopeMoments
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace WMFKIExternalProbe

section Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem observed_pair_feature_difference_bound
    (g K : E → E) (G H C D : ℝ) (hG : 0 ≤ G) (hH : 0 ≤ H) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hg : ∀ x, ‖g x‖ ≤ G) (hgl : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖)
    (hK : ∀ x, ‖K x‖ ≤ C*(1+‖x‖)) (hKl : ∀ x y, ‖K x-K y‖ ≤ D*‖x-y‖)
    (x y e f : E) :
    |inner ℝ (g (x+e)) (K ((x+e)-(y+f)))-inner ℝ (g x) (K (x-y))| ≤
      (H*C)*(‖e‖+‖e‖*‖x‖+‖e‖*‖y‖)+(G*D)*(‖e‖+‖f‖) := by
  have hsplit : inner ℝ (g (x+e)) (K ((x+e)-(y+f)))-inner ℝ (g x) (K (x-y)) =
      inner ℝ (g (x+e)-g x) (K (x-y))+
      inner ℝ (g (x+e)) (K ((x+e)-(y+f))-K (x-y)) := by
    rw [inner_sub_left,inner_sub_right]
    ring
  have hgd : ‖g (x+e)-g x‖ ≤ H*‖e‖ := by simpa using hgl (x+e) x
  have hkg : ‖K (x-y)‖ ≤ C*(1+‖x‖+‖y‖) := (hK _).trans
    (mul_le_mul_of_nonneg_left (by linarith [norm_sub_le x y]) hC)
  have hkd : ‖K ((x+e)-(y+f))-K (x-y)‖ ≤ D*(‖e‖+‖f‖) := by
    apply (hKl _ _).trans
    have hh : ((x+e)-(y+f))-(x-y) = e-f := by abel
    rw [hh]
    exact mul_le_mul_of_nonneg_left (norm_sub_le e f) hD
  rw [hsplit]
  calc
    _ ≤ |inner ℝ (g (x+e)-g x) (K (x-y))|+
        |inner ℝ (g (x+e)) (K ((x+e)-(y+f))-K (x-y))| := abs_add_le _ _
    _ ≤ (H*‖e‖)*(C*(1+‖x‖+‖y‖))+G*(D*(‖e‖+‖f‖)) := add_le_add
      ((abs_real_inner_le_norm _ _).trans (mul_le_mul hgd hkg (norm_nonneg _) (mul_nonneg hH (norm_nonneg _))))
      ((abs_real_inner_le_norm _ _).trans (mul_le_mul (hg _) hkd (norm_nonneg _) hG))
    _ = _ := by ring
end Geometry

section Moments
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
theorem independent_norm_product_l2 (P : Measure Ω) [IsProbabilityMeasure P]
    (e x : Ω → E) (he : MemLp e 2 P) (hx : MemLp x 2 P)
    (hind : IndepFun e x P) (q R : ℝ) (hq : 0 ≤ q)
    (heq : (∫ ω, ‖e ω‖^2 ∂P) ≤ q) (hxR : (∫ ω, ‖x ω‖^2 ∂P) ≤ R) :
    MemLp (fun ω => ‖e ω‖*‖x ω‖) 2 P ∧ (∫ ω, (‖e ω‖*‖x ω‖)^2 ∂P) ≤ q*R := by
  have hind2 : IndepFun (fun ω => ‖e ω‖^2) (fun ω => ‖x ω‖^2) P :=
    hind.comp (measurable_norm.pow_const 2) (measurable_norm.pow_const 2)
  have hi := hind2.integrable_mul he.norm.integrable_sq hx.norm.integrable_sq
  have hL : MemLp (fun ω => ‖e ω‖*‖x ω‖) 2 P :=
    (memLp_two_iff_integrable_sq (he.norm.aestronglyMeasurable.mul hx.norm.aestronglyMeasurable)).mpr
      (by simpa only [mul_pow,Pi.mul_def] using hi)
  refine ⟨hL,?_⟩
  calc
    _ = (∫ ω, ‖e ω‖^2 ∂P)*(∫ ω, ‖x ω‖^2 ∂P) := by
      simp_rw [mul_pow]
      exact hind2.integral_fun_mul_eq_mul_integral he.norm.integrable_sq.aestronglyMeasurable hx.norm.integrable_sq.aestronglyMeasurable
    _ ≤ q*R := mul_le_mul heq hxR (integral_nonneg (fun _ => sq_nonneg _)) hq

/-- Only noise/latent independence is used. No independence is required
between the two particles or between the two observation errors. -/
theorem observed_pair_feature_difference_moment (P : Measure Ω) [IsProbabilityMeasure P]
    (g K : E → E) (hgm : Measurable g) (hKm : Measurable K)
    (G H C D : ℝ) (hG : 0 ≤ G) (hH : 0 ≤ H) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hg : ∀ x, ‖g x‖ ≤ G) (hgl : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖)
    (hK : ∀ x, ‖K x‖ ≤ C*(1+‖x‖)) (hKl : ∀ x y, ‖K x-K y‖ ≤ D*‖x-y‖)
    (x y e f : Ω → E) (hxm : Measurable x) (hym : Measurable y) (hem : Measurable e) (hfm : Measurable f)
    (hx : MemLp x 2 P) (hy : MemLp y 2 P) (he : MemLp e 2 P) (hf : MemLp f 2 P)
    (hex : IndepFun e x P) (hey : IndepFun e y P)
    (q R : ℝ) (hq : 0 ≤ q)
    (hxR : (∫ ω, ‖x ω‖^2 ∂P) ≤ R) (hyR : (∫ ω, ‖y ω‖^2 ∂P) ≤ R)
    (heq : (∫ ω, ‖e ω‖^2 ∂P) ≤ q) (hfq : (∫ ω, ‖f ω‖^2 ∂P) ≤ q) :
    let F := fun ω => inner ℝ (g (x ω+e ω)) (K ((x ω+e ω)-(y ω+f ω)))-inner ℝ (g (x ω)) (K (x ω-y ω))
    MemLp F 2 P ∧ (∫ ω,(F ω)^2 ∂P) ≤ (6*(H*C)^2*(1+2*R)+8*(G*D)^2)*q := by
  dsimp only
  obtain ⟨hexL,hexB⟩ := independent_norm_product_l2 P e x he hx hex q R hq heq hxR
  obtain ⟨heyL,heyB⟩ := independent_norm_product_l2 P e y he hy hey q R hq heq hyR
  obtain ⟨hu,huB⟩ := three_l2_moment (P := P) (fun ω => ‖e ω‖) (fun ω => ‖e ω‖*‖x ω‖)
    (fun ω => ‖e ω‖*‖y ω‖) he.norm hexL heyL q (q*R) (q*R) heq hexB heyB
  have hv := two_vector_l2_moment P (fun ω => ‖e ω‖) (fun ω => ‖f ω‖) he.norm hf.norm q q
    (by simpa only [Real.norm_eq_abs,abs_norm] using heq) (by simpa only [Real.norm_eq_abs,abs_norm] using hfq)
  have hvB : (∫ ω,(‖e ω‖+‖f ω‖)^2 ∂P) ≤ 2*(q+q) := by
    simpa only [Real.norm_eq_abs,sq_abs] using hv.2
  let U := fun ω => (H*C)*(‖e ω‖+‖e ω‖*‖x ω‖+‖e ω‖*‖y ω‖)
  let V := fun ω => (G*D)*(‖e ω‖+‖f ω‖)
  have hU : MemLp U 2 P := hu.const_mul _
  have hV : MemLp V 2 P := hv.1.const_mul _
  have hUB : (∫ ω, ‖U ω‖^2 ∂P) ≤ (H*C)^2*(3*(q+q*R+q*R)) := by
    simp only [U,Real.norm_eq_abs,sq_abs,mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left huB (by positivity)
  have hVB : (∫ ω, ‖V ω‖^2 ∂P) ≤ (G*D)^2*(2*(q+q)) := by
    simp only [V,Real.norm_eq_abs,sq_abs,mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hvB (by positivity)
  obtain ⟨hUV,hUVB⟩ := two_vector_l2_moment P U V hU hV _ _ hUB hVB
  have hEnv : (∫ ω,(U ω+V ω)^2 ∂P) ≤ (6*(H*C)^2*(1+2*R)+8*(G*D)^2)*q := by
    simp only [Real.norm_eq_abs,sq_abs] at hUVB
    convert hUVB using 1
    ring
  apply real_l2_domination P _ (fun ω => U ω+V ω) _ hUV _ _ hEnv
  · exact ((hgm.comp (hxm.add hem)).inner (hKm.comp ((hxm.add hem).sub (hym.add hfm)))).sub
      ((hgm.comp hxm).inner (hKm.comp (hxm.sub hym)))
  · intro ω
    exact observed_pair_feature_difference_bound g K G H C D hG hH hC hD hg hgl hK hKl _ _ _ _
end Moments
end WMFKIExternalProbe
