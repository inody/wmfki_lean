import WMFKI_Stochastic.DiscreteWeakResidual
import Lean_Code.MatrixBridge

open MeasureTheory Set
open scoped BigOperators
namespace WMFKIExternalProbe

theorem three_vector_l2_moment {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Measure Ω)
    (f g h : Ω → E) (hf : MemLp f 2 P) (hg : MemLp g 2 P) (hh : MemLp h 2 P)
    (A B C : ℝ) (hA : (∫ ω, ‖f ω‖^2 ∂P) ≤ A) (hB : (∫ ω, ‖g ω‖^2 ∂P) ≤ B)
    (hC : (∫ ω, ‖h ω‖^2 ∂P) ≤ C) :
    MemLp (fun ω => f ω+g ω+h ω) 2 P ∧ (∫ ω, ‖f ω+g ω+h ω‖^2 ∂P) ≤ 3*(A+B+C) := by
  obtain ⟨hEnv,hEnvB⟩ := three_l2_moment (P := P) (fun ω => ‖f ω‖) (fun ω => ‖g ω‖) (fun ω => ‖h ω‖)
    hf.norm hg.norm hh.norm A B C hA hB hC
  have hR := (hf.add hg).add hh
  refine ⟨hR,?_⟩
  apply le_trans (integral_mono_ae hR.norm.integrable_sq hEnv.integrable_sq ?_) hEnvB
  apply ae_of_all
  intro ω
  change ‖f ω+g ω+h ω‖^2 ≤ (‖f ω‖+‖g ω‖+‖h ω‖)^2
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
  exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))

/-- The RMS Frobenius quadrature assumption controls the true coefficient
direction. L2 is explicit, so a default integral cannot certify the bound. -/
theorem matrix_quadrature_direction_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (L M : ℕ) (A : Ω → Matrix (Fin L) (Fin M) ℝ)
    (hA : MemLp (fun ω => (WithLp.toLp 2 (fun ij : Fin L × Fin M => A ω ij.1 ij.2) : EuclideanSpace ℝ (Fin L × Fin M))) 2 P)
    (Q : ℝ) (hQ : (∫ ω, (WMFKI.frobenius (A ω))^2 ∂P) ≤ Q)
    (θ : EuclideanSpace ℝ (Fin M)) :
    MemLp (fun ω => WMFKI.matrixMap (A ω) θ) 2 P ∧
      (∫ ω, ‖WMFKI.matrixMap (A ω) θ‖^2 ∂P) ≤ Q*‖θ‖^2 := by
  have hD : MemLp (fun ω => WMFKI.matrixMap (A ω) θ) 2 P := by
    apply MemLp.of_eval_piLp
    intro a
    change MemLp (fun ω => ∑ m, A ω a m*θ m) 2 P
    exact memLp_finsetSum Finset.univ (fun m _ => (hA.eval_piLp (a,m)).mul_const (θ m))
  have hFi : Integrable (fun ω => (WMFKI.frobenius (A ω))^2) P := by
    simpa only [WMFKI.frobenius_eq_vector_norm] using hA.norm.integrable_sq
  refine ⟨hD,?_⟩
  calc
    _ ≤ ∫ ω, (WMFKI.frobenius (A ω))^2*‖θ‖^2 ∂P := by
      apply integral_mono_ae hD.norm.integrable_sq (hFi.mul_const _)
      apply ae_of_all
      intro ω
      have h := (WMFKI.matrixMap (A ω)).le_opNorm θ |>.trans
        (mul_le_mul_of_nonneg_right (WMFKI.matrixMap_norm_le_frobenius _) (norm_nonneg _))
      have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr h
      simpa only [WMFKI.frobenius,mul_pow] using hh
    _ = (∫ ω, (WMFKI.frobenius (A ω))^2 ∂P)*‖θ‖^2 := integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hQ (sq_nonneg _)

/-- Composition of the two given RMS quadrature errors with the already
proved continuous residual. This does not claim a quadrature order from C1
regularity or prove the manuscript's assumed quadrature accuracy. -/
theorem quadrature_residual_moment {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Measure Ω)
    (r db dk : Ω → E) (hr : MemLp r 2 P) (hb : MemLp db 2 P) (hk : MemLp dk 2 P)
    (S Q α e : ℝ) (hS : (∫ ω, ‖r ω‖^2 ∂P) ≤ S)
    (hQb : (∫ ω, ‖db ω‖^2 ∂P) ≤ Q*e) (hQk : (∫ ω, ‖dk ω‖^2 ∂P) ≤ Q*α*e) :
    MemLp (fun ω => r ω+db ω-dk ω) 2 P ∧
      (∫ ω, ‖r ω+db ω-dk ω‖^2 ∂P) ≤ 2*S+4*Q*(1+α)*e := by
  have hkn : (∫ ω, ‖-dk ω‖^2 ∂P) ≤ Q*α*e := by simpa only [norm_neg] using hQk
  obtain ⟨hd,hdB⟩ := two_vector_l2_moment P db (fun ω => -dk ω) hb hk.neg _ _ hQb hkn
  obtain ⟨hR,hRB⟩ := two_vector_l2_moment P r _ hr hd S _ hS hdB
  refine ⟨?_,?_⟩
  · simpa only [sub_eq_add_neg,add_assoc] using hR
  · convert hRB using 1
    · simp only [sub_eq_add_neg,add_assoc]
    · ring

/-- Adds biased, correlated observation perturbations using the genuine
three-term inequality, rather than a false orthogonality assumption. -/
theorem observed_residual_error_composition {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Measure Ω)
    (r db dk eb ek : Ω → E) (hr : MemLp r 2 P) (hb : MemLp db 2 P) (hk : MemLp dk 2 P)
    (heb : MemLp eb 2 P) (hek : MemLp ek 2 P)
    (S Q α e Cb Ck q : ℝ) (hS : (∫ ω, ‖r ω‖^2 ∂P) ≤ S)
    (hQb : (∫ ω, ‖db ω‖^2 ∂P) ≤ Q*e) (hQk : (∫ ω, ‖dk ω‖^2 ∂P) ≤ Q*α*e)
    (hEb : (∫ ω, ‖eb ω‖^2 ∂P) ≤ Cb*q) (hEk : (∫ ω, ‖ek ω‖^2 ∂P) ≤ Ck*q) :
    MemLp (fun ω => (r ω+db ω-dk ω)+eb ω-ek ω) 2 P ∧
      (∫ ω, ‖(r ω+db ω-dk ω)+eb ω-ek ω‖^2 ∂P) ≤
        6*S+12*Q*(1+α)*e+3*(Cb+Ck)*q := by
  obtain ⟨hR,hRB⟩ := quadrature_residual_moment P r db dk hr hb hk S Q α e hS hQb hQk
  have hkn : (∫ ω, ‖-ek ω‖^2 ∂P) ≤ Ck*q := by simpa only [norm_neg] using hEk
  obtain ⟨hO,hOB⟩ := three_vector_l2_moment P _ eb (fun ω => -ek ω) hR heb hek.neg _ _ _ hRB hEb hkn
  refine ⟨?_,?_⟩
  · simpa only [sub_eq_add_neg] using hO
  · convert hOB using 1
    · simp only [sub_eq_add_neg]
    · ring

theorem three_scale_budget (Γ Q α Cb Ck Cε u e v : ℝ)
    (hu : 0 ≤ u) (he : 0 ≤ e) (hv : 0 ≤ v) :
    6*(Γ*u)+12*Q*(1+α)*e+3*(Cb+Ck)*(Cε*v) ≤
      (3*max (max (2*Γ) (4*Q*(1+α))) ((Cb+Ck)*Cε))*(u+e+v) := by
  let C := max (max (2*Γ) (4*Q*(1+α))) ((Cb+Ck)*Cε)
  have h1 : 2*Γ ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have h2 : 4*Q*(1+α) ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have h3 : (Cb+Ck)*Cε ≤ C := le_max_right _ _
  have h1' := mul_le_mul_of_nonneg_right h1 hu
  have h2' := mul_le_mul_of_nonneg_right h2 he
  have h3' := mul_le_mul_of_nonneg_right h3 hv
  change _ ≤ (3*C)*(u+e+v)
  nlinarith

end WMFKIExternalProbe
