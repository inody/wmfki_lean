import WMFKI_Stochastic.ObservedDictionaryMoment

open MeasureTheory
open WMFKIExternalProbe WMFKIFeatureCoupling
namespace WMFKIObservedDesign

/-- 三つの依存しうる行列誤差を、可積分性を保持して合成する。 -/
theorem three_matrix_errors {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (nr nc : ℕ)
    (A B C D : Ω → Matrix (Fin nr) (Fin nc) ℝ)
    (hAB : MemLp (fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => (A ω-B ω) am.1 am.2) :
      EuclideanSpace ℝ (Fin nr × Fin nc))) 2 P)
    (hBC : MemLp (fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => (B ω-C ω) am.1 am.2) :
      EuclideanSpace ℝ (Fin nr × Fin nc))) 2 P)
    (hCD : MemLp (fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => (C ω-D ω) am.1 am.2) :
      EuclideanSpace ℝ (Fin nr × Fin nc))) 2 P)
    (U V W : ℝ) (hu : (∫ ω, WMFKI.frobenius (A ω-B ω)^2 ∂P) ≤ U)
    (hv : (∫ ω, WMFKI.frobenius (B ω-C ω)^2 ∂P) ≤ V)
    (hw : (∫ ω, WMFKI.frobenius (C ω-D ω)^2 ∂P) ≤ W) :
    MemLp (fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => (A ω-D ω) am.1 am.2) :
      EuclideanSpace ℝ (Fin nr × Fin nc))) 2 P ∧
    (∫ ω, WMFKI.frobenius (A ω-D ω)^2 ∂P) ≤ 3*(U+V+W) := by
  let f := fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => (A ω-B ω) am.1 am.2) : EuclideanSpace ℝ (Fin nr × Fin nc))
  let g := fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => (B ω-C ω) am.1 am.2) : EuclideanSpace ℝ (Fin nr × Fin nc))
  let h := fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => (C ω-D ω) am.1 am.2) : EuclideanSpace ℝ (Fin nr × Fin nc))
  let k := fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => (A ω-D ω) am.1 am.2) : EuclideanSpace ℝ (Fin nr × Fin nc))
  have he ω : f ω+g ω+h ω = k ω := by
    ext am
    change (A ω am.1 am.2-B ω am.1 am.2)+(B ω am.1 am.2-C ω am.1 am.2)+(C ω am.1 am.2-D ω am.1 am.2) = A ω am.1 am.2-D ω am.1 am.2
    ring
  have he' : (fun ω => f ω+g ω+h ω) = k := funext he
  have hu' : (∫ ω, ‖f ω‖^2 ∂P) ≤ U := by simpa only [WMFKI.frobenius_eq_vector_norm] using hu
  have hv' : (∫ ω, ‖g ω‖^2 ∂P) ≤ V := by simpa only [WMFKI.frobenius_eq_vector_norm] using hv
  have hw' : (∫ ω, ‖h ω‖^2 ∂P) ≤ W := by simpa only [WMFKI.frobenius_eq_vector_norm] using hw
  have hl := (hAB.add hBC).add hCD
  change MemLp (fun ω => f ω+g ω+h ω) 2 P at hl
  have hb := three_l2_moment (P := P) (fun ω => ‖f ω‖) (fun ω => ‖g ω‖) (fun ω => ‖h ω‖)
    hAB.norm hBC.norm hCD.norm U V W hu' hv' hw'
  have hm : (∫ ω, ‖f ω+g ω+h ω‖^2 ∂P) ≤ 3*(U+V+W) := by
    apply (integral_mono hl.norm.integrable_sq hb.1.integrable_sq ?_).trans hb.2
    intro ω
    have ht : ‖f ω+g ω+h ω‖ ≤ ‖f ω‖+‖g ω‖+‖h ω‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    exact pow_le_pow_left₀ (norm_nonneg _) ht 2
  refine ⟨by simpa only [he'] using hl,?_⟩
  simpa only [he,WMFKI.frobenius_eq_vector_norm] using hm

/-- 同期L4率からNに依存しない位置のL2定数を取り出す。 -/
theorem coupled_uniform_position_second {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ) (hN : 0 < N) (x y : Ω → E) (hy : MemLp y 4 P)
    (he : MemLp (fun ω => x ω-y ω) 4 P) (R S : ℝ) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hyR : (∫ ω, ‖y ω‖^4 ∂P) ≤ R) (heS : (∫ ω, ‖x ω-y ω‖^4 ∂P) ≤ S/(N : ℝ)^2) :
    MemLp x 2 P ∧ (∫ ω, ‖x ω‖^2 ∂P) ≤ 2*(Real.sqrt R+Real.sqrt S) := by
  obtain ⟨hl,hb⟩ := coupled_position_second P x y hy he R (S/(N : ℝ)^2) hR (by positivity) hyR heS
  refine ⟨hl,hb.trans ?_⟩
  rw [sqrt_fourth_rate S hS N]
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd := div_le_self (Real.sqrt_nonneg S) hn
  linarith

end WMFKIObservedDesign
