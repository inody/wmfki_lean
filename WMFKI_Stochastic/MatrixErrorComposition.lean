import WMFKI_Stochastic.IIDTimeDesignRate

open MeasureTheory
open WMFKIExternalProbe
namespace WMFKIPopulationDesign

/-- 行列誤差をEuclidean成分ベクトルとして合成する。行・列・両誤差の独立性は不要。 -/
theorem matrix_error_composition {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (nr nc : ℕ)
    (A B C : Ω → Matrix (Fin nr) (Fin nc) ℝ)
    (hAB : MemLp (fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => (A ω-B ω) am.1 am.2) :
      EuclideanSpace ℝ (Fin nr × Fin nc))) 2 P)
    (hBC : MemLp (fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => (B ω-C ω) am.1 am.2) :
      EuclideanSpace ℝ (Fin nr × Fin nc))) 2 P)
    (U V : ℝ) (hu : (∫ ω, WMFKI.frobenius (A ω-B ω)^2 ∂P) ≤ U)
    (hv : (∫ ω, WMFKI.frobenius (B ω-C ω)^2 ∂P) ≤ V) :
    MemLp (fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => (A ω-C ω) am.1 am.2) :
      EuclideanSpace ℝ (Fin nr × Fin nc))) 2 P ∧
    (∫ ω, WMFKI.frobenius (A ω-C ω)^2 ∂P) ≤ 2*(U+V) := by
  let f := fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => (A ω-B ω) am.1 am.2) : EuclideanSpace ℝ (Fin nr × Fin nc))
  let g := fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => (B ω-C ω) am.1 am.2) : EuclideanSpace ℝ (Fin nr × Fin nc))
  let h := fun ω => (WithLp.toLp 2 (fun am : Fin nr × Fin nc => (A ω-C ω) am.1 am.2) : EuclideanSpace ℝ (Fin nr × Fin nc))
  have he ω : f ω+g ω = h ω := by
    ext am
    change (A ω am.1 am.2-B ω am.1 am.2)+(B ω am.1 am.2-C ω am.1 am.2) = A ω am.1 am.2-C ω am.1 am.2
    ring
  have he' : (fun ω => f ω+g ω) = h := funext he
  have hu' : (∫ ω, ‖f ω‖^2 ∂P) ≤ U := by simpa only [WMFKI.frobenius_eq_vector_norm] using hu
  have hv' : (∫ ω, ‖g ω‖^2 ∂P) ≤ V := by simpa only [WMFKI.frobenius_eq_vector_norm] using hv
  have hh := two_vector_l2_moment P f g hAB hBC U V hu' hv'
  simpa only [he',he,WMFKI.frobenius_eq_vector_norm] using hh

end WMFKIPopulationDesign
