import WMFKI_Stochastic.ObservationAveraging
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory Set
open scoped BigOperators
namespace WMFKIExternalProbe
-- Cache the standard operator-space instances to avoid a nested-instance
-- elaboration diamond. These are inferred Mathlib structures, not new norms.
private noncomputable local instance (d : ℕ) : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := inferInstance
private noncomputable local instance (d : ℕ) : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := inferInstance
private noncomputable local instance (d : ℕ) : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := inferInstance
private noncomputable local instance (d : ℕ) : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := inferInstance

theorem global_derivative_difference_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : Differentiable ℝ f) (C : ℝ) (hC : ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (x y : E) : ‖f x-f y‖ ≤ C*‖x-y‖ :=
  Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hf z) (fun z _ => hC z)
    convex_univ (mem_univ y) (mem_univ x)

/-- Bounded genuine first, second and third Frechet derivatives give the
three observation Lipschitz bounds. The Laplacian constant may depend on d,
but none of these constants depends on the particle count or time grid. -/
theorem observation_test_derivative_bounds (d : ℕ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : ContDiff ℝ 3 φ)
    (G H J : ℝ)
    (hG : ∀ x, ‖fderiv ℝ φ x‖ ≤ G)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ H)
    (hJ : ∀ x, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x‖ ≤ J) :
    (∀ x, ‖gradient φ x‖ ≤ G) ∧
    (∀ x y, |φ x-φ y| ≤ G*‖x-y‖) ∧
    (∀ x y, ‖gradient φ x-gradient φ y‖ ≤ H*‖x-y‖) ∧
    (∀ x y, |Laplacian.laplacian φ x-Laplacian.laplacian φ y| ≤ ((d : ℝ)*J)*‖x-y‖) := by
  have hd : ContDiff ℝ 2 (fderiv ℝ φ) := (contDiff_succ_iff_fderiv (n := 2)).mp hφ |>.2.2
  have hdd : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ φ)) := (contDiff_succ_iff_fderiv (n := 1)).mp hd |>.2.2
  refine ⟨?_,?_,?_,?_⟩
  · intro x
    change ‖(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ φ x)‖ ≤ G
    rw [LinearIsometryEquiv.norm_map]
    exact hG x
  · intro x y
    simpa only [Real.norm_eq_abs] using global_derivative_difference_bound φ
      (hφ.differentiable (by norm_num)) G hG x y
  · intro x y
    change ‖(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ φ x)-
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ φ y)‖ ≤ _
    rw [←map_sub,LinearIsometryEquiv.norm_map]
    exact global_derivative_difference_bound (fderiv ℝ φ) (hd.differentiable (by norm_num)) H hH x y
  · intro x y
    rw [euclidean_laplacian_trace,euclidean_laplacian_trace,←Finset.sum_sub_distrib]
    have hddB := global_derivative_difference_bound (fderiv ℝ (fderiv ℝ φ))
      (hdd.differentiable (by norm_num)) J hJ x y
    calc
      _ ≤ ∑ a, |fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single a 1) (EuclideanSpace.single a 1)-
        fderiv ℝ (fderiv ℝ φ) y (EuclideanSpace.single a 1) (EuclideanSpace.single a 1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin d, J*‖x-y‖ := by
        apply Finset.sum_le_sum
        intro a _
        have hh := (fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y).le_opNorm₂
          (EuclideanSpace.single a 1) (EuclideanSpace.single a 1)
        have hh' : |fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single a 1) (EuclideanSpace.single a 1)-
            fderiv ℝ (fderiv ℝ φ) y (EuclideanSpace.single a 1) (EuclideanSpace.single a 1)| ≤
            ‖fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y‖ := by
          simpa [sub_apply,Real.norm_eq_abs] using hh
        exact hh'.trans hddB
      _ = _ := by simp; ring

/-- Only genuine regularity and derivative bounds are stored, not observation-error conclusions. -/
structure C3TestBounds (d : ℕ) (φ : EuclideanSpace ℝ (Fin d) → ℝ) (G H J : ℝ) : Prop where
  smooth : ContDiff ℝ 3 φ
  first : ∀ x, ‖fderiv ℝ φ x‖ ≤ G
  second : ∀ x, ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ H
  third : ∀ x, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x‖ ≤ J

theorem C3TestBounds.observation_bounds {d : ℕ} {φ : EuclideanSpace ℝ (Fin d) → ℝ} {G H J : ℝ}
    (h : C3TestBounds d φ G H J) :
    (∀ x, ‖gradient φ x‖ ≤ G) ∧
    (∀ x y, |φ x-φ y| ≤ G*‖x-y‖) ∧
    (∀ x y, ‖gradient φ x-gradient φ y‖ ≤ H*‖x-y‖) ∧
    (∀ x y, |Laplacian.laplacian φ x-Laplacian.laplacian φ y| ≤ ((d : ℝ)*J)*‖x-y‖) :=
  observation_test_derivative_bounds d φ h.smooth G H J h.first h.second h.third

theorem constant_c3_test_bounds (d : ℕ) (c : ℝ) :
    C3TestBounds d (fun _ : EuclideanSpace ℝ (Fin d) => c) 0 0 0 := by
  constructor
  · exact contDiff_const
  · intro x; simp
  · intro x; simp
  · intro x; simp

end WMFKIExternalProbe
