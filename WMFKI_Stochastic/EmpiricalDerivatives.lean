import WMFKI_Stochastic.EmpiricalWeakBalance
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian

open MeasureTheory
open scoped BigOperators
namespace WMFKIExternalProbe

/-- Coordinate directions affect exactly one Euclidean particle block. -/
theorem particleProjection_single (N d : ℕ) (i j : Fin N) (a : Fin d) :
    particleProjection N d j (Pi.single (finProdFinEquiv (i,a)) 1) =
      if j=i then EuclideanSpace.single a 1 else 0 := by
  classical
  by_cases h : j=i
  · subst j
    ext b
    simp [particleProjection,particlePositions,EuclideanSpace.single,Pi.single_apply]
  · ext b
    simp [particleProjection,particlePositions,h]

theorem empirical_fderiv_apply (N d : ℕ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : Differentiable ℝ φ)
    (x v : Fin (N*d) → ℝ) :
    fderiv ℝ (empiricalObservable N d φ) x v =
      (N : ℝ)⁻¹ * ∑ i, fderiv ℝ φ (particlePositions N d x i) (particlePositions N d v i) := by
  have hD := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (hφ (particleProjection N d i x)).hasFDerivAt.comp x (particleProjection N d i).hasFDerivAt)
  have he := congrArg (fun L : (Fin (N*d) → ℝ) →L[ℝ] ℝ => L v)
    (hD.const_mul ((N : ℝ)⁻¹)).fderiv
  change fderiv ℝ (fun y => (N : ℝ)⁻¹ * ∑ i, φ (particlePositions N d y i)) x v = _
  simpa [particleProjection,Function.comp_def] using he

theorem empirical_fderiv_coordinate (N d : ℕ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : Differentiable ℝ φ)
    (x : Fin (N*d) → ℝ) (i : Fin N) (a : Fin d) :
    fderiv ℝ (empiricalObservable N d φ) x (Pi.single (finProdFinEquiv (i,a)) 1) =
      (N : ℝ)⁻¹ * fderiv ℝ φ (particlePositions N d x i) (EuclideanSpace.single a 1) := by
  classical
  rw [empirical_fderiv_apply N d φ hφ]
  change (N : ℝ)⁻¹ * ∑ j, fderiv ℝ φ (particlePositions N d x j)
    (particleProjection N d j (Pi.single (finProdFinEquiv (i,a)) 1)) = _
  simp_rw [particleProjection_single,apply_ite,map_zero]
  simp

/-- Differentiating a derivative evaluated at a fixed direction really yields
its Hessian; no independent Hessian symbol is postulated. -/
theorem fderiv_directional_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) (x u v : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x u = fderiv ℝ (fderiv ℝ f) x u v := by
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := (contDiff_succ_iff_fderiv (n := 1)).mp hf |>.2.2
  rw [fderiv_clm_apply (hf1.differentiable (by norm_num) x) (differentiableAt_const v)]
  simp

theorem empirical_hessian_diagonal (N d : ℕ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (x : Fin (N*d) → ℝ) (i : Fin N) (a : Fin d) :
    fderiv ℝ (fderiv ℝ (empiricalObservable N d φ)) x
      (Pi.single (finProdFinEquiv (i,a)) 1) (Pi.single (finProdFinEquiv (i,a)) 1) =
      (N : ℝ)⁻¹ * fderiv ℝ (fderiv ℝ φ) (particlePositions N d x i)
        (EuclideanSpace.single a 1) (EuclideanSpace.single a 1) := by
  let e : Fin (N*d) → ℝ := Pi.single (finProdFinEquiv (i,a)) 1
  let v := EuclideanSpace.single a (1 : ℝ)
  have hφ1 : ContDiff ℝ 1 (fderiv ℝ φ) := (contDiff_succ_iff_fderiv (n := 1)).mp hφ |>.2.2
  have hd : Differentiable ℝ (fun y => fderiv ℝ φ y v) :=
    hφ1.differentiable (by norm_num) |>.clm_apply (differentiable_const v)
  have he : (fun y => fderiv ℝ (empiricalObservable N d φ) y e) =
      (fun y => (N : ℝ)⁻¹ * fderiv ℝ φ (particleProjection N d i y) v) :=
    funext (fun y => empirical_fderiv_coordinate N d φ (hφ.differentiable (by norm_num)) y i a)
  rw [← fderiv_directional_apply _ (empiricalObservable_contDiff N d φ hφ) x e e, he]
  have hdc : DifferentiableAt ℝ (fun y => fderiv ℝ φ (particleProjection N d i y) v) x :=
    hd.comp (particleProjection N d i).differentiable x
  rw [fderiv_const_mul hdc]
  rw [fderiv_fun_comp x (hd _) (particleProjection N d i).differentiableAt]
  simp only [smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,ContinuousLinearMap.fderiv]
  rw [fderiv_directional_apply φ hφ]
  change (N : ℝ)⁻¹ * fderiv ℝ (fderiv ℝ φ) (particlePositions N d x i)
    (particleProjection N d i (Pi.single (finProdFinEquiv (i,a)) 1)) v = _
  rw [particleProjection_single]
  simp only [ite_true]
  rfl

end WMFKIExternalProbe
