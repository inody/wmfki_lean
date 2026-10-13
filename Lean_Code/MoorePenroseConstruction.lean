import Lean_Code.MoorePenrose
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

namespace WMFKI

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
  [FiniteDimensional ℝ E]

/-- 有限次元では擬似逆を実際に構成できる。全列階数は仮定しない。 -/
theorem exists_moorePenrose (B : E →L[ℝ] F) : ∃ P, IsMoorePenrose B P := by
  let K := B.ker
  let R := B.range
  obtain ⟨q, hq⟩ := B.toLinearMap.rangeRestrict.exists_rightInverse_of_surjective
    B.toLinearMap.range_rangeRestrict
  let C : F →L[ℝ] E := q.toContinuousLinearMap.comp R.orthogonalProjectionOnto
  have hBC (y : F) : B (C y) = R.starProjection y := by
    have h := congrArg (fun f => f (R.orthogonalProjectionOnto y)) hq
    exact congrArg (fun z : R => (z : F)) h
  let P : F →L[ℝ] E := Kᗮ.starProjection.comp C
  have hBP : B.comp P = R.starProjection := by
    ext y
    change B (Kᗮ.starProjection (C y)) = R.starProjection y
    rw [Submodule.starProjection_orthogonal_val, map_sub]
    have hz : B (K.starProjection (C y)) = 0 :=
      K.starProjection_apply_mem (C y)
    rw [hz, sub_zero, hBC]
  have hPB : P.comp B = Kᗮ.starProjection := by
    ext x
    change Kᗮ.starProjection (C (B x)) = Kᗮ.starProjection x
    have hmem : C (B x) - x ∈ K := by
      change B (C (B x) - x) = 0
      rw [map_sub, hBC]
      have hr : R.starProjection (B x) = B x :=
        Submodule.starProjection_eq_self_iff.mpr ⟨x, rfl⟩
      rw [hr, sub_self]
    have hz : Kᗮ.starProjection (C (B x) - x) = 0 := by
      rw [Submodule.starProjection_orthogonal_val,
        Submodule.starProjection_eq_self_iff.mpr hmem, sub_self]
    rw [map_sub] at hz
    exact sub_eq_zero.mp hz
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · rw [hBP]
    ext x
    exact Submodule.starProjection_eq_self_iff.mpr ⟨x, rfl⟩
  · rw [hPB]
    ext y
    exact Submodule.starProjection_eq_self_iff.mpr (Kᗮ.starProjection_apply_mem (C y))
  · rw [hBP]
    exact R.starProjection_isSymmetric.clm_adjoint_eq
  · rw [hPB]
    exact Kᗮ.starProjection_isSymmetric.clm_adjoint_eq

noncomputable def moorePenrose (B : E →L[ℝ] F) : F →L[ℝ] E :=
  Classical.choose (exists_moorePenrose B)

theorem moorePenrose_spec (B : E →L[ℝ] F) : IsMoorePenrose B (moorePenrose B) :=
  Classical.choose_spec (exists_moorePenrose B)

theorem moorePenrose_minimizes (B : E →L[ℝ] F) (y : F) :
    IsLeastSquares B y (moorePenrose B y) :=
  moorePenrose_isLeastSquares B (moorePenrose B) (moorePenrose_spec B) y

end WMFKI
