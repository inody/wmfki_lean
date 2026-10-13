import WMFKI_Stochastic.ArrayProductRealization

open MeasureTheory ProbabilityTheory Set
open WMFKIMeanFieldCopies WMFKIMeanFieldAdapted
open scoped NNReal
namespace WMFKISynchronousModel
variable {A Ω E : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

def arrayCopy {I : Type*} (Y : ℝ → A × Ω → E) (i : I) (t : ℝ) (z : (I → A) × (I → Ω)) : E :=
  Y t (z.1 i,z.2 i)

/-- 同じ初期配列とBrownian配列を使うコピーの出力証明書。 -/
structure ArrayNonlinearFamily (π : Measure A) (P : Measure Ω) (T : ℝ) (K : E → E)
    (ξ : A → E) (D Y : ℝ → A × Ω → E) (C : ℝ) : Prop where
  base_paths : FiniteL4Paths (π.prod P) T Y
  nonneg : 0 ≤ C
  paths : ∀ N : ℕ, ∀ i : Fin N, FiniteL4Paths (arrayMeasure π P (Fin N)) T (arrayCopy Y i)
  joint : ∀ N : ℕ, ∀ i : Fin N,
    StronglyMeasurable (fun z : ℝ × ((Fin N → A) × (Fin N → Ω)) => arrayCopy Y i z.1 z.2)
  independent : ∀ N : ℕ,
    iIndepFun (fun i : Fin N => finiteTrajectory T (arrayCopy Y i)) (arrayMeasure π P (Fin N))
  law : ∀ N : ℕ, ∀ i : Fin N, ∀ t ∈ Icc 0 T,
    HasLaw (arrayCopy Y i t) ((π.prod P).map (Y t)) (arrayMeasure π P (Fin N))
  fourth : ∀ N : ℕ, ∀ i : Fin N, ∀ t ∈ Icc 0 T,
    MemLp (arrayCopy Y i t) 4 (arrayMeasure π P (Fin N)) ∧
      (∫ z, ‖arrayCopy Y i t z‖^4 ∂arrayMeasure π P (Fin N)) ≤ C
  equation : ∀ N : ℕ, ∀ᵐ z ∂arrayMeasure π P (Fin N), ∀ i : Fin N,
    arrayCopy Y i 0 z = ξ (z.1 i) ∧ ∀ t ∈ Icc 0 T,
      arrayCopy Y i t z = ξ (z.1 i) +
        (∫ s in (0 : ℝ)..t, ∫ y, K (arrayCopy Y i s z-y) ∂((π.prod P).map (Y s))) + D t (z.1 i,z.2 i)

omit [SecondCountableTopology E] in
/-- 初期配列と雑音配列への移し替えでは同じN一様定数を保つ。 -/
theorem array_family_pullback (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P]
    {F : ℝ → MeasurableSpace (A × Ω)} {T C : ℝ} {K : E → E} {ξ : A → E}
    {D Y : ℝ → A × Ω → E}
    (h : IIDNonlinearFamily (π.prod P) F T K (fun z => ξ z.1) D Y C) :
    ArrayNonlinearFamily π P T K ξ D Y C := by
  refine ⟨h.base_paths,h.nonneg,?_,?_,?_,?_,?_,?_⟩
  · intro N i
    exact finite_l4_paths_pullback (join_arrays_preserving π P) (h.paths N i)
  · intro N i
    exact (h.joint N i).comp_measurable
      (measurable_fst.prodMk ((join_arrays_preserving π P).measurable.comp measurable_snd))
  · intro N
    exact independent_family_pullback (join_arrays_preserving π P)
      (fun i : Fin N => finiteTrajectory T (copyProcess Y i))
      (fun i => finite_trajectory_measurable (h.paths N i)) (h.independent N)
  · intro N i t ht
    exact (h.law N i t ht).comp (join_arrays_preserving π P).hasLaw
  · intro N i t ht
    refine ⟨((h.fourth N i t ht).1).comp_measurePreserving (join_arrays_preserving π P),?_⟩
    have he : (∫ z, ‖arrayCopy Y i t z‖^4 ∂arrayMeasure π P (Fin N)) =
        ∫ ω, ‖copyProcess Y i t ω‖^4 ∂Measure.pi (fun _ : Fin N => π.prod P) :=
      (join_arrays_preserving π P).hasLaw.integral_comp
        (((h.paths N i).measurable t ht).norm.pow_const 4).aestronglyMeasurable
    rw [he]
    exact (h.fourth N i t ht).2
  · intro N
    exact (join_arrays_preserving π P).quasiMeasurePreserving.ae (h.equation N)

/-- 母集団ドリフトの時間積分が本当に可積分であることをコピーに移す。 -/
theorem array_population_drift_integrable (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P] {T : ℝ} (hT : 0 ≤ T)
    {L : ℝ≥0} {K : E → E} (hK : LipschitzWith L K) {Y : ℝ → A × Ω → E}
    (hY : FiniteL4Paths (π.prod P) T Y) (N : ℕ) :
    ∀ᵐ z ∂arrayMeasure π P (Fin N), ∀ i : Fin N,
      IntervalIntegrable (fun s => ∫ y, K (arrayCopy Y i s z-y) ∂((π.prod P).map (Y s))) volume 0 T := by
  apply ae_all_iff.mpr
  intro i
  have hi := (joined_coordinate_preserving π P i).quasiMeasurePreserving.ae
    (hY.drift_integrable hT hK).2
  filter_upwards [hi] with z hz
  apply hz.congr
  intro s hs
  have hs' : s ∈ Ioc (0 : ℝ) T := by simpa only [uIoc_of_le hT] using hs
  exact WMFKIMeanFieldPicard.law_drift_map hK (hY.measurable s ⟨hs'.1.le,hs'.2⟩) _

end WMFKISynchronousModel
