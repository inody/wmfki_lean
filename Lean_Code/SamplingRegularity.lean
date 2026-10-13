import Lean_Code.WeakPairMoments
import Lean_Code.MatrixMoments

namespace WMFKI
open MeasureTheory

/-- 有限行列からEuclidean作用素への変換の連続性。行列ノルムの同一視はしない。 -/
theorem continuous_matrixMap {L M : ℕ} :
    Continuous (matrixMap : Matrix (Fin L) (Fin M) ℝ →
      EuclideanSpace ℝ (Fin M) →L[ℝ] EuclideanSpace ℝ (Fin L)) := by
  let f : Matrix (Fin L) (Fin M) ℝ →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin M) →L[ℝ] EuclideanSpace ℝ (Fin L)) :=
    { toFun := matrixMap
      map_add' := by intro A B; ext u a; simp [matrixMap_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c A; ext u a; simp [matrixMap_apply, Finset.mul_sum, mul_assoc] }
  exact f.continuous_of_finiteDimensional

theorem frobenius_sq_sum {L M : ℕ} (A : Matrix (Fin L) (Fin M) ℝ) :
    frobenius A ^ 2 = ∑ a, ∑ m, A a m ^ 2 := by
  unfold frobenius
  exact Real.sq_sqrt (by positivity)

theorem finite_vector_norm_sq_regular {Ω : Type*} [MeasurableSpace Ω] {L : ℕ}
    (μ : Measure Ω) (r : Ω → Fin L → ℝ)
    (hm : ∀ a, Measurable (fun ω => r ω a)) (hh : ∀ a, MemLp (fun ω => r ω a) 2 μ) :
    Measurable (fun ω => ‖(WithLp.toLp 2 (r ω) : EuclideanSpace ℝ (Fin L))‖ ^ 2) ∧
    Integrable (fun ω => ‖(WithLp.toLp 2 (r ω) : EuclideanSpace ℝ (Fin L))‖ ^ 2) μ := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  exact ⟨by fun_prop, integrable_finsetSum _ (fun a _ => (hh a).integrable_sq)⟩

theorem frobenius_sq_regular {Ω : Type*} [MeasurableSpace Ω] {L M : ℕ}
    (μ : Measure Ω) (A : Ω → Matrix (Fin L) (Fin M) ℝ)
    (hm : ∀ a m, Measurable (fun ω => A ω a m))
    (hh : ∀ a m, MemLp (fun ω => A ω a m) 2 μ) :
    Measurable (fun ω => frobenius (A ω) ^ 2) ∧
    Integrable (fun ω => frobenius (A ω) ^ 2) μ := by
  simp_rw [frobenius_sq_sum]
  exact ⟨by fun_prop, integrable_finsetSum _ (fun a _ =>
    integrable_finsetSum _ (fun m _ => (hh a m).integrable_sq))⟩

/-- 成分の可測性・L2性から作用素ノルムの可測性・可積分性とFrobenius上界。 -/
theorem matrix_operator_moment_regular {Ω : Type*} [MeasurableSpace Ω] {L M : ℕ}
    (μ : Measure Ω) (A : Ω → Matrix (Fin L) (Fin M) ℝ)
    (hm : ∀ a m, Measurable (fun ω => A ω a m))
    (hh : ∀ a m, MemLp (fun ω => A ω a m) 2 μ) :
    Measurable (fun ω => ‖matrixMap (A ω)‖ ^ 2) ∧
    Integrable (fun ω => ‖matrixMap (A ω)‖ ^ 2) μ ∧
    (∫ ω, ‖matrixMap (A ω)‖ ^ 2 ∂μ) ≤ ∫ ω, frobenius (A ω) ^ 2 ∂μ := by
  let : MeasurableSpace (Matrix (Fin L) (Fin M) ℝ) :=
    inferInstanceAs (MeasurableSpace (Fin L → Fin M → ℝ))
  let : BorelSpace (Matrix (Fin L) (Fin M) ℝ) :=
    inferInstanceAs (BorelSpace (Fin L → Fin M → ℝ))
  have hAm : Measurable A := Measurable.of_eval (fun a => Measurable.of_eval (hm a))
  have hcont : Continuous (fun A : Matrix (Fin L) (Fin M) ℝ => ‖matrixMap A‖ ^ 2) :=
    continuous_matrixMap.norm.pow 2
  have hop : Measurable (fun ω => ‖matrixMap (A ω)‖ ^ 2) := hcont.measurable.comp hAm
  exact ⟨hop, matrixMap_secondMoment_transfer μ A hop (frobenius_sq_regular μ A hm hh).2⟩

/-- 標本行列の成分の正則性は、全ペア成分と中心化誤差から導く。 -/
theorem sampledPairDesign_entry_regular {Ω : Type*} [MeasurableSpace Ω]
    {L M T P N : ℕ} [Fact (2 ≤ N)] (hP : 0 < P)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Fin L → Fin M → Fin T → OrderedPair N → ℝ) (w : Fin T → ℝ)
    (hm : ∀ a m t p, Measurable (fun ω => h ω a m t p))
    (hh : ∀ a m t p, MemLp (fun ω => h ω a m t p) 2 μ) (a : Fin L) (m : Fin M) :
    Measurable (fun z => sampledPairDesign (P := P) h w z a m) ∧
    MemLp (fun z => sampledPairDesign h w z a m) 2
      (μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))) := by
  constructor
  · apply measurable_from_prod_countable_left
    intro ω
    change Measurable (fun y => pairPrefactor L N *
      ∑ t, w t * (∑ ν, h y a m t (ω (t, ν))) / P)
    fun_prop
  · have he := pairRowError_joint_memLp (P := P) μ L (fun y t p => h y a m t p) w (hm a m) (hh a m)
    have hf := (fullPairDesign_entry_memLp μ h w hh a m).comp_measurePreserving
      (measurePreserving_fst (ν := independentDraws (Fin T × Fin P) (OrderedPair N)))
    have hd (z : Ω × ((Fin T × Fin P) → OrderedPair N)) :
        pairDesignError h w z a m + fullPairDesign h w z.1 a m = sampledPairDesign h w z a m := by
      rw [pairDesignError_eq_difference Fact.out hP]
      simp
    change MemLp (fun z => pairDesignError h w z a m) 2 _ at he
    have hsum : MemLp (fun z => pairDesignError h w z a m + fullPairDesign h w z.1 a m) 2
        (μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))) := he.add hf
    simpa only [hd] using hsum

/-- 抽象回帰定理に渡すものと同じ、Euclidean空間上の実際の残差。 -/
theorem sampledResidual_eq_regression {Ω : Type*} {L M T P N : ℕ}
    (h : Ω → Fin L → Fin M → Fin T → OrderedPair N → ℝ)
    (w : Fin T → ℝ) (b : Ω → Fin L → ℝ) (θ : Fin M → ℝ)
    (z : Ω × ((Fin T × Fin P) → OrderedPair N)) :
    sampledRegressionResidual h w b θ z =
      WithLp.toLp 2 (b z.1) - matrixMap (sampledPairDesign h w z) (WithLp.toLp 2 θ) := rfl

theorem sampledResidual_norm_sq_regular {Ω : Type*} [MeasurableSpace Ω]
    {L M T P N : ℕ} [Fact (2 ≤ N)] (hP : 0 < P)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Fin L → Fin M → Fin T → OrderedPair N → ℝ)
    (w : Fin T → ℝ) (b : Ω → Fin L → ℝ) (θ : Fin M → ℝ)
    (hm : ∀ a m t p, Measurable (fun ω => h ω a m t p))
    (hh : ∀ a m t p, MemLp (fun ω => h ω a m t p) 2 μ)
    (hbm : ∀ a, Measurable (fun ω => b ω a)) (hb : ∀ a, MemLp (fun ω => b ω a) 2 μ) :
    Measurable (fun z => ‖sampledRegressionResidual (P := P) h w b θ z‖ ^ 2) ∧
    Integrable (fun z => ‖sampledRegressionResidual h w b θ z‖ ^ 2)
      (μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))) := by
  have hs := sampledPairDesign_entry_regular hP μ h w hm hh
  apply finite_vector_norm_sq_regular _ (fun z a => b z.1 a - ∑ m, sampledPairDesign h w z a m * θ m)
  · intro a
    have hba : Measurable (fun z : Ω × ((Fin T × Fin P) → OrderedPair N) => b z.1 a) :=
      (hbm a).comp measurable_fst
    have hsa := fun m => (hs a m).1
    fun_prop
  · intro a
    exact ((hb a).comp_measurePreserving measurePreserving_fst).sub
      (memLp_finsetSum _ (fun m _ => ((hs a m).2).mul_const (θ m)))

end WMFKI
