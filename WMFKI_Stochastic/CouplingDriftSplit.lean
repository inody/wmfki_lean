import WMFKI_Stochastic.SynchronousArrayEquation

open MeasureTheory
open Asakura.FullAudit Asakura.Chapter2Complete
open WMFKIExternalProbe
open scoped BigOperators NNReal
namespace WMFKISynchronousModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- 対角を含む和との違いはK(0)/N。K(0)=0とはしない。 -/
theorem particle_drift_full_sum {N : ℕ} (K : E → E) (x : Fin N → E) (i : Fin N) :
    particleDrift K x i = (N : ℝ)⁻¹ • (∑ j, K (x i-x j)) - (N : ℝ)⁻¹ • K 0 := by
  have he (j : Fin N) : (if i = j then 0 else K (x i-x j)) =
      K (x i-x j) - (if i = j then K 0 else 0) := by
    by_cases h : i = j <;> simp [h]
  unfold particleDrift
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  simp [smul_sub]

/-- 正確な自己項補正を残した、ラベルごとの次元非依存安定性。 -/
theorem particle_drift_component_bound {N : ℕ} (hN : 0 < N) {L : ℝ≥0}
    (K : E → E) (hK : LipschitzWith L K) (x y : Fin N → E) (i : Fin N) :
    ‖particleDrift K x i-particleDrift K y i‖ ≤
      (L : ℝ)*‖x i-y i‖ + (L : ℝ)*((N : ℝ)⁻¹*∑ j, ‖x j-y j‖) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm (j : Fin N) :
      ‖(if i = j then 0 else K (x i-x j))-(if i = j then 0 else K (y i-y j))‖ ≤
        (L : ℝ)*‖x i-y i‖+(L : ℝ)*‖x j-y j‖ := by
    by_cases hij : i = j
    · simp only [hij,ite_true,sub_self,norm_zero]
      positivity
    · simp only [hij,ite_false]
      calc
        _ ≤ (L : ℝ)*‖(x i-x j)-(y i-y j)‖ := hK.norm_sub_le _ _
        _ = (L : ℝ)*‖(x i-y i)-(x j-y j)‖ := by congr 2;abel
        _ ≤ (L : ℝ)*(‖x i-y i‖+‖x j-y j‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) L.coe_nonneg
        _ = _ := by ring
  unfold particleDrift
  rw [← smul_sub,← Finset.sum_sub_distrib,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hn.le)]
  calc
    _ ≤ (N : ℝ)⁻¹*∑ j, ‖(if i = j then 0 else K (x i-x j))-(if i = j then 0 else K (y i-y j))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn.le)
    _ ≤ (N : ℝ)⁻¹*∑ j, ((L : ℝ)*‖x i-y i‖+(L : ℝ)*‖x j-y j‖) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hterm j)) (inv_nonneg.mpr hn.le)
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        ← Finset.mul_sum]
      field_simp

variable [MeasurableSpace E]
/-- 実際のoff-diagonal平均と母集団平均の差。中心化はこの定義に仮定しない。 -/
noncomputable def empiricalFluctuation {N : ℕ} (ρ : Measure E) (K : E → E) (y : Fin N → E) (i : Fin N) : E :=
  particleDrift K y i - ∫ z, K (y i-z) ∂ρ

theorem drift_gap_split {N : ℕ} (ρ : Measure E) (K : E → E) (x y : Fin N → E) (i : Fin N) :
    particleDrift K x i - (∫ z, K (y i-z) ∂ρ) =
      (particleDrift K x i-particleDrift K y i) + empiricalFluctuation ρ K y i := by
  unfold empiricalFluctuation
  abel

theorem drift_gap_norm_bound {N : ℕ} (hN : 0 < N) (ρ : Measure E) {L : ℝ≥0}
    (K : E → E) (hK : LipschitzWith L K) (x y : Fin N → E) (i : Fin N) :
    ‖particleDrift K x i - (∫ z, K (y i-z) ∂ρ)‖ ≤
      (L : ℝ)*‖x i-y i‖+(L : ℝ)*((N : ℝ)⁻¹*∑ j, ‖x j-y j‖)+‖empiricalFluctuation ρ K y i‖ := by
  rw [drift_gap_split]
  exact (norm_add_le _ _).trans (add_le_add (particle_drift_component_bound hN K hK x y i) (le_refl _))

/-- 構成した粒子・コピー・実際の母集団法則に、上の分解と安定性を接続する。 -/
theorem synchronous_drift_gap_bound {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
    {N d : ℕ} (hN : 0 < N) (π : Measure A) (P : Measure Ω) {L : ℝ≥0}
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : LipschitzWith L K)
    (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d))
    (X : HalfClosedTime → (Fin N → A) × (Fin N → Ω) → Fin (N*d) → ℝ)
    (i : Fin N) (s : ℝ) (z : (Fin N → A) × (Fin N → Ω)) :
    ‖driftGap π P K Y X i s z‖ ≤
      (L : ℝ)*‖realParticle X i s z-arrayCopy Y i s z‖ +
      (L : ℝ)*((N : ℝ)⁻¹*∑ j, ‖realParticle X j s z-arrayCopy Y j s z‖) +
      ‖empiricalFluctuation ((π.prod P).map (Y s)) K (fun j => arrayCopy Y j s z) i‖ :=
  drift_gap_norm_bound hN ((π.prod P).map (Y s)) K hK
    (fun j => realParticle X j s z) (fun j => arrayCopy Y j s z) i

end WMFKISynchronousModel
