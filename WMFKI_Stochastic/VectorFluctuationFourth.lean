import WMFKI_Stochastic.ConditionalFluctuationFourth
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory ProbabilityTheory

namespace WMFKIIndependentFourth

/-- 固定空間次元の評価。粒子数や全粒子座標の最大値を使わない。 -/
theorem euclidean_norm_fourth_le (d : ℕ) (v : EuclideanSpace ℝ (Fin d)) :
    ‖v‖^4 ≤ (d : ℝ)*∑ c, (v c)^4 := by
  rw [show ‖v‖^4 = (‖v‖^2)^2 by ring, EuclideanSpace.real_norm_sq_eq]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin d => (1 : ℝ)) (fun c => v c^2)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  apply h.trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- 座標間の独立性は不要。d=0も扱う。 -/
theorem vector_fourth_from_coordinates {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ)
    (X : Ω → EuclideanSpace ℝ (Fin d)) (hX : ∀ c, MemLp (fun ω => X ω c) 4 P)
    (C : Fin d → ℝ) (hC : ∀ c, (∫ ω, X ω c^4 ∂P) ≤ C c) :
    MemLp X 4 P ∧ (∫ ω, ‖X ω‖^4 ∂P) ≤ (d : ℝ)*∑ c, C c := by
  have hL : MemLp X 4 P := MemLp.of_eval_piLp hX
  refine ⟨hL, ?_⟩
  calc
    _ ≤ ∫ ω, (d : ℝ)*∑ c, X ω c^4 ∂P :=
      integral_mono (hL.integrable_norm_pow (p := 4) (by decide))
        ((integrable_finsetSum _ (fun c _ => l4_integrable_power (hX c) 4 le_rfl)).const_mul _)
        (fun ω => euclidean_norm_fourth_le d (X ω))
    _ = (d : ℝ)*∑ c, ∫ ω, X ω c^4 ∂P := by
      rw [integral_const_mul, integral_finsetSum _ (fun c _ => l4_integrable_power (hX c) 4 le_rfl)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => hC c)) (Nat.cast_nonneg d)

/-- ベクトル核の経験ドリフトから実際のBochner平均を引く。 -/
noncomputable def vectorKernelFluctuation {A B I : Type*} [MeasurableSpace B] [Fintype I]
    (d N : ℕ) (ν : Measure B) (F : A × B → EuclideanSpace ℝ (Fin d))
    (z : A × (I → B)) : EuclideanSpace ℝ (Fin d) :=
  (N : ℝ)⁻¹ • ∑ i, F (z.1,z.2 i) - ∫ y, F (z.1,y) ∂ν

/-- 同期結合の入力となる固定粒子の揺らぎのベクトル版。
    原始核の積空間L4から有限N補正込みの評価を導く。 -/
theorem vector_kernel_fluctuation_fourth_bound
    {A B I : Type*} [MeasurableSpace A] [MeasurableSpace B] [Fintype I]
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B) [IsProbabilityMeasure ν]
    (d N : ℕ) (hcard : Fintype.card I + 1 = N)
    (F : A × B → EuclideanSpace ℝ (Fin d)) (hF : Measurable F) (hL : MemLp F 4 (μ.prod ν))
    (C : ℝ) (hC : 0 ≤ C) (hFC : (∫ z, ‖F z‖^4 ∂(μ.prod ν)) ≤ C) :
    let R := Measure.pi (fun _ : I => ν)
    MemLp (vectorKernelFluctuation (I := I) d N ν F) 4 (μ.prod R) ∧
    (∫ z, ‖vectorKernelFluctuation (I := I) d N ν F z‖^4 ∂(μ.prod R)) ≤
      392*(d : ℝ)^2*C/(N : ℝ)^2 := by
  classical
  dsimp only
  let R := Measure.pi (fun _ : I => ν)
  let V := vectorKernelFluctuation (I := I) d N ν F
  have hcoord (c : Fin d) := hL.eval_piLp c
  have hcc (c : Fin d) : (∫ z, (F z c)^4 ∂(μ.prod ν)) ≤ C := by
    apply le_trans _ hFC
    apply integral_mono (l4_integrable_power (hcoord c) 4 le_rfl)
      (hL.integrable_norm_pow (p := 4) (by decide))
    intro z
    have h := pow_le_pow_left₀ (norm_nonneg (F z c)) (PiLp.norm_apply_le (F z) c) 4
    simpa only [Real.norm_eq_abs, (show Even (4 : ℕ) from by decide).pow_abs] using h
  have he (c : Fin d) : (fun z => V z c) =ᵐ[μ.prod R]
      kernelFluctuation (I := I) N ν (fun z => F z c) := by
    have hs := (hL.integrable (by norm_num)).prod_right_ae
    filter_upwards [(measurePreserving_fst (μ := μ) (ν := R)).quasiMeasurePreserving.ae hs] with z hz
    change ((N : ℝ)⁻¹ • ∑ i, F (z.1,z.2 i) - ∫ y, F (z.1,y) ∂ν) c = _
    rw [PiLp.sub_apply, PiLp.smul_apply, eval_integral_piLp (fun c => hz.eval_piLp c)]
    have hsum : (∑ i, F (z.1,z.2 i)) c = ∑ i, F (z.1,z.2 i) c := by
      exact map_sum (EuclideanSpace.proj (𝕜 := ℝ) c) _ _
    rw [hsum]
    rfl
  have hscalar (c : Fin d) := kernel_fluctuation_fourth_bound μ ν N hcard
    (fun z => F z c) ((EuclideanSpace.proj c).continuous.measurable.comp hF)
    (hcoord c) C hC (hcc c)
  have hVL (c : Fin d) : MemLp (fun z => V z c) 4 (μ.prod R) := (hscalar c).1.ae_eq (he c).symm
  have hVB (c : Fin d) : (∫ z, V z c^4 ∂(μ.prod R)) ≤ 392*C/(N : ℝ)^2 := by
    calc
      _ = ∫ z, kernelFluctuation (I := I) N ν (fun z => F z c) z^4 ∂(μ.prod R) :=
        integral_congr_ae ((he c).fun_comp (fun a : ℝ => a^4))
      _ ≤ _ := (hscalar c).2
  obtain ⟨hp,hb⟩ := vector_fourth_from_coordinates (μ.prod R) d V hVL
    (fun _ => 392*C/(N : ℝ)^2) hVB
  refine ⟨hp, hb.trans_eq ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end WMFKIIndependentFourth
