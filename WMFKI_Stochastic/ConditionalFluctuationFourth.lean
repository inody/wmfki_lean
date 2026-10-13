import WMFKI_Stochastic.KernelCenteringFourth

open MeasureTheory ProbabilityTheory

namespace WMFKIIndependentFourth

/-- Nで正規化した条件付き中心化和のL4率。項数はN以下でよい。 -/
theorem conditional_fourth_average
    {A B I : Type*} [MeasurableSpace A] [MeasurableSpace B] [Fintype I]
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B) [IsProbabilityMeasure ν]
    (N : ℕ) (hN : 0 < N) (s : Finset I) (hs : s.card ≤ N)
    (F : A × B → ℝ) (hF : Measurable F) (hL : MemLp F 4 (μ.prod ν))
    (hc : ∀ᵐ x ∂μ, (∫ y, F (x,y) ∂ν) = 0) :
    let R := Measure.pi (fun _ : I => ν)
    let U := fun z : A × (I → B) => (N : ℝ)⁻¹ * ∑ i ∈ s, F (z.1,z.2 i)
    MemLp U 4 (μ.prod R) ∧
    (∫ z, U z^4 ∂(μ.prod R)) ≤ 3*(∫ z, F z^4 ∂(μ.prod ν))/(N : ℝ)^2 := by
  dsimp only
  obtain ⟨hS,hB⟩ := conditionally_centered_fourth_sum μ ν s F hF hL hc
  refine ⟨hS.const_mul _, ?_⟩
  simp_rw [mul_pow]
  rw [integral_const_mul]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hcard : (s.card : ℝ) ≤ N := by exact_mod_cast hs
  have hA : 0 ≤ ∫ z, F z^4 ∂(μ.prod ν) := integral_nonneg (fun _ => by positivity)
  calc
    _ ≤ (N : ℝ)⁻¹^4 * (3*(s.card : ℝ)^2*(∫ z, F z^4 ∂(μ.prod ν))) :=
      mul_le_mul_of_nonneg_left hB (by positivity)
    _ ≤ (N : ℝ)⁻¹^4 * (3*(N : ℝ)^2*(∫ z, F z^4 ∂(μ.prod ν))) := by gcongr
    _ = _ := by field_simp

/-- 実際の経験ドリフトと平均場ドリフトの差。和はN-1項、分母はN。 -/
noncomputable def kernelFluctuation {A B I : Type*} [MeasurableSpace B] [Fintype I]
    (N : ℕ) (ν : Measure B) (F : A × B → ℝ) (z : A × (I → B)) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, F (z.1,z.2 i) - ∫ y, F (z.1,y) ∂ν

/-- 中心化和と有限N補正への正確な分解。N=1も含む。 -/
theorem kernel_fluctuation_centering {A B I : Type*} [MeasurableSpace B] [Fintype I]
    (N : ℕ) (hcard : Fintype.card I + 1 = N) (ν : Measure B) (F : A × B → ℝ)
    (z : A × (I → B)) :
    kernelFluctuation N ν F z =
      (N : ℝ)⁻¹ * ∑ i, (F (z.1,z.2 i) - ∫ y, F (z.1,y) ∂ν) -
      (N : ℝ)⁻¹ * (∫ y, F (z.1,y) ∂ν) := by
  have hN : 0 < N := by omega
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hc : (Fintype.card I : ℝ) + 1 = N := by exact_mod_cast hcard
  unfold kernelFluctuation
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  nlinarith [congrArg (fun t : ℝ => t*(∫ y, F (z.1,y) ∂ν)) hc]

/-- 原始的な核のL4のみから、有限N補正込みの揺らぎをO(N^-2)で評価。
    中心化、各切片のL4、平均のL4はいずれも内部で証明する。 -/
theorem kernel_fluctuation_fourth_bound
    {A B I : Type*} [MeasurableSpace A] [MeasurableSpace B] [Fintype I]
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B) [IsProbabilityMeasure ν]
    (N : ℕ) (hcard : Fintype.card I + 1 = N)
    (F : A × B → ℝ) (hF : Measurable F) (hL : MemLp F 4 (μ.prod ν))
    (C : ℝ) (hC : 0 ≤ C) (hFC : (∫ z, F z^4 ∂(μ.prod ν)) ≤ C) :
    let R := Measure.pi (fun _ : I => ν)
    MemLp (kernelFluctuation (I := I) N ν F) 4 (μ.prod R) ∧
    (∫ z, kernelFluctuation (I := I) N ν F z ^ 4 ∂(μ.prod R)) ≤ 392*C/(N : ℝ)^2 := by
  classical
  dsimp only
  let R := Measure.pi (fun _ : I => ν)
  let H := fun z : A × B => F z - ∫ y, F (z.1,y) ∂ν
  let U := fun z : A × (I → B) => (N : ℝ)⁻¹ * ∑ i, H (z.1,z.2 i)
  let g := fun z : A × (I → B) => (N : ℝ)⁻¹ * ∫ y, F (z.1,y) ∂ν
  have hN : 0 < N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hHm,hHL,hH0,hH4⟩ := centered_kernel_fourth μ ν F hF hL
  obtain ⟨hU,hU4⟩ := conditional_fourth_average μ ν N hN (Finset.univ : Finset I)
    (by simpa using (show Fintype.card I ≤ N by omega)) H hHm hHL hH0
  have hUbound : (∫ z, U z^4 ∂(μ.prod R)) ≤ 48*C/(N : ℝ)^2 := by
    apply hU4.trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    linarith
  obtain ⟨hmean,hmean4⟩ := parameter_mean_fourth μ ν F hF hL
  have hg : MemLp g 4 (μ.prod R) := (hmean.comp_fst R).const_mul _
  have hgbound : (∫ z, g z^4 ∂(μ.prod R)) ≤ C/(N : ℝ)^2 := by
    dsimp only [g]
    simp_rw [mul_pow]
    rw [integral_const_mul, integral_fun_fst (fun x => (∫ y, F (x,y) ∂ν)^4)]
    simp only [probReal_univ, one_smul]
    calc
      _ ≤ (N : ℝ)⁻¹^4 * C := mul_le_mul_of_nonneg_left (hmean4.trans hFC) (by positivity)
      _ = C/(N : ℝ)^4 := by ring
      _ ≤ C/(N : ℝ)^2 := div_le_div_of_nonneg_left hC (sq_pos_of_pos hn)
        (by nlinarith [sq_nonneg ((N : ℝ)^2 - 1)])
  have he : kernelFluctuation (I := I) N ν F = fun z => U z - g z := by
    funext z
    exact kernel_fluctuation_centering N hcard ν F z
  rw [he]
  refine ⟨hU.sub hg, ?_⟩
  have hUi := l4_integrable_power hU 4 le_rfl
  have hgi := l4_integrable_power hg 4 le_rfl
  calc
    _ ≤ ∫ z, 8*(U z^4+g z^4) ∂(μ.prod R) :=
      integral_mono (l4_integrable_power (hU.sub hg) 4 le_rfl) ((hUi.add hgi).const_mul 8)
        (fun z => fourth_sub_le _ _)
    _ = 8*((∫ z, U z^4 ∂(μ.prod R))+(∫ z, g z^4 ∂(μ.prod R))) := by
      rw [integral_const_mul, integral_add hUi hgi]
    _ ≤ 8*(48*C/(N : ℝ)^2+C/(N : ℝ)^2) := by linarith
    _ = _ := by ring

end WMFKIIndependentFourth
