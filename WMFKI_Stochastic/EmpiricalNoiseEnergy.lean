import WMFKI_Stochastic.FiniteBrownianEnergy
import WMFKI_Stochastic.ExpandedEmpiricalBalance

open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
namespace WMFKIExternalProbe

noncomputable def empiricalNoiseIntegrand {Ω : Type*} (N d : ℕ) (σ : ℝ) (ψ : ℝ → ℝ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (k : Fin (N*d)) (z : Ω × ℝ) : ℝ :=
  σ*ψ z.2*fderiv ℝ (empiricalObservable N d φ) (X (realTimeClamp z.2) z.1) (Pi.single k 1)

theorem empirical_noise_coordinate {Ω : Type*} (N d : ℕ) (σ : ℝ) (ψ : ℝ → ℝ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : Differentiable ℝ φ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ) (i : Fin N) (a : Fin d) (z : Ω × ℝ) :
    empiricalNoiseIntegrand N d σ ψ φ X (finProdFinEquiv (i,a)) z =
      (σ/(N : ℝ))*ψ z.2*(gradient φ (particlePositions N d (X (realTimeClamp z.2) z.1) i) : EuclideanSpace ℝ (Fin d)) a := by
  unfold empiricalNoiseIntegrand
  rw [empirical_fderiv_coordinate N d φ hφ, fderiv_euclidean_coordinate]
  simp only [div_eq_mul_inv]
  ring

theorem empirical_noise_pointwise_energy {Ω : Type*} (N d : ℕ) (hN : 0 < N)
    (σ : ℝ) (ψ : ℝ → ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : Differentiable ℝ φ)
    (G : ℝ) (hbound : ∀ x, ‖gradient φ x‖ ≤ G)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ) (z : Ω × ℝ) :
    (∑ k, empiricalNoiseIntegrand N d σ ψ φ X k z^2) ≤ (σ^2/(N : ℝ))*G^2*(ψ z.2)^2 := by
  simp only [empiricalNoiseIntegrand,mul_pow]
  rw [←Finset.mul_sum]
  calc
    _ ≤ (σ^2*(ψ z.2)^2)*(G^2/(N : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (empirical_gradient_energy_bound N d hN φ hφ G hbound _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := by ring

/-- Regularity is obtained from actual continuous adapted paths, rather
than supplied as a stochastic-integral or moment assumption. -/
theorem empirical_noise_regularity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N d : ℕ) (B : BrownianSystem P (N*d)) (σ : ℝ)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (ha : ∀ t, t < ⊤ → Measurable[B.F t] (X t))
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t)
    (T : ℝ) (hT : 0 ≤ T) :
    (∀ k, Measurable (empiricalNoiseIntegrand N d σ ψ φ X k)) ∧
    (∀ k, @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) T => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) T => empiricalNoiseIntegrand N d σ ψ φ X k (z.1,z.2.val))) := by
  have hf (r : ℝ) : (realTimeClamp r : HalfClosedTime) < ⊤ := by
    apply (real_time_clamp_mono (le_max_left r 0)).trans_lt
    exact real_time_below (max r 0) (le_max_right r 0) (EReal.coe_lt_top _)
  have hxc := half_process_real_continuous X hc
  have hxm : Measurable (fun z : Ω × ℝ => X (realTimeClamp z.2) z.1) :=
    (measurable_uncurry_of_continuous_of_measurable hxc
      (fun r => (ha _ (hf r)).mono (B.le _) le_rfl)).comp measurable_swap
  have hd k : Continuous (fun x => fderiv ℝ (empiricalObservable N d φ) x (Pi.single k 1)) :=
    ((empiricalObservable_contDiff N d φ hφ).continuous_fderiv (by norm_num)).clm_apply continuous_const
  constructor
  · intro k
    exact ((hψ.measurable.comp measurable_snd).const_mul σ).mul ((hd k).measurable.comp hxm)
  · intro k
    apply continuous_adapted_real_progressive B.F B.mono _ T hT
    · intro r _
      exact ((hd k).measurable.comp (ha _ (hf r))).const_mul (σ*ψ r)
    · intro ω
      exact ((hψ.const_mul σ).mul ((hd k).comp (hxc ω))).continuousOn

/-- Construct genuine Brownian-coordinate integrals along the supplied
actual interacting SDE solution. They are true L2 martingales, centered,
and their sum has the sigma^2/N energy bound. Identification of this sum
with the residual in expanded_empirical_weak_response is a separate step. -/
theorem exists_empirical_noise_with_energy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N d : ℕ) (hN : 0 < N) (B : BrownianSystem P (N*d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (σ : ℝ) (ξ : Ω → Fin (N*d) → ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hX : VectorSDESolution P B.F B.W (particleCoordinateDrift N d K)
      (fun i j _ => if i=j then σ else 0) ξ X)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (G : ℝ) (hbound : ∀ x, ‖gradient φ x‖ ≤ G) (T : ℝ) (hT : 0 ≤ T) :
    ∃ M : Fin (N*d) → HalfClosedTime → Ω → ℝ,
      (∀ k, ContinuousM2Witness P B.F (M k)) ∧
      (∀ k, LocalMProcessWitness P B.F (M k)) ∧
      (∀ k, ItoCovarianceFormula P B.F (B.W k)
        (fun z => (Iic T).indicator (fun r => empiricalNoiseIntegrand N d σ ψ φ X k (z.1,r)) z.2) (M k)) ∧
      ContinuousM2Witness P B.F (fun t ω => ∑ k, M k t ω) ∧
      (∫ ω, (∑ k, M k (realTimeClamp T) ω) ∂P) = 0 ∧
      (∫ ω, (∑ k, M k (realTimeClamp T) ω)^2 ∂P) ≤
        (σ^2/(N : ℝ))*G^2*(∫ s in 0..T, (ψ s)^2) := by
  classical
  let H := empiricalNoiseIntegrand N d σ ψ φ X
  let ν := P.prod (volume.restrict (Ioo 0 T))
  let C := (σ^2/(N : ℝ))*G^2
  obtain ⟨hm,hp⟩ := empirical_noise_regularity P N d B σ ψ hψ φ hφ X hX.adapted hX.path T hT
  have he z : (∑ k, H k z^2) ≤ C*(ψ z.2)^2 :=
    empirical_noise_pointwise_energy N d hN σ ψ φ (hφ.differentiable (by norm_num)) G hbound X z
  have ht : Integrable (fun s => C*(ψ s)^2) (volume.restrict (Ioo 0 T)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mp
      (((hψ.pow 2).const_mul C).intervalIntegrable 0 T)
  have hg : Integrable (fun z : Ω × ℝ => C*(ψ z.2)^2) ν := ht.comp_snd P
  have hi k : Integrable (fun z => H k z^2) ν := by
    apply hg.mono' ((hm k).pow_const 2).aestronglyMeasurable
    apply ae_of_all
    intro z
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact (Finset.single_le_sum (fun j _ => sq_nonneg (H j z)) (Finset.mem_univ k)).trans (he z)
  obtain ⟨M,hM,hMl,hI,hS,hE⟩ := finite_brownian_integrals_energy P (N*d) B T hT H hm hp hi
  refine ⟨M,hM,hMl,hI,hS,(continuous_m2_mean_zero P B.F B.le _ hS _).2,?_⟩
  calc
    _ = ∑ k, ∫ z, H k z^2 ∂ν := hE
    _ = ∫ z, ∑ k, H k z^2 ∂ν := (integral_finsetSum _ (fun k _ => hi k)).symm
    _ ≤ ∫ z, C*(ψ z.2)^2 ∂ν := integral_mono_ae
      (integrable_finsetSum _ (fun k _ => hi k)) hg (ae_of_all _ he)
    _ = C*(∫ s in 0..T, (ψ s)^2) := by
      dsimp only [ν]
      rw [integral_fun_snd (fun s => C*(ψ s)^2)]
      simp only [probReal_univ,one_smul]
      rw [integral_const_mul,restrict_Ioo_eq_restrict_Ioc,intervalIntegral.integral_of_le hT]

end WMFKIExternalProbe
