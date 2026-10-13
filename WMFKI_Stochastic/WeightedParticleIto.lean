import WMFKI_Stochastic.ParticleC12Drift

open MeasureTheory Set
open scoped BigOperators
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
namespace WMFKIExternalProbe

theorem fderiv_fderiv_const_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) (c : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (fun y => c*f y)) x = c • fderiv ℝ (fderiv ℝ f) x := by
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := (contDiff_succ_iff_fderiv (n := 1)).mp hf |>.2.2
  have he : fderiv ℝ (fun y => c*f y) = fun y => c • fderiv ℝ f y :=
    funext (fun y => fderiv_const_mul (hf.differentiable (by norm_num) y) c)
  rw [he,fderiv_fun_const_smul (hf1.differentiable (by norm_num) x) c]

theorem additiveParticleGenerator_const_mul (N d : ℕ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (σ : ℝ)
    (f : (Fin (N*d) → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (c : ℝ) (x : Fin (N*d) → ℝ) :
    additiveParticleGenerator N d K σ (fun y => c*f y) x =
      c*additiveParticleGenerator N d K σ f x := by
  unfold additiveParticleGenerator
  rw [fderiv_const_mul (hf.differentiable (by norm_num) x) c, fderiv_fderiv_const_mul f hf c x]
  simp only [smul_apply,smul_eq_mul]
  simp_rw [mul_assoc,← Finset.mul_sum]
  ring

/-- Actual time-weighted Ito decomposition, with a C1 (not C2) time test
and genuine first and second spatial derivatives of the observable. -/
theorem weighted_particle_ito
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N d : ℕ) (B : BrownianSystem P (N*d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : Continuous K)
    (σ : ℝ) (ξ : Ω → Fin (N*d) → ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hX : VectorSDESolution P B.F B.W (particleCoordinateDrift N d K)
      (fun i j _ => if i=j then σ else 0) ξ X)
    (f : (Fin (N*d) → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ Z : HalfClosedTime → Ω → ℝ, LocalMProcessWitness P B.F Z ∧
      ∀ t, t ∈ Icc 0 T → (fun ω => ψ t*f (X (realTimeClamp t) ω)) =ᵐ[P]
        fun ω => ψ 0*f (X ⊥ ω)+Z (realTimeClamp t) ω+
          ∫ s in 0..t, deriv ψ s*f (X (realTimeClamp s) ω)+
            ψ s*additiveParticleGenerator N d K σ f (X (realTimeClamp s) ω) := by
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := (contDiff_succ_iff_fderiv (n := 1)).mp hf |>.2.2
  have hdf t x : fderiv ℝ (fun y => ψ t*f y) x = ψ t • fderiv ℝ f x :=
    fderiv_const_mul (hf.differentiable (by norm_num) x) (ψ t)
  have hddf t x := fderiv_fderiv_const_mul f hf (ψ t) x
  have hc1 : Continuous (fun z : ℝ × (Fin (N*d) → ℝ) => fderiv ℝ (fun y => ψ z.1*f y) z.2) := by
    simp_rw [hdf]
    exact (hψ.continuous.comp continuous_fst).smul ((hf.continuous_fderiv (by norm_num)).comp continuous_snd)
  have hc2 : Continuous (fun z : ℝ × (Fin (N*d) → ℝ) => fderiv ℝ (fderiv ℝ (fun y => ψ z.1*f y)) z.2) := by
    simp_rw [hddf]
    exact (hψ.continuous.comp continuous_fst).smul ((hf1.continuous_fderiv (by norm_num)).comp continuous_snd)
  obtain ⟨Z,hZ,he⟩ := particle_c12_drift_representation P N d B K hK σ ξ X hX
    (fun t x => ψ t*f x) (fun z => deriv ψ z.1*f z.2)
    (fun _ => contDiff_const.mul hf)
    (fun t x => (hψ.differentiable (by norm_num) t).hasDerivAt.mul_const (f x))
    ((hψ.continuous.comp continuous_fst).mul (hf.continuous.comp continuous_snd))
    (((hψ.continuous_deriv le_rfl).comp continuous_fst).mul (hf.continuous.comp continuous_snd))
    hc1 hc2 T hT
  refine ⟨Z,hZ,?_⟩
  intro t ht
  filter_upwards [he t ht] with ω hω
  simpa only [additiveParticleGenerator_const_mul N d K σ f hf] using hω

/-- Vanishing endpoint tests yield the weak balance with a proved local
martingale residual. Identifying this residual's Brownian integrands and
its second moment is a separate step, not asserted here. -/
theorem weighted_particle_weak_balance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N d : ℕ) (B : BrownianSystem P (N*d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : Continuous K)
    (σ : ℝ) (ξ : Ω → Fin (N*d) → ℝ)
    (X : HalfClosedTime → Ω → Fin (N*d) → ℝ)
    (hX : VectorSDESolution P B.F B.W (particleCoordinateDrift N d K)
      (fun i j _ => if i=j then σ else 0) ξ X)
    (f : (Fin (N*d) → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ) (T : ℝ) (hT : 0 ≤ T)
    (hψ0 : ψ 0 = 0) (hψT : ψ T = 0) :
    ∃ Z : HalfClosedTime → Ω → ℝ, LocalMProcessWitness P B.F Z ∧
      (fun ω => ∫ s in 0..T, deriv ψ s*f (X (realTimeClamp s) ω)+
        ψ s*additiveParticleGenerator N d K σ f (X (realTimeClamp s) ω)) =ᵐ[P]
      fun ω => -Z (realTimeClamp T) ω := by
  obtain ⟨Z,hZ,he⟩ := weighted_particle_ito P N d B K hK σ ξ X hX f hf ψ hψ T hT
  refine ⟨Z,hZ,?_⟩
  filter_upwards [he T ⟨hT,le_rfl⟩] with ω hω
  simp only [hψ0,hψT,zero_mul,zero_add] at hω
  linarith

end WMFKIExternalProbe
