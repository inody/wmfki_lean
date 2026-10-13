import WMFKI_Stochastic.ParticleSystemProbe
import Chapter11ConstantIntegral

open MeasureTheory Set
open scoped BigOperators
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
namespace WMFKIExternalProbe

/-- The actual stochastic integrals in VectorSDESolution reduce to sigma W for
constant diagonal diffusion, simultaneously at all finite times. -/
theorem additive_sde_equation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (B : BrownianSystem P n)
    (b : Fin n → (Fin n → ℝ) → ℝ) (σ : ℝ) (ξ : Ω → Fin n → ℝ)
    (X : HalfClosedTime → Ω → Fin n → ℝ)
    (hX : VectorSDESolution P B.F B.W b (fun i j _ => if i = j then σ else 0) ξ X) :
    ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → ∀ i,
      X (realTimeClamp r) ω i = ξ ω i + (∫ s in 0..r, b i (X (realTimeClamp s) ω)) +
        σ * B.W i (realTimeClamp r) ω := by
  obtain ⟨I,hI,hIc,he⟩ := hX.integrals
  have hi i j := Asakura.Chapter11.constant_ito_integral_unique P (EReal.coe_lt_top 0)
    B.F B.mono B.le B.null (B.W j) (I i j) (B.martingale j) (hI i j)
    (if i = j then σ else 0) (hIc i j)
  have hall := ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hi i j))
  filter_upwards [he,hall] with ω heq hconst
  intro r hr i
  have ht : (realTimeClamp r : HalfClosedTime) < ⊤ := by
    change (realTimeClamp r : EReal) < ⊤
    rw [real_time_clamp_eq r hr (le_top)]
    exact EReal.coe_lt_top r
  rw [heq r hr (EReal.coe_lt_top r) i]
  simp_rw [hconst _ _ _ ht]
  simp [ite_mul]

end WMFKIExternalProbe
#print axioms WMFKIExternalProbe.additive_sde_equation
