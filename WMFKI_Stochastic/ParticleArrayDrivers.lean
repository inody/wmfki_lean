import WMFKI_Stochastic.ArrayProductRealization
import WMFKI_Stochastic.AdditiveParticleEquation

open MeasureTheory ProbabilityTheory
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
open WMFKIMeanFieldCopies WMFKIExternalProbe
open scoped NNReal
namespace WMFKISynchronousModel
variable {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω]

def flatBrownian {d : ℕ} (W : Fin d → ℝ≥0 → Ω → ℝ) (N : ℕ)
    (k : Fin (N*d)) (t : ℝ≥0) (ω : Fin N → Ω) : ℝ :=
  W (finProdFinEquiv.symm k).2 t (ω (finProdFinEquiv.symm k).1)

omit [MeasurableSpace Ω] in
theorem flat_brownian_coordinate {N d : ℕ} (W : Fin d → ℝ≥0 → Ω → ℝ)
    (i : Fin N) (j : Fin d) (t : ℝ≥0) (ω : Fin N → Ω) :
    flatBrownian W N (finProdFinEquiv (i,j)) t ω = W j t (ω i) := by
  simp [flatBrownian]

/-- Brownianの粒子・空間座標を既存粒子SDEの番号に接続する。 -/
theorem flat_brownian_family (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (W : Fin d → ℝ≥0 → Ω → ℝ) (hW : ∀ j, IsBrownianReal (W j) P)
    (hm : ∀ j t, Measurable (W j t)) (hI : iIndepFun (fun j ω t => W j t ω) P) (N : ℕ) :
    (∀ k, IsBrownianReal (flatBrownian W N k) (Measure.pi (fun _ : Fin N => P))) ∧
    (∀ k t, Measurable (flatBrownian W N k t)) ∧
    iIndepFun (fun k ω t => flatBrownian W N k t ω) (Measure.pi (fun _ : Fin N => P)) := by
  obtain ⟨hb,hm',hi⟩ := replicated_brownian_family (I := Fin N) W hW hm hI
  exact ⟨fun k => hb (finProdFinEquiv.symm k),fun k t => hm' (finProdFinEquiv.symm k) t,
    iIndepFun.precomp finProdFinEquiv.symm.injective hi⟩

/-- 同じ原始入力配列から、相互作用粒子と完備BrownianSystemを実際に構成する。
    コピー過程をこの新しいフィルトレーションに適合すると仮定しない。 -/
theorem exists_particle_on_arrays (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P] {d : ℕ}
    (W : Fin d → ℝ≥0 → Ω → ℝ) (hW : ∀ j, IsBrownianReal (W j) P)
    (hm : ∀ j t, Measurable (W j t)) (hI : iIndepFun (fun j ω t => W j t ω) P)
    (ξ : A → EuclideanSpace ℝ (Fin d)) (hξm : Measurable ξ) (hξ : MemLp ξ 4 π)
    (N : ℕ) (hN : 0 < N) {L : ℝ≥0}
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : LipschitzWith L K) (σ : ℝ) :
    ∃ (B : BrownianSystem (arrayMeasure π P (Fin N)) (N*d))
      (X : HalfClosedTime → (Fin N → A) × (Fin N → Ω) → Fin (N*d) → ℝ),
      (∀ᵐ z ∂arrayMeasure π P (Fin N), ∀ i j t,
        B.W (finProdFinEquiv (i,j)) t z = W j (halfTimeReal t) (z.2 i)) ∧
      IndepFun (Prod.fst : (Fin N → A) × (Fin N → Ω) → Fin N → A)
        (fun z (q : Fin (N*d) × HalfClosedTime) => B.W q.1 q.2 z) (arrayMeasure π P (Fin N)) ∧
      VectorSDESolution (arrayMeasure π P (Fin N)) B.F B.W (particleCoordinateDrift N d K)
        (fun i j _ => if i = j then σ else 0) (fun z => packParticles N d (fun i => ξ (z.1 i))) X := by
  obtain ⟨hb,hm',hi⟩ := flat_brownian_family P W hW hm hI N
  obtain ⟨B,X,he,hind,hX,_⟩ := exists_unique_product_particle_system
    (Measure.pi (fun _ : Fin N => π)) (Measure.pi (fun _ : Fin N => P)) N d hN
    (flatBrownian W N) hb hm' hi (fun a i => ξ (a i))
    (fun i => hξm.comp (measurable_pi_apply i))
    (fun i => hξ.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => π) i))
    K L L.coe_nonneg (fun u v => hK.norm_sub_le u v) σ
  refine ⟨B,X,?_,hind,hX⟩
  filter_upwards [he] with z hz
  intro i j t
  simpa only [flat_brownian_coordinate] using hz (finProdFinEquiv (i,j)) t

end WMFKISynchronousModel
