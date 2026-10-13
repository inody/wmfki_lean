import WMFKI_Stochastic.TaggedCopyLaw

open MeasureTheory ProbabilityTheory Set
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
open WMFKISynchronousModel WMFKIMeanFieldCopies WMFKIIndependentFourth
open scoped NNReal
namespace WMFKIRealizedFluctuation
variable {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω] {d : ℕ}

noncomputable def arrayFluctuation {N : ℕ} (π : Measure A) (P : Measure Ω)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d)) (i : Fin N) (t : ℝ)
    (z : (Fin N → A) × (Fin N → Ω)) : EuclideanSpace ℝ (Fin d) :=
  empiricalFluctuation ((π.prod P).map (Y t)) K (fun j => arrayCopy Y j t z) i

/-- 出力する一様評価。原始入力定理ではこの性質を仮定しない。 -/
def UniformFluctuationFourth (π : Measure A) (P : Measure Ω) (T : ℝ)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d)) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ N : ℕ, 0 < N → ∀ i : Fin N, ∀ t ∈ Icc 0 T,
    MemLp (arrayFluctuation π P K Y i t) 4 (arrayMeasure π P (Fin N)) ∧
    (∫ z, ‖arrayFluctuation π P K Y i t z‖^4 ∂arrayMeasure π P (Fin N)) ≤ C/(N : ℝ)^2

/-- 実際の非線形コピーで、N・任意タグ・時刻より先に定数を選ぶ。 -/
theorem array_fluctuation_uniform_fourth (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P] {T R₀ : ℝ}
    {ξ : A → EuclideanSpace ℝ (Fin d)} {D Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d)}
    {L : ℝ≥0} {K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hK : LipschitzWith L K) (h : ArrayNonlinearFamily π P T K ξ D Y R₀) :
    ∃ C : ℝ, UniformFluctuationFourth π P T K Y C := by
  obtain ⟨R,hR,hr⟩ := h.base_paths.marginal_fourth
  let G : ℝ := ‖K 0‖+(L : ℝ)
  let B : ℝ := 27*G^4*(1+R+R)
  have hG : 0 ≤ G := by dsimp [G];positivity
  have hB : 0 ≤ B := by dsimp [B];positivity
  refine ⟨392*(d : ℝ)^2*B,by positivity,?_⟩
  intro N hN
  cases N with
  | zero => omega
  | succ n =>
    intro i t ht
    let ρ := (π.prod P).map (Y t)
    have : IsProbabilityMeasure ρ := (hr t ht).1
    obtain ⟨hm,h4,hb⟩ := linear_growth_pair_fourth d ρ ρ
      (hr t ht).2.1 (hr t ht).2.1 R R (hr t ht).2.2 (hr t ht).2.2 K
      hK.continuous.measurable G hG (lipschitz_growth_with_origin d hK)
    have hi : iIndepFun (fun j : Fin (n+1) => arrayCopy Y j t) (arrayMeasure π P (Fin (n+1))) :=
      (h.independent (n+1)).comp
        (fun _ (p : Icc (0 : ℝ) T → EuclideanSpace ℝ (Fin d)) => p ⟨t,ht⟩)
        (fun _ => measurable_pi_apply (⟨t,ht⟩ : Icc (0 : ℝ) T))
    exact iid_fluctuation_fourth (arrayMeasure π P (Fin (n+1))) ρ
      (fun j => arrayCopy Y j t) (fun j => (h.paths (n+1) j).measurable t ht) hi
      (fun j => h.law (n+1) j t ht) K hm h4 B hB hb i

set_option maxHeartbeats 800000 in
/-- 原始入力→同期モデル→実際の揺らぎのC/N²。未知の揺らぎ率を入力にしない。 -/
theorem exists_synchronous_family_with_fluctuation (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P]
    (W : Fin d → ℝ≥0 → Ω → ℝ) (hW : ∀ j, IsBrownianReal (W j) P)
    (hm : ∀ j t, Measurable (W j t)) (hI : iIndepFun (fun j ω t => W j t ω) P)
    (ξ : A → EuclideanSpace ℝ (Fin d)) (hξm : Measurable ξ) (hξ : MemLp ξ 4 π)
    (T : ℝ) (hT : 0 ≤ T) (σ : ℝ) {L : ℝ≥0}
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : LipschitzWith L K) :
    ∃ (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d)) (R C : ℝ),
      ArrayNonlinearFamily π P T K ξ
        (fun t z => σ • WithLp.toLp 2 (fun j => W j (halfTimeReal (realTimeClamp t)) z.2)) Y R ∧
      UniformFluctuationFourth π P T K Y C ∧
      ∀ N : ℕ, 0 < N → ∃ (B : BrownianSystem (arrayMeasure π P (Fin N)) (N*d))
        (X : HalfClosedTime → (Fin N → A) × (Fin N → Ω) → Fin (N*d) → ℝ),
        SynchronousParticlePair π P W ξ T σ K Y B X := by
  obtain ⟨Y,R,hy,hp⟩ := exists_synchronous_particle_family π P W hW hm hI ξ hξm hξ T hT σ K hK
  obtain ⟨C,hc⟩ := array_fluctuation_uniform_fourth π P hK hy
  exact ⟨Y,R,C,hy,hc,hp⟩

end WMFKIRealizedFluctuation
