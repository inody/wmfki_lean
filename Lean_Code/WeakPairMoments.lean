import Lean_Code.SampledResidual

namespace WMFKI
open MeasureTheory

/-- 観測位置だけから有限和で組み立てる弱形式の応答。φ, lap, ψ, dψはテストの評価値。 -/
noncomputable def observedWeakResponse {Ω F : Type*} {N T L : ℕ}
    (Y : Ω → Fin N → Fin T → F) (φ lap : Fin L → F → ℝ)
    (ψ dψ : Fin L → Fin T → ℝ) (w : Fin T → ℝ) (σ : ℝ)
    (ω : Ω) (a : Fin L) : ℝ :=
  -(1 / (Real.sqrt L * N)) * (∑ i, ∑ t, w t * φ a (Y ω i t) * dψ a t) -
    (σ ^ 2 / (2 * Real.sqrt L * N)) * (∑ i, ∑ t, w t * lap a (Y ω i t) * ψ a t)

/-- 応答の可測性とL2性は、有界テストの有限和から供給する。 -/
theorem observedWeakResponse_regular {Ω F : Type*} [MeasurableSpace Ω]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F] {N T L : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → Fin N → Fin T → F) (φ lap : Fin L → F → ℝ)
    (ψ dψ : Fin L → Fin T → ℝ) (w : Fin T → ℝ) (σ : ℝ)
    (hY : ∀ i t, Measurable (fun ω => Y ω i t))
    (hφ : ∀ a, Continuous (φ a)) (hlap : ∀ a, Continuous (lap a))
    (Cφ Cl : ℝ) (hφb : ∀ a x, |φ a x| ≤ Cφ) (hlapb : ∀ a x, |lap a x| ≤ Cl)
    (a : Fin L) :
    Measurable (fun ω => observedWeakResponse Y φ lap ψ dψ w σ ω a) ∧
    MemLp (fun ω => observedWeakResponse Y φ lap ψ dψ w σ ω a) 2 μ := by
  have hφlp (i : Fin N) (t : Fin T) : MemLp (fun ω => φ a (Y ω i t)) 2 μ :=
    MemLp.of_bound ((hφ a).measurable.comp (hY i t)).aestronglyMeasurable Cφ
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hφb a (Y ω i t))
  have hllp (i : Fin N) (t : Fin T) : MemLp (fun ω => lap a (Y ω i t)) 2 μ :=
    MemLp.of_bound ((hlap a).measurable.comp (hY i t)).aestronglyMeasurable Cl
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hlapb a (Y ω i t))
  constructor
  · unfold observedWeakResponse
    fun_prop
  · exact ((memLp_finsetSum _ (fun i _ => memLp_finsetSum _ (fun t _ =>
        ((hφlp i t).const_mul (w t)).mul_const (dψ a t)))).const_mul _).sub
      ((memLp_finsetSum _ (fun i _ => memLp_finsetSum _ (fun t _ =>
        ((hllp i t).const_mul (w t)).mul_const (ψ a t)))).const_mul _)

/--
加法観測から応答・デザインを実際に組み立て、ペア抽出の二乗平均評価を結合する。
潜在位置モーメントと全ペア残差の上界Vは入力であり、SDEからの導出は含まない。
テストの微分に対応するg,lap,dψを入力するが、その微分関係はここでは要求しない。
-/
theorem weak_pair_moment_bounds {Ω F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] [SecondCountableTopology F]
    {N T P L M : ℕ} [Fact (2 ≤ N)] (hP : 0 < P) (hL : 0 < L)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X e : Ω → Fin N → Fin T → F) (φ lap : Fin L → F → ℝ)
    (ψ dψ : Fin L → Fin T → ℝ) (g : Fin L → F → F) (Φ : Fin M → F → F)
    (w : Fin T → ℝ) (σ : ℝ) (θ : Fin M → ℝ) (κ : F → F)
    (hκ : ∀ z, ∑ m, θ m • Φ m z = κ z)
    (hX : ∀ i t, Measurable (fun ω => X ω i t))
    (he : ∀ i t, Measurable (fun ω => e ω i t))
    (hiX : ∀ i t, Integrable (fun ω => ‖X ω i t‖ ^ 2) μ)
    (hie : ∀ i t, Integrable (fun ω => ‖e ω i t‖ ^ 2) μ)
    (RX Re : ℝ) (hRX0 : 0 ≤ RX) (hRe0 : 0 ≤ Re)
    (hRX : ∀ i t, (∫ ω, ‖X ω i t‖ ^ 2 ∂μ) ≤ RX)
    (hRe : ∀ i t, (∫ ω, ‖e ω i t‖ ^ 2 ∂μ) ≤ Re)
    (hg : ∀ a, Continuous (g a)) (hΦ : ∀ m, Continuous (Φ m)) (hκm : Continuous κ)
    (hφ : ∀ a, Continuous (φ a)) (hlap : ∀ a, Continuous (lap a))
    (Cφ Cl : ℝ) (hφb : ∀ a x, |φ a x| ≤ Cφ) (hlapb : ∀ a x, |lap a x| ≤ Cl)
    (B G K KT : ℝ) (hB : 0 ≤ B) (hG : 0 ≤ G) (hK : 0 ≤ K) (hKT : 0 ≤ KT)
    (hψ : ∀ a t, |ψ a t| ≤ B) (hgb : ∀ a x, ‖g a x‖ ≤ G)
    (hΦb : ∀ m z, ‖Φ m z‖ ≤ K * (1 + ‖z‖))
    (hκb : ∀ z, ‖κ z‖ ≤ KT * (1 + ‖z‖)) (V : ℝ) :
    let Y := fun ω i t => X ω i t + e ω i t
    let h := observedPairFeature Y ψ g Φ
    let b := observedWeakResponse Y φ lap ψ dψ w σ
    let ν := μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))
    (∫ ω, ‖fullRegressionResidual h w b θ ω‖ ^ 2 ∂μ) ≤ V →
    (∀ a m, ν[(fun z => (sampledPairDesign h w z - fullPairDesign h w z.1) a m) |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[ν] 0) ∧
    (∫ z, frobenius (sampledPairDesign h w z - fullPairDesign h w z.1) ^ 2 ∂ν) ≤
      M * featureMomentBound B G K (2 * RX + 2 * Re) * (∑ t, w t ^ 2) / P ∧
    (∫ z, ‖sampledRegressionResidual h w b θ z‖ ^ 2 ∂ν) ≤
      V + featureMomentBound B G KT (2 * RX + 2 * Re) * (∑ t, w t ^ 2) / P := by
  dsimp only
  intro hV
  let Y := fun ω i t => X ω i t + e ω i t
  have hobs (i : Fin N) (t : Fin T) := observation_second_moment μ
    (fun ω => X ω i t) (fun ω => e ω i t) (hX i t) (he i t) (hiX i t) (hie i t)
    RX Re (hRX i t) (hRe i t)
  have hYm : ∀ i t, Measurable (fun ω => Y ω i t) := fun i t => (hobs i t).1
  have hYi : ∀ i t, Integrable (fun ω => ‖Y ω i t‖ ^ 2) μ := fun i t => (hobs i t).2.1
  have hYR : ∀ i t, (∫ ω, ‖Y ω i t‖ ^ 2 ∂μ) ≤ 2 * RX + 2 * Re := fun i t => (hobs i t).2.2
  have hmom := observedPairFeature_moments μ Y ψ g Φ hYm hYi _ hYR hg hΦ
    B G K hB hG hK hψ hgb hΦb
  refine ⟨?_, ?_, ?_⟩
  · exact assembled_design_conditional_centered hP μ _ w
      (observedPairFeature_measurable Y ψ g Φ hYm hg hΦ)
      (fun a m t p => (hmom a m t p).1)
  · exact noisy_observed_design_second_moment hP hL μ X e ψ g Φ w
      hX he hiX hie RX Re hRX0 hRe0 hRX hRe hg hΦ B G K hB hG hK hψ hgb hΦb
  · have hb := observedWeakResponse_regular μ Y φ lap ψ dψ w σ hYm hφ hlap Cφ Cl hφb hlapb
    exact observed_residual_second_moment_bound hP hL μ Y ψ g Φ w _ θ κ hκ
      hYm hYi _ (by positivity) hYR hg hΦ hκm B G K KT hB hG hK hKT hψ hgb hΦb hκb
      (fun a => (hb a).1) (fun a => (hb a).2) V hV

end WMFKI
