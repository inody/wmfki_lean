import Lean_Code.ObservationMoments

namespace WMFKI
open MeasureTheory

variable {Ω F : Type*} [MeasurableSpace Ω] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

/-- 有限時刻で観測した粒子位置から評価する、原稿のペア特徴。 -/
noncomputable def observedPairFeature {N T L M : ℕ}
    (Y : Ω → Fin N → Fin T → F) (ψ : Fin L → Fin T → ℝ)
    (g : Fin L → F → F) (Φ : Fin M → F → F)
    (ω : Ω) (a : Fin L) (m : Fin M) (t : Fin T) (p : OrderedPair N) : ℝ :=
  ψ a t * inner ℝ (g a (Y ω p.1.1 t)) (Φ m (Y ω p.1.1 t - Y ω p.1.2 t))

def featureMomentBound (B G K R : ℝ) : ℝ := 3 * (B * G * K) ^ 2 * (1 + 2 * R)

theorem observedPairFeature_measurable {N T L M : ℕ}
    (Y : Ω → Fin N → Fin T → F) (ψ : Fin L → Fin T → ℝ)
    (g : Fin L → F → F) (Φ : Fin M → F → F)
    (hY : ∀ i t, Measurable (fun ω => Y ω i t))
    (hg : ∀ a, Continuous (g a)) (hΦ : ∀ m, Continuous (Φ m))
    (a : Fin L) (m : Fin M) (t : Fin T) (p : OrderedPair N) :
    Measurable (fun ω => observedPairFeature Y ψ g Φ ω a m t p) := by
  unfold observedPairFeature
  fun_prop

theorem observedPairFeature_moments {N T L M : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → Fin N → Fin T → F) (ψ : Fin L → Fin T → ℝ)
    (g : Fin L → F → F) (Φ : Fin M → F → F)
    (hY : ∀ i t, Measurable (fun ω => Y ω i t))
    (hiY : ∀ i t, Integrable (fun ω => ‖Y ω i t‖ ^ 2) μ)
    (R : ℝ) (hR : ∀ i t, (∫ ω, ‖Y ω i t‖ ^ 2 ∂μ) ≤ R)
    (hg : ∀ a, Continuous (g a)) (hΦ : ∀ m, Continuous (Φ m))
    (B G K : ℝ) (hB : 0 ≤ B) (hG : 0 ≤ G) (hK : 0 ≤ K)
    (hψ : ∀ a t, |ψ a t| ≤ B) (hgb : ∀ a x, ‖g a x‖ ≤ G)
    (hΦb : ∀ m z, ‖Φ m z‖ ≤ K * (1 + ‖z‖))
    (a : Fin L) (m : Fin M) (t : Fin T) (p : OrderedPair N) :
    MemLp (fun ω => observedPairFeature Y ψ g Φ ω a m t p) 2 μ ∧
    (∫ ω, observedPairFeature Y ψ g Φ ω a m t p ^ 2 ∂μ) ≤ featureMomentBound B G K R := by
  exact pairFeature_second_moment μ _ _ (hY _ _) (hY _ _) (hiY _ _) (hiY _ _)
    R (hR _ _) (hR _ _) (g a) (Φ m) (hg a) (hΦ m) (ψ a t) B G K
    hB hG hK (hψ a t) (hgb a) (hΦb m)

/-- 位置モーメントから、実際の特徴で組み立てたデザイン差までを結ぶ。 -/
theorem observed_design_second_moment {N T P L M : ℕ} [Fact (2 ≤ N)]
    (hP : 0 < P) (hL : 0 < L) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → Fin N → Fin T → F) (ψ : Fin L → Fin T → ℝ)
    (g : Fin L → F → F) (Φ : Fin M → F → F) (w : Fin T → ℝ)
    (hY : ∀ i t, Measurable (fun ω => Y ω i t))
    (hiY : ∀ i t, Integrable (fun ω => ‖Y ω i t‖ ^ 2) μ)
    (R : ℝ) (hR0 : 0 ≤ R) (hR : ∀ i t, (∫ ω, ‖Y ω i t‖ ^ 2 ∂μ) ≤ R)
    (hg : ∀ a, Continuous (g a)) (hΦ : ∀ m, Continuous (Φ m))
    (B G K : ℝ) (hB : 0 ≤ B) (hG : 0 ≤ G) (hK : 0 ≤ K)
    (hψ : ∀ a t, |ψ a t| ≤ B) (hgb : ∀ a x, ‖g a x‖ ≤ G)
    (hΦb : ∀ m z, ‖Φ m z‖ ≤ K * (1 + ‖z‖)) :
    (∫ z, frobenius (sampledPairDesign (observedPairFeature Y ψ g Φ) w z -
      fullPairDesign (observedPairFeature Y ψ g Φ) w z.1) ^ 2
      ∂μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))) ≤
      M * featureMomentBound B G K R * (∑ t, w t ^ 2) / P := by
  have hc : 0 ≤ featureMomentBound B G K R := by unfold featureMomentBound; positivity
  have hmom := observedPairFeature_moments μ Y ψ g Φ hY hiY R hR hg hΦ
    B G K hB hG hK hψ hgb hΦb
  exact assembled_design_second_moment hP hL μ _ w _ hc
    (observedPairFeature_measurable Y ψ g Φ hY hg hΦ)
    (fun a m t p => (hmom a m t p).1) (fun a m t p => (hmom a m t p).2)

/-- 潜在位置と加法観測誤差のモーメントからペア・デザイン誤差までを一括して導く。 -/
theorem noisy_observed_design_second_moment {N T P L M : ℕ} [Fact (2 ≤ N)]
    (hP : 0 < P) (hL : 0 < L) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X e : Ω → Fin N → Fin T → F) (ψ : Fin L → Fin T → ℝ)
    (g : Fin L → F → F) (Φ : Fin M → F → F) (w : Fin T → ℝ)
    (hX : ∀ i t, Measurable (fun ω => X ω i t))
    (he : ∀ i t, Measurable (fun ω => e ω i t))
    (hiX : ∀ i t, Integrable (fun ω => ‖X ω i t‖ ^ 2) μ)
    (hie : ∀ i t, Integrable (fun ω => ‖e ω i t‖ ^ 2) μ)
    (RX Re : ℝ) (hRX0 : 0 ≤ RX) (hRe0 : 0 ≤ Re)
    (hRX : ∀ i t, (∫ ω, ‖X ω i t‖ ^ 2 ∂μ) ≤ RX)
    (hRe : ∀ i t, (∫ ω, ‖e ω i t‖ ^ 2 ∂μ) ≤ Re)
    (hg : ∀ a, Continuous (g a)) (hΦ : ∀ m, Continuous (Φ m))
    (B G K : ℝ) (hB : 0 ≤ B) (hG : 0 ≤ G) (hK : 0 ≤ K)
    (hψ : ∀ a t, |ψ a t| ≤ B) (hgb : ∀ a x, ‖g a x‖ ≤ G)
    (hΦb : ∀ m z, ‖Φ m z‖ ≤ K * (1 + ‖z‖)) :
    let Y := fun ω i t => X ω i t + e ω i t
    (∫ z, frobenius (sampledPairDesign (observedPairFeature Y ψ g Φ) w z -
      fullPairDesign (observedPairFeature Y ψ g Φ) w z.1) ^ 2
      ∂μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))) ≤
      M * featureMomentBound B G K (2 * RX + 2 * Re) * (∑ t, w t ^ 2) / P := by
  have hobs (i : Fin N) (t : Fin T) := observation_second_moment μ
    (fun ω => X ω i t) (fun ω => e ω i t) (hX i t) (he i t) (hiX i t) (hie i t)
    RX Re (hRX i t) (hRe i t)
  exact observed_design_second_moment hP hL μ _ ψ g Φ w
    (fun i t => (hobs i t).1) (fun i t => (hobs i t).2.1)
    _ (by positivity) (fun i t => (hobs i t).2.2)
    hg hΦ B G K hB hG hK hψ hgb hΦb

omit [MeasurableSpace Ω] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
/-- 辞書の厳密表現を使うと、合成特徴は真の相互作用の特徴になる。 -/
theorem observedPairFeature_realizable {N T L M : ℕ}
    (Y : Ω → Fin N → Fin T → F) (ψ : Fin L → Fin T → ℝ)
    (g : Fin L → F → F) (Φ : Fin M → F → F) (θ : Fin M → ℝ) (κ : F → F)
    (hκ : ∀ z, ∑ m, θ m • Φ m z = κ z)
    (ω : Ω) (a : Fin L) (t : Fin T) (p : OrderedPair N) :
    (∑ m, θ m * observedPairFeature Y ψ g Φ ω a m t p) =
      ψ a t * inner ℝ (g a (Y ω p.1.1 t)) (κ (Y ω p.1.1 t - Y ω p.1.2 t)) := by
  rw [← hκ]
  simp only [inner_sum, inner_smul_right, Finset.mul_sum, observedPairFeature]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- 真の相互作用の成長率を使い、係数の大きさやsupport数を増やさない評価。 -/
theorem observed_direction_second_moment {N T P L M : ℕ} [Fact (2 ≤ N)]
    (hP : 0 < P) (hL : 0 < L) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → Fin N → Fin T → F) (ψ : Fin L → Fin T → ℝ)
    (g : Fin L → F → F) (Φ : Fin M → F → F) (w : Fin T → ℝ)
    (θ : Fin M → ℝ) (κ : F → F) (hκ : ∀ z, ∑ m, θ m • Φ m z = κ z)
    (hY : ∀ i t, Measurable (fun ω => Y ω i t))
    (hiY : ∀ i t, Integrable (fun ω => ‖Y ω i t‖ ^ 2) μ)
    (R : ℝ) (hR0 : 0 ≤ R) (hR : ∀ i t, (∫ ω, ‖Y ω i t‖ ^ 2 ∂μ) ≤ R)
    (hg : ∀ a, Continuous (g a)) (hκm : Continuous κ)
    (B G K : ℝ) (hB : 0 ≤ B) (hG : 0 ≤ G) (hK : 0 ≤ K)
    (hψ : ∀ a t, |ψ a t| ≤ B) (hgb : ∀ a x, ‖g a x‖ ≤ G)
    (hκb : ∀ z, ‖κ z‖ ≤ K * (1 + ‖z‖)) :
    (∫ z, ‖matrixMap (sampledPairDesign (observedPairFeature Y ψ g Φ) w z -
      fullPairDesign (observedPairFeature Y ψ g Φ) w z.1) (WithLp.toLp 2 θ)‖ ^ 2
      ∂μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))) ≤
      featureMomentBound B G K R * (∑ t, w t ^ 2) / P := by
  have hc : 0 ≤ featureMomentBound B G K R := by unfold featureMomentBound; positivity
  apply assembled_design_direction_second_moment hP hL μ _ w θ _ hc
  · intro a t p
    simp_rw [observedPairFeature_realizable Y ψ g Φ θ κ hκ]
    fun_prop
  · intro a t p
    simp_rw [observedPairFeature_realizable Y ψ g Φ θ κ hκ]
    exact (pairFeature_second_moment μ _ _ (hY _ _) (hY _ _) (hiY _ _) (hiY _ _)
      R (hR _ _) (hR _ _) (g a) κ (hg a) hκm (ψ a t) B G K
      hB hG hK (hψ a t) (hgb a) hκb).1
  · intro a t p
    simp_rw [observedPairFeature_realizable Y ψ g Φ θ κ hκ]
    exact (pairFeature_second_moment μ _ _ (hY _ _) (hY _ _) (hiY _ _) (hiY _ _)
      R (hR _ _) (hR _ _) (g a) κ (hg a) hκm (ψ a t) B G K
      hB hG hK (hψ a t) (hgb a) hκb).2

end WMFKI
