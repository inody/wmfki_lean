import Lean_Code.PairRecovery

namespace WMFKI
open MeasureTheory

/--
離散組立に必要な入力をまとめる。SDE強解やテストの微分関係はこの構造では表さない。
特徴や標本残差のモーメントはフィールドにせず、位置モーメントから後で証明する。
-/
structure WeakAssemblyData {Ω F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] [SecondCountableTopology F]
    (μ : Measure Ω) (N T L M : ℕ) where
  X : Ω → Fin N → Fin T → F
  noise : Ω → Fin N → Fin T → F
  φ : Fin L → F → ℝ
  lap : Fin L → F → ℝ
  ψ : Fin L → Fin T → ℝ
  dψ : Fin L → Fin T → ℝ
  g : Fin L → F → F
  Φ : Fin M → F → F
  w : Fin T → ℝ
  σ : ℝ
  RX : ℝ
  Re : ℝ
  B : ℝ
  G : ℝ
  K : ℝ
  Cφ : ℝ
  Cl : ℝ
  hX : ∀ i t, Measurable (fun y => X y i t)
  he : ∀ i t, Measurable (fun y => noise y i t)
  hiX : ∀ i t, Integrable (fun y => ‖X y i t‖ ^ 2) μ
  hie : ∀ i t, Integrable (fun y => ‖noise y i t‖ ^ 2) μ
  hRX0 : 0 ≤ RX
  hRe0 : 0 ≤ Re
  hRX : ∀ i t, (∫ y, ‖X y i t‖ ^ 2 ∂μ) ≤ RX
  hRe : ∀ i t, (∫ y, ‖noise y i t‖ ^ 2 ∂μ) ≤ Re
  hg : ∀ a, Continuous (g a)
  hΦ : ∀ m, Continuous (Φ m)
  hφ : ∀ a, Continuous (φ a)
  hlap : ∀ a, Continuous (lap a)
  hB : 0 ≤ B
  hG : 0 ≤ G
  hK : 0 ≤ K
  hψ : ∀ a t, |ψ a t| ≤ B
  hgb : ∀ a x, ‖g a x‖ ≤ G
  hΦb : ∀ m z, ‖Φ m z‖ ≤ K * (1 + ‖z‖)
  hφb : ∀ a x, |φ a x| ≤ Cφ
  hlapb : ∀ a x, |lap a x| ≤ Cl

namespace WeakAssemblyData
variable {Ω F : Type*} [MeasurableSpace Ω] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  {μ : Measure Ω} {N T L M : ℕ}

def observed (d : WeakAssemblyData (F := F) μ N T L M) := fun y i t => d.X y i t + d.noise y i t
noncomputable def features (d : WeakAssemblyData (F := F) μ N T L M) :=
  observedPairFeature d.observed d.ψ d.g d.Φ
noncomputable def response (d : WeakAssemblyData (F := F) μ N T L M) :=
  observedWeakResponse d.observed d.φ d.lap d.ψ d.dψ d.w d.σ
noncomputable def radius (d : WeakAssemblyData (F := F) μ N T L M) : ℝ := 2 * d.RX + 2 * d.Re
noncomputable def atomBound (d : WeakAssemblyData (F := F) μ N T L M) : ℝ :=
  featureMomentBound d.B d.G d.K d.radius
noncomputable def kernelBound (d : WeakAssemblyData (F := F) μ N T L M) (KT : ℝ) : ℝ :=
  featureMomentBound d.B d.G KT d.radius

theorem radius_nonneg (d : WeakAssemblyData (F := F) μ N T L M) : 0 ≤ d.radius :=
  add_nonneg (mul_nonneg (by norm_num) d.hRX0) (mul_nonneg (by norm_num) d.hRe0)

theorem atomBound_nonneg (d : WeakAssemblyData (F := F) μ N T L M) : 0 ≤ d.atomBound := by
  have hr := d.radius_nonneg
  unfold atomBound featureMomentBound
  positivity

theorem kernelBound_nonneg (d : WeakAssemblyData (F := F) μ N T L M) (KT : ℝ) :
    0 ≤ d.kernelBound KT := by
  have hr := d.radius_nonneg
  unfold kernelBound featureMomentBound
  positivity

theorem position_moments (d : WeakAssemblyData (F := F) μ N T L M) (i : Fin N) (t : Fin T) :
    Measurable (fun y => d.observed y i t) ∧
    Integrable (fun y => ‖d.observed y i t‖ ^ 2) μ ∧
    (∫ y, ‖d.observed y i t‖ ^ 2 ∂μ) ≤ d.radius :=
  observation_second_moment μ _ _ (d.hX i t) (d.he i t) (d.hiX i t) (d.hie i t)
    d.RX d.Re (d.hRX i t) (d.hRe i t)

/-- 回復定理が要求する特徴・応答の正則性と原子モーメントを、入力データから供給。 -/
theorem regular [IsProbabilityMeasure μ] (d : WeakAssemblyData (F := F) μ N T L M) :
    (∀ a m t p, Measurable (fun y => d.features y a m t p)) ∧
    (∀ a m t p, MemLp (fun y => d.features y a m t p) 2 μ) ∧
    (∀ a, Measurable (fun y => d.response y a)) ∧
    (∀ a, MemLp (fun y => d.response y a) 2 μ) ∧
    (∀ a m t p, (∫ y, d.features y a m t p ^ 2 ∂μ) ≤ d.atomBound) := by
  have hp := d.position_moments
  have hf := observedPairFeature_moments μ d.observed d.ψ d.g d.Φ
    (fun i t => (hp i t).1) (fun i t => (hp i t).2.1)
    d.radius (fun i t => (hp i t).2.2) d.hg d.hΦ d.B d.G d.K d.hB d.hG d.hK d.hψ d.hgb d.hΦb
  have hb := observedWeakResponse_regular μ d.observed d.φ d.lap d.ψ d.dψ d.w d.σ
    (fun i t => (hp i t).1) d.hφ d.hlap d.Cφ d.Cl d.hφb d.hlapb
  exact ⟨observedPairFeature_measurable d.observed d.ψ d.g d.Φ (fun i t => (hp i t).1) d.hg d.hΦ,
    (fun a m t p => (hf a m t p).1), (fun a => (hb a).1), (fun a => (hb a).2),
    (fun a m t p => (hf a m t p).2)⟩

/-- 真の相互作用の厳密表現から、選択した列の合成特徴モーメントを導く。 -/
theorem selected_direction_bound [IsProbabilityMeasure μ]
    (d : WeakAssemblyData (F := F) μ N T L M) {s : ℕ} (e : Fin s → Fin M)
    (θ : Fin s → ℝ) (κ : F → F) (hκ : ∀ z, ∑ j, θ j • d.Φ (e j) z = κ z)
    (hκm : Continuous κ) (KT : ℝ) (hKT : 0 ≤ KT)
    (hκb : ∀ z, ‖κ z‖ ≤ KT * (1 + ‖z‖)) (a : Fin L) (t : Fin T) (p : OrderedPair N) :
    (∫ y, (∑ j, θ j * d.features y a (e j) t p) ^ 2 ∂μ) ≤ d.kernelBound KT := by
  have hp := d.position_moments
  change (∫ y, (∑ j, θ j * observedPairFeature d.observed d.ψ d.g (fun j => d.Φ (e j)) y a j t p) ^ 2 ∂μ) ≤ _
  simp_rw [observedPairFeature_realizable d.observed d.ψ d.g (fun j => d.Φ (e j)) θ κ hκ]
  exact (pairFeature_second_moment μ _ _ (hp _ _).1 (hp _ _).1 (hp _ _).2.1 (hp _ _).2.1
    d.radius (hp _ _).2.2 (hp _ _).2.2 (d.g a) κ (d.hg a) hκm (d.ψ a t) d.B d.G KT
    d.hB d.hG hKT (d.hψ a t) (d.hgb a) hκb).2

/-- 加法観測と弱形式の有限和から、既知supportのOLS回復までを結合する。 -/
theorem oracle_recovery [IsProbabilityMeasure μ] (d : WeakAssemblyData (F := F) μ N T L M)
    {P s : ℕ} [Fact (2 ≤ N)] (hP : 0 < P) (hL : 0 < L)
    (A : Matrix (Fin L) (Fin M) ℝ) (e : Fin s → Fin M) (he : Function.Injective e)
    (θ : Fin s → ℝ) (κ : F → F) (hκ : ∀ z, ∑ j, θ j • d.Φ (e j) z = κ z)
    (hκm : Continuous κ) (KT : ℝ) (hKT : 0 ≤ KT) (hκb : ∀ z, ‖κ z‖ ≤ KT * (1 + ‖z‖))
    (D0 V0 γ δ ε : ℝ)
    (hD : (∫ y, frobenius (fullPairDesign d.features d.w y - A) ^ 2 ∂μ) ≤ D0)
    (hV : (∫ y, ‖fullRegressionResidual (selectPairFeatures d.features e) d.w d.response θ y‖ ^ 2 ∂μ) ≤ V0)
    (hγ : 0 < γ) (hδ : 0 < δ) (hε : 0 < ε) (hprob : δ + ε < 1)
    (hA : LowerBound (matrixMap (A.submatrix id e)) γ)
    (hsmall : designSamplingBudget M P d.w D0 d.atomBound ≤ δ * γ ^ 2 / 4) :
    ∃ G : Set (Ω × ((Fin T × Fin P) → OrderedPair N)), MeasurableSet G ∧
      1 - δ - ε ≤ (μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))).real G ∧
      ∀ z ∈ G, ‖moorePenrose (matrixMap ((sampledPairDesign d.features d.w z).submatrix id e))
        (WithLp.toLp 2 (d.response z.1)) - WithLp.toLp 2 θ‖ ^ 2 ≤
        4 * residualSamplingBudget P d.w V0 (d.kernelBound KT) / (ε * γ ^ 2) := by
  obtain ⟨hm, hh, hbm, hb, hCA⟩ := d.regular
  exact sampled_oracle_recovery hP hL μ d.features d.w d.response θ A e he hm hh hbm hb
    D0 V0 d.atomBound (d.kernelBound KT) γ δ ε d.atomBound_nonneg (d.kernelBound_nonneg KT)
    hD hV hCA (d.selected_direction_bound e θ κ hκ hκm KT hKT hκb)
    hγ hδ hε hprob hA hsmall

/-- 加法観測と弱形式の有限和から、同じ生デザインによるLASSO回復までを結合する。 -/
theorem lasso_recovery [IsProbabilityMeasure μ] (d : WeakAssemblyData (F := F) μ N T L M)
    {P : ℕ} [Fact (2 ≤ N)] (hP : 0 < P) (hL : 0 < L)
    (A : Matrix (Fin L) (Fin M) ℝ) (S : Finset (Fin M)) (θ : Fin M → ℝ)
    (κ : F → F) (hκ : ∀ z, ∑ m, θ m • d.Φ m z = κ z)
    (hκm : Continuous κ) (KT : ℝ) (hKT : 0 ≤ KT) (hκb : ∀ z, ‖κ z‖ ≤ KT * (1 + ‖z‖))
    (D0 V0 γ R δ ε lam : ℝ)
    (hD : (∫ y, frobenius (fullPairDesign d.features d.w y - A) ^ 2 ∂μ) ≤ D0)
    (hV : (∫ y, ‖fullRegressionResidual d.features d.w d.response θ y‖ ^ 2 ∂μ) ≤ V0)
    (hγ : 0 < γ) (hR : 0 ≤ R) (hδ : 0 < δ) (hε : 0 < ε) (hprob : δ + ε < 1)
    (hlam : 0 < lam) (hsupp : ∀ i ∉ S, θ i = 0)
    (hA : ConeLowerBound (matrixMap A) S γ) (hcol : ColumnBound (matrixMap A) R)
    (hsmall : designSamplingBudget M P d.w D0 d.atomBound ≤ δ * γ ^ 2 / 4)
    (hpen : 2 * (R + γ / 2) * Real.sqrt (residualSamplingBudget P d.w V0 (d.kernelBound KT) / ε) ≤ lam) :
    ∃ G : Set (Ω × ((Fin T × Fin P) → OrderedPair N)), MeasurableSet G ∧
      1 - δ - ε ≤ (μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))).real G ∧
      ∀ z ∈ G,
        SparseCone S (lassoEstimator (matrixMap (sampledPairDesign d.features d.w z))
          (WithLp.toLp 2 (d.response z.1)) lam hlam - WithLp.toLp 2 θ) ∧
        ‖lassoEstimator (matrixMap (sampledPairDesign d.features d.w z))
          (WithLp.toLp 2 (d.response z.1)) lam hlam - WithLp.toLp 2 θ‖ ^ 2 ≤
            144 * (S.card : ℝ) * lam ^ 2 / γ ^ 4 := by
  obtain ⟨hm, hh, hbm, hb, hCA⟩ := d.regular
  exact sampled_lasso_recovery hP hL μ d.features d.w d.response θ A S hm hh hbm hb
    D0 V0 d.atomBound (d.kernelBound KT) γ R δ ε lam d.atomBound_nonneg (d.kernelBound_nonneg KT)
    hD hV hCA (d.selected_direction_bound id θ κ hκ hκm KT hKT hκb)
    hγ hR hδ hε hprob hlam hsupp hA hcol hsmall hpen

/-- 加法観測と弱形式の有限和から、任意のLASSO最小化解へ回復評価を適用する。 -/
theorem lasso_recovery_of_minimizer [IsProbabilityMeasure μ]
    (d : WeakAssemblyData (F := F) μ N T L M)
    {P : ℕ} [Fact (2 ≤ N)] (hP : 0 < P) (hL : 0 < L)
    (A : Matrix (Fin L) (Fin M) ℝ) (S : Finset (Fin M)) (θ : Fin M → ℝ)
    (θhat : Ω × ((Fin T × Fin P) → OrderedPair N) → Coeff M)
    (κ : F → F) (hκ : ∀ z, ∑ m, θ m • d.Φ m z = κ z)
    (hκm : Continuous κ) (KT : ℝ) (hKT : 0 ≤ KT) (hκb : ∀ z, ‖κ z‖ ≤ KT * (1 + ‖z‖))
    (D0 V0 γ R δ ε lam : ℝ)
    (hD : (∫ y, frobenius (fullPairDesign d.features d.w y - A) ^ 2 ∂μ) ≤ D0)
    (hV : (∫ y, ‖fullRegressionResidual d.features d.w d.response θ y‖ ^ 2 ∂μ) ≤ V0)
    (hγ : 0 < γ) (hR : 0 ≤ R) (hδ : 0 < δ) (hε : 0 < ε) (hprob : δ + ε < 1)
    (hlam : 0 < lam) (hsupp : ∀ i ∉ S, θ i = 0)
    (hA : ConeLowerBound (matrixMap A) S γ) (hcol : ColumnBound (matrixMap A) R)
    (hsmall : designSamplingBudget M P d.w D0 d.atomBound ≤ δ * γ ^ 2 / 4)
    (hpen : 2 * (R + γ / 2) * Real.sqrt (residualSamplingBudget P d.w V0 (d.kernelBound KT) / ε) ≤ lam)
    (hfit : ∀ z, IsLasso (matrixMap (sampledPairDesign d.features d.w z))
      (WithLp.toLp 2 (d.response z.1)) lam (θhat z)) :
    ∃ G : Set (Ω × ((Fin T × Fin P) → OrderedPair N)), MeasurableSet G ∧
      1 - δ - ε ≤ (μ.prod (independentDraws (Fin T × Fin P) (OrderedPair N))).real G ∧
      ∀ z ∈ G, SparseCone S (θhat z - WithLp.toLp 2 θ) ∧
        ‖θhat z - WithLp.toLp 2 θ‖ ^ 2 ≤
          144 * (S.card : ℝ) * lam ^ 2 / γ ^ 4 := by
  obtain ⟨hm, hh, hbm, hb, hCA⟩ := d.regular
  exact sampled_lasso_recovery_of_minimizer hP hL μ d.features d.w d.response θ A S θhat hm hh hbm hb
    D0 V0 d.atomBound (d.kernelBound KT) γ R δ ε lam d.atomBound_nonneg (d.kernelBound_nonneg KT)
    hD hV hCA (d.selected_direction_bound id θ κ hκ hκm KT hKT hκb)
    hγ hR hδ hε hprob hlam hsupp hA hcol hsmall hpen hfit

end WeakAssemblyData
end WMFKI
