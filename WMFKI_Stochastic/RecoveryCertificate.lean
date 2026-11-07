import WMFKI_Stochastic.JointWeakBudgets

open MeasureTheory Set
open WMFKIExternalProbe WMFKI
namespace WMFKIJointAssembly

/-- 本番APIの二回復法の結論。これは原始仮定ではなく、下で構成する出力命題。
    非退化性・許容誤差・penalty条件を明示し、係数回復とsupport回復を区別する。 -/
structure RecoveryCertificate {Ω F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure Ω) (N nt nr nc : ℕ)
    (h : Ω → Fin nr → Fin nc → Fin nt → OrderedPair N → ℝ)
    (b : Ω → Fin nr → ℝ) (w : Fin nt → ℝ)
    (θ : EuclideanSpace ℝ (Fin nc)) (A : Matrix (Fin nr) (Fin nc) ℝ)
    (D0 V0 CA CK : ℝ) (atom : Fin nc → F → F) (K : F → F) : Prop where
  lasso : ∀ (np : ℕ), 0 < np → ∀ (hN : 2 ≤ N),
    letI : Fact (2 ≤ N) := ⟨hN⟩
    ∀ (S : Finset (Fin nc)) (γ R δ ε lam : ℝ),
    0 < γ → 0 ≤ R → 0 < δ → 0 < ε → δ+ε < 1 → ∀ (hlam : 0 < lam),
    (∀ i ∉ S, θ i = 0) → ConeLowerBound (matrixMap A) S γ → ColumnBound (matrixMap A) R →
    designSamplingBudget nc np w D0 CA ≤ δ*γ^2/4 →
    2*(R+γ/2)*Real.sqrt (residualSamplingBudget np w V0 CK/ε) ≤ lam →
    ∃ G : Set (Ω × ((Fin nt × Fin np) → OrderedPair N)), MeasurableSet G ∧
      1-δ-ε ≤ (μ.prod (independentDraws (Fin nt × Fin np) (OrderedPair N))).real G ∧
      ∀ z ∈ G, SparseCone S (lassoEstimator (matrixMap (sampledPairDesign h w z)) (WithLp.toLp 2 (b z.1)) lam hlam-θ) ∧
        ‖lassoEstimator (matrixMap (sampledPairDesign h w z)) (WithLp.toLp 2 (b z.1)) lam hlam-θ‖^2 ≤
          144*(S.card : ℝ)*lam^2/γ^4
  lasso_any : ∀ (np : ℕ), 0 < np → ∀ (hN : 2 ≤ N),
    letI : Fact (2 ≤ N) := ⟨hN⟩
    ∀ (S : Finset (Fin nc)) (γ R δ ε lam : ℝ),
    0 < γ → 0 ≤ R → 0 < δ → 0 < ε → δ+ε < 1 → ∀ (_hlam : 0 < lam),
    (∀ i ∉ S, θ i = 0) → ConeLowerBound (matrixMap A) S γ → ColumnBound (matrixMap A) R →
    designSamplingBudget nc np w D0 CA ≤ δ*γ^2/4 →
    2*(R+γ/2)*Real.sqrt (residualSamplingBudget np w V0 CK/ε) ≤ lam →
    ∀ (θhat : Ω × ((Fin nt × Fin np) → OrderedPair N) → Coeff nc),
    (∀ z, IsLasso (matrixMap (sampledPairDesign h w z)) (WithLp.toLp 2 (b z.1)) lam (θhat z)) →
    ∃ G : Set (Ω × ((Fin nt × Fin np) → OrderedPair N)), MeasurableSet G ∧
      1-δ-ε ≤ (μ.prod (independentDraws (Fin nt × Fin np) (OrderedPair N))).real G ∧
      ∀ z ∈ G, SparseCone S (θhat z-θ) ∧
        ‖θhat z-θ‖^2 ≤ 144*(S.card : ℝ)*lam^2/γ^4
  oracle : ∀ (np s : ℕ), 0 < np → ∀ (hN : 2 ≤ N),
    letI : Fact (2 ≤ N) := ⟨hN⟩
    ∀ (sel : Fin s → Fin nc), Function.Injective sel →
    ∀ (θS : Fin s → ℝ), (∀ x, ∑ j, θS j • atom (sel j) x = K x) →
    ∀ (γ δ ε : ℝ), 0 < γ → 0 < δ → 0 < ε → δ+ε < 1 →
    LowerBound (matrixMap (A.submatrix id sel)) γ → designSamplingBudget nc np w D0 CA ≤ δ*γ^2/4 →
    ∃ G : Set (Ω × ((Fin nt × Fin np) → OrderedPair N)), MeasurableSet G ∧
      1-δ-ε ≤ (μ.prod (independentDraws (Fin nt × Fin np) (OrderedPair N))).real G ∧
      ∀ z ∈ G, ‖moorePenrose (matrixMap ((sampledPairDesign h w z).submatrix id sel))
        (WithLp.toLp 2 (b z.1))-WithLp.toLp 2 θS‖^2 ≤
          4*residualSamplingBudget np w V0 CK/(ε*γ^2)

/-- 同じ真の核の二つの厳密表現は、実際の全ペア残差を同じにする。
    選択列でのOLSにも、同じ実粒子上で得たV0を使える。 -/
theorem selected_residual_eq {Ω : Type*} (nr N nt d nc s : ℕ) (σ : ℝ) (w τ : Fin nt → ℝ)
    (φ : Fin nr → EuclideanSpace ℝ (Fin d) → ℝ) (ψ : Fin nr → ℝ → ℝ)
    (atom : Fin nc → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin nc)) (hReal : ∀ x, ∑ m, θ m • atom m x = K x)
    (sel : Fin s → Fin nc) (θS : Fin s → ℝ) (hS : ∀ x, ∑ j, θS j • atom (sel j) x = K x)
    (x : Fin nt → Fin N → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    let h := observedPairFeature (fun ω i t => x t i ω) (fun a t => ψ a (τ t)) (fun a => gradient (φ a)) atom
    let b := observedWeakResponse (fun ω i t => x t i ω) φ (fun a => Laplacian.laplacian (φ a))
      (fun a t => ψ a (τ t)) (fun a t => deriv (ψ a) (τ t)) w σ
    fullRegressionResidual (selectPairFeatures h sel) w b θS ω = fullRegressionResidual h w b θ ω := by
  have hs := full_residual_bridge nr N nt d s σ w τ φ ψ (fun j => atom (sel j)) (WithLp.toLp 2 θS) x ω
  have hf := full_residual_bridge nr N nt d nc σ w τ φ ψ atom θ x ω
  dsimp only
  change fullRegressionResidual (observedPairFeature (fun ω i t => x t i ω) (fun a t => ψ a (τ t))
    (fun a => gradient (φ a)) (fun j => atom (sel j))) w _ (WithLp.toLp 2 θS) ω = _
  rw [← hs,← hf,discrete_dictionary_realizable nr N nt d s w τ (fun j => atom (sel j)) (WithLp.toLp 2 θS) K hS,
    discrete_dictionary_realizable nr N nt d nc w τ atom θ K hReal]

/-- ここで受けるD0,V0は原始終点で実際の同じSDEから供給する中間接口。
    位置・微分・特徴・応答の実定義を固定した本番WeakAssemblyDataを構成して二法を呼ぶ。 -/
theorem recover_genuine_assembly {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N nt d nr nc : ℕ) (hnr : 0 < nr)
    (R q : ℝ) (hR : 0 ≤ R) (hq : 0 ≤ q)
    (O : ObservationSamples (E := EuclideanSpace ℝ (Fin d)) μ N nt R q)
    (σ : ℝ) (w τ : Fin nt → ℝ) (ψ : Fin nr → ℝ → ℝ)
    (φ : Fin nr → EuclideanSpace ℝ (Fin d) → ℝ)
    (atom : Fin nc → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (B G H J C Cφ : ℝ) (hB : 0 ≤ B) (hG : 0 ≤ G) (hC : 0 ≤ C)
    (hφ : ∀ a, C3TestBounds d (φ a) G H J) (hφb : ∀ a x, |φ a x| ≤ Cφ)
    (hψ : ∀ a t, |ψ a (τ t)| ≤ B) (hAtom : ∀ m, Continuous (atom m))
    (hg : ∀ m x, ‖atom m x‖ ≤ C*(1+‖x‖))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : Continuous K)
    (KT : ℝ) (hKT : 0 ≤ KT) (hKg : ∀ x, ‖K x‖ ≤ KT*(1+‖x‖))
    (θ : EuclideanSpace ℝ (Fin nc)) (hReal : ∀ x, ∑ m, θ m • atom m x = K x)
    (A : Matrix (Fin nr) (Fin nc) ℝ) (D0 V0 : ℝ) :
    let Obs := fun z i t => O.pos t i z+O.noise t i z
    let h := observedPairFeature Obs (fun a t => ψ a (τ t)) (fun a => gradient (φ a)) atom
    let b := observedWeakResponse Obs φ (fun a => Laplacian.laplacian (φ a))
      (fun a t => ψ a (τ t)) (fun a t => deriv (ψ a) (τ t)) w σ
    (∫ z, frobenius (fullPairDesign h w z-A)^2 ∂μ) ≤ D0 →
    (∫ z, ‖fullRegressionResidual h w b θ z‖^2 ∂μ) ≤ V0 →
    RecoveryCertificate μ N nt nr nc h b w θ A D0 V0
      (featureMomentBound B G C (2*R+2*q)) (featureMomentBound B G KT (2*R+2*q)) atom K := by
  dsimp only
  intro hD hV
  let data := genuineWeakAssembly μ N nt d nr nc R q hR hq O σ w τ ψ φ atom B G H J C Cφ hB hG hC hφ hφb hψ hAtom hg
  constructor
  · intro np hnp hN
    let : Fact (2 ≤ N) := ⟨hN⟩
    dsimp only
    intro S γ Rcol δ ε lam hγ hRc hδ hε hprob hlam hsupp hA hcol hsmall hpen
    exact data.lasso_recovery hnp hnr A S θ K hReal hK KT hKT hKg
      D0 V0 γ Rcol δ ε lam hD hV hγ hRc hδ hε hprob hlam hsupp hA hcol hsmall hpen
  · intro np hnp hN
    let : Fact (2 ≤ N) := ⟨hN⟩
    dsimp only
    intro S γ Rcol δ ε lam hγ hRc hδ hε hprob hlam hsupp hA hcol hsmall hpen θhat hfit
    exact data.lasso_recovery_of_minimizer hnp hnr A S θ θhat K hReal hK KT hKT hKg
      D0 V0 γ Rcol δ ε lam hD hV hγ hRc hδ hε hprob hlam hsupp hA hcol hsmall hpen hfit
  · intro np s hnp hN
    let : Fact (2 ≤ N) := ⟨hN⟩
    dsimp only
    intro sel hsel θS hS γ δ ε hγ hδ hε hprob hA hsmall
    have hVs : (∫ z, ‖fullRegressionResidual (selectPairFeatures data.features sel) w data.response θS z‖^2 ∂μ) ≤ V0 := by
      have he z : fullRegressionResidual (selectPairFeatures data.features sel) w data.response θS z =
          fullRegressionResidual data.features w data.response θ z :=
        selected_residual_eq nr N nt d nc s σ w τ φ ψ atom K θ hReal sel θS hS
          (fun t i z => O.pos t i z+O.noise t i z) z
      simp_rw [he]
      exact hV
    exact data.oracle_recovery hnp hnr A sel hsel θS K hS hK KT hKT hKg
      D0 V0 γ δ ε hD hVs hγ hδ hε hprob hA hsmall

end WMFKIJointAssembly
