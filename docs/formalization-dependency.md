# WMFKI形式化：主要宣言の依存グラフ

この図は、新規437宣言のうち、数学的な流れを把握するための主要宣言だけを表示します。完全な監査対象一覧は [`WMFKI_Stochastic/Audit.lean`](../WMFKI_Stochastic/Audit.lean) と [`SOURCE_MANIFEST.json`](../WMFKI_Stochastic/SOURCE_MANIFEST.json) にあります。

- 青：Leanが構成・証明した宣言
- 紫：既存production定義・回復APIとの橋
- 緑：最終出力
- 黄：適用時に残す明示的仮定
- 灰：今回の対象外

```mermaid
flowchart TB
  classDef proved fill:#e9f6fa,stroke:#176b87,color:#17324a,stroke-width:1.5px
  classDef bridge fill:#efedff,stroke:#5747b7,color:#2f285f,stroke-width:1.5px
  classDef result fill:#e8f7ef,stroke:#26734d,color:#16452f,stroke-width:2px
  classDef assumed fill:#fff4df,stroke:#b56a00,color:#684000,stroke-width:1.5px
  classDef outside fill:#eef1f5,stroke:#7a8494,color:#4f5968,stroke-dasharray:5 4

  subgraph I[0. 原始入力]
    I0["π, P：確率測度"]:::assumed
    I1["ξ：可測L⁴初期値"]:::assumed
    I2["W：独立Brownian族"]:::assumed
    I3["K：globally Lipschitz"]:::assumed
    I4["φ：有界C³試験 / ψ：C¹時間試験"]:::assumed
    I5["辞書atomと真の係数表現"]:::assumed
  end

  subgraph M[1. 平均場解の構成]
    M0["lawDrift / picardStep"]:::proved
    M1["picardIter → picardLimit"]:::proved
    M2["FiniteL4Paths"]:::proved
    M3["exists_unique_product_adapted_mean_field"]:::proved
  end

  subgraph C[2. コピーと実粒子]
    C0["exists_iid_nonlinear_family"]:::proved
    C1["ArrayNonlinearFamily"]:::proved
    C2["exists_synchronous_particle_family"]:::proved
    C3["SynchronousParticlePair"]:::proved
  end

  subgraph S[3. 同期第4モーメント率]
    S0["iid_fluctuation_fourth"]:::proved
    S1["finite_integral_fourth_moment"]:::proved
    S2["synchronous_path_envelope"]:::proved
    S3["exists_synchronous_fourth_rate\nE‖Xᵢᴺ−Yᵢ‖⁴ ≤ C/N²"]:::proved
  end

  subgraph D[4A. 設計 D₀ の枝]
    D0["weak_pair_feature_coupling\n依存L⁴×L⁴"]:::proved
    D1["exists_continuous_design_coupling"]:::proved
    D2["time_pair_kernel_moments"]:::proved
    D3["copy_design_identification"]:::proved
    D4["iid_pair_matrix_frobenius_rate"]:::proved
    D5["population_design_identification"]:::proved
    D6["exists_continuous_population_rate\nE‖Aᴺ−A∞‖F² ≤ CM/N"]:::proved
  end

  subgraph V[4B. 残差 V₀ の枝]
    V0["weighted_particle_ito"]:::proved
    V1["weighted_particle_weak_balance"]:::proved
    V2["weak_residual_vector_energy\n∝ σ²/N"]:::proved
    V3["independent_residual_from_position"]:::proved
  end

  subgraph O[5. 観測・求積]
    O0["independentObservationSamples\n雑音対潜在系のみ独立"]:::proved
    O1["observed_dictionary_moment"]:::proved
    O2["exists_observed_full_design_rate"]:::proved
    O3["exists_joint_weak_budgets\nD₀,V₀を同じX上で構成"]:::proved
    Q0["設計RMS求積 ≤ Qe"]:::assumed
    Q1["応答RMS求積 ≤ Qe"]:::assumed
  end

  subgraph B[6. production定義との橋]
    B0["continuous_design_bridge"]:::bridge
    B1["discrete_design_bridge\n= fullPairDesign"]:::bridge
    B2["weak_response_bridge\n= observedWeakResponse"]:::bridge
    B3["full_residual_bridge\n= fullRegressionResidual"]:::bridge
    B4["genuineWeakAssembly"]:::bridge
  end

  subgraph R[7. ランダムペア回復]
    R0["WeakAssemblyData.oracle_recovery"]:::bridge
    R1["WeakAssemblyData.lasso_recovery\n/ lasso_recovery_of_minimizer"]:::bridge
    R2["recover_genuine_assembly"]:::bridge
    R3["RecoveryCertificate"]:::result
    R4["exists_particle_weak_recovery"]:::result
    A0["選択列lower bound / cone lower bound"]:::assumed
    A1["sampling smallness, δ, ε"]:::assumed
    A2["column bound / λ条件"]:::assumed
  end

  I0 --> M0
  I1 --> M0
  I2 --> M3
  I3 --> M0
  M0 --> M1 --> M2 --> M3
  M3 --> C0 --> C1
  I2 --> C2
  I3 --> C2
  C1 --> C2 --> C3

  C3 --> S0
  S0 --> S1 --> S2 --> S3

  I4 --> D0
  I5 --> D0
  S3 --> D0 --> D1
  C1 --> D2
  D2 --> D3
  C1 --> D4
  D3 --> D4
  D4 --> D6
  D5 --> D6
  D1 --> D6

  C3 --> V0 --> V1 --> V2 --> V3
  I4 --> V0
  I3 --> V0

  D6 --> O2
  O0 --> O1 --> O2
  Q0 --> O2
  V3 --> O3
  O2 --> O3
  Q1 --> O3

  O2 --> B0
  O2 --> B1
  O3 --> B2
  O3 --> B3
  B0 --> B4
  B1 --> B4
  B2 --> B4
  B3 --> B4

  B4 --> R2
  O3 --> R2
  R0 --> R2
  R1 --> R2
  A0 --> R0
  A0 --> R1
  A1 --> R0
  A1 --> R1
  A2 --> R1
  R2 --> R3 --> R4

  X0["任意の既存joint realizationへの移送"]:::outside
  X1["無限時間一様率"]:::outside
  X2["数値ソルバー / support回復"]:::outside
  R4 -. 対象外 .-> X0
  R4 -. 対象外 .-> X1
  R4 -. 対象外 .-> X2

  click M1 "../WMFKI_Stochastic/MeanFieldPicardLimit.lean" "Picard極限"
  click M3 "../WMFKI_Stochastic/MeanFieldWellPosedness.lean" "平均場の適合性と一意性"
  click C0 "../WMFKI_Stochastic/NonlinearCopiesFromInputs.lean" "iidコピー"
  click C2 "../WMFKI_Stochastic/SynchronousArrayEquation.lean" "同期粒子系"
  click S3 "../WMFKI_Stochastic/SynchronousFourthRate.lean" "同期率"
  click D1 "../WMFKI_Stochastic/ActualDesignCoupling.lean" "特徴設計カップリング"
  click D2 "../WMFKI_Stochastic/TimePairKernel.lean" "実時間核"
  click D4 "../WMFKI_Stochastic/IIDPairMatrix.lean" "iidペアP2"
  click D5 "../WMFKI_Stochastic/PopulationFeatureLaw.lean" "母集団同定"
  click D6 "../WMFKI_Stochastic/ContinuousPopulationRate.lean" "連続設計率"
  click V2 "../WMFKI_Stochastic/EmpiricalResidualEnergy.lean" "弱残差エネルギー"
  click V3 "../WMFKI_Stochastic/IndependentResidualFromPosition.lean" "観測・求積V0"
  click O2 "../WMFKI_Stochastic/ActualObservedDesign.lean" "観測D0"
  click O3 "../WMFKI_Stochastic/JointWeakBudgets.lean" "同一実現D0/V0"
  click B1 "../WMFKI_Stochastic/DiscreteDesignBridge.lean" "fullPairDesignとの同定"
  click B2 "../WMFKI_Stochastic/WeakResponseBridge.lean" "observedWeakResponseとの同定"
  click B4 "../WMFKI_Stochastic/GenuineWeakAssembly.lean" "WeakAssemblyData構成"
  click R2 "../WMFKI_Stochastic/RecoveryCertificate.lean" "production回復API接続"
  click R4 "../WMFKI_Stochastic/PrimitiveRecovery.lean" "公開終点"
```

## 原稿とLeanの対応

| 原稿上の役割 | 主要Lean宣言 | ファイル |
|---|---|---|
| 平均場方程式の構成・一意性 | `exists_unique_product_adapted_mean_field` | [`MeanFieldWellPosedness.lean`](../WMFKI_Stochastic/MeanFieldWellPosedness.lean) |
| iid非線形コピー | `exists_iid_nonlinear_family` | [`NonlinearCopiesFromInputs.lean`](../WMFKI_Stochastic/NonlinearCopiesFromInputs.lean) |
| 同期粒子系 | `exists_synchronous_particle_family` | [`SynchronousArrayEquation.lean`](../WMFKI_Stochastic/SynchronousArrayEquation.lean) |
| 同期第4モーメント率 | `exists_synchronous_fourth_rate` | [`SynchronousFourthRate.lean`](../WMFKI_Stochastic/SynchronousFourthRate.lean) |
| 特徴安定性 | `exists_continuous_design_coupling` | [`ActualDesignCoupling.lean`](../WMFKI_Stochastic/ActualDesignCoupling.lean) |
| iidペア設計のP2評価 | `iid_pair_matrix_frobenius_rate` | [`IIDPairMatrix.lean`](../WMFKI_Stochastic/IIDPairMatrix.lean) |
| 実母集団設計との同定 | `population_design_identification` | [`PopulationFeatureLaw.lean`](../WMFKI_Stochastic/PopulationFeatureLaw.lean) |
| 連続設計収束（4.9型） | `exists_continuous_population_rate` | [`ContinuousPopulationRate.lean`](../WMFKI_Stochastic/ContinuousPopulationRate.lean) |
| 観測を含むD₀ | `exists_observed_full_design_rate` | [`ActualObservedDesign.lean`](../WMFKI_Stochastic/ActualObservedDesign.lean) |
| 同じ実現上のD₀/V₀（4.8–4.9型） | `exists_joint_weak_budgets` | [`JointWeakBudgets.lean`](../WMFKI_Stochastic/JointWeakBudgets.lean) |
| production回復APIへの接続 | `recover_genuine_assembly` | [`RecoveryCertificate.lean`](../WMFKI_Stochastic/RecoveryCertificate.lean) |
| ランダムペア回復（4.12型） | `exists_particle_weak_recovery` | [`PrimitiveRecovery.lean`](../WMFKI_Stochastic/PrimitiveRecovery.lean) |

## 最終定理を読むときの要点

`exists_particle_weak_recovery`の量化順序は次です。

```text
原始入力
  → ∃ Y, R, Rpos, CA, CV
  → ∀ N > 0, ∃ BN, X
  → 任意の有限グリッド・観測雑音・e・q
  → D₀評価 ∧ V₀評価 ∧ RecoveryCertificate
```

したがって、`CA`や`CV`は`N`ごとに選ばれていません。また、`D₀`・`V₀`や未知の軌道を原始仮定として受け取る定理ではありません。`RecoveryCertificate.lasso_any`は、LASSO最小化条件を点ごとに満たす任意の選択に同じ良事象と係数評価を適用し、その選択自体の可測性は要求しません。

## 明示的仮定と対象外

### 明示的仮定

- 設計・応答のRMS求積精度
- 真の核の辞書による厳密表現
- OLSの選択母集団設計lower bound
- LASSOのcone lower boundとcolumn bound
- sampling smallness、`δ, ε`、正のpenaltyとpenalty下限

### 対象外

- 任意の既存joint realizationへの普遍移送
- コピーの新しい粒子filtrationへの追加適合性
- 無限時間一様率
- 推定量自体の可測性
- 数値ソルバーの正当性
- support回復

## 表示方法

GitHubやMermaid対応Markdownプレビューでは、このファイルを開くだけで図が描画されます。概念中心の1ページ版は [`formalization-map.html`](formalization-map.html) です。
