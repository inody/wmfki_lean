# WMFKI Lean Formalization

This repository contains the Lean 4 formalization accompanying *Mesh-Free
Weak-Form Regression for Learning Interaction Kernels from Particle
Trajectories*. Its main public endpoint is

```lean
WMFKIJointAssembly.exists_particle_weak_recovery
```

Starting from primitive initial random variables and independent Brownian
inputs, the formalization constructs the mean-field and interacting particle
systems, proves the design and residual moment bounds, and connects them to
oracle OLS and LASSO coefficient-recovery certificates. Quadrature accuracy,
identifiability, sampling-smallness, probability-tolerance, and LASSO-penalty
conditions remain explicit assumptions. The result concerns coefficient
recovery, not support recovery.

The audited project contains 563 declarations and 32 examples, with no
project-specific axioms and no `sorry`. Its permitted transitive dependencies
are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. For a clean
verification run:

```bash
./scripts/setup.sh
python3 scripts/verify.py --clean
```

See [`docs/formalization-map-en.html`](docs/formalization-map-en.html) for a
one-page overview and
[`docs/formalization-dependency-en.md`](docs/formalization-dependency-en.md)
for the theorem-dependency map. The project-level source has no selected
license; the pinned third-party stochastic-analysis dependency and its
Apache-2.0 license are documented in
[`WMFKI_Stochastic/THIRD_PARTY.md`](WMFKI_Stochastic/THIRD_PARTY.md).

## 日本語概要

### 現在の結果

**有限時間の原始粒子入力から、同じ実現上の設計・残差評価を経て、ランダムペア既知support OLSおよびLASSO回復へ接続しました。**

正式な入口は次の定理です。

```lean
WMFKIJointAssembly.exists_particle_weak_recovery
```

この定理は、初期乱数と独立Brownian入力から平均場過程と相互作用粒子系を構成し、同期第4モーメント率、実時間特徴核、母集団設計、観測摂動を同じ構成上で扱います。供給されたRMS求積精度を加え、

```text
D0 ≤ CA (1/N + e + q),
V0 ≤ CV (σ²/N + e + q)
```

を導きます。さらに既存の本番APIへ接続し、母集団設計の識別条件、sampling smallness、確率許容値、LASSO penalty条件の下でOLS・LASSOの係数回復証明書を返します。

ここで `e` は原稿の `Δt^(2p)`、`q` は観測誤差の二乗平均予算に対応します。RMS求積精度、識別可能性・restricted-cone geometry、smallness、penalty条件そのものは原稿どおり明示的な仮定です。係数回復をsupport回復とは同一視しません。

実装は二つのライブラリに分かれます。

- `Lean_Code/`：行列、抽出、OLS/LASSOおよび回復API。既存126宣言・26例。
- `WMFKI_Stochastic/`：粒子SDEから上記APIまでの接続。新規437宣言・6例。

合計563宣言について推移的な公理依存を監査し、32例を再検証します。プロジェクト固有公理0、`sorry` 0です。

まず全体像をつかむには、次の可視化を参照してください。

- [`docs/formalization-map.html`](docs/formalization-map.html)：概念中心の1ページ地図（日本語）
- [`docs/formalization-map-en.html`](docs/formalization-map-en.html)：共著者向け英語版
- [`docs/formalization-dependency.md`](docs/formalization-dependency.md)：主要宣言のMermaid依存グラフと原稿対応表（日本語）
- [`docs/formalization-dependency-en.md`](docs/formalization-dependency-en.md)：同じ依存グラフと対応表の英語版

## 検証済みの内容

| 項目 | 内容 |
|---|---|
| 粒子SDE | 独立初期乱数・Brownian入力から実際の有限粒子解を構成し、同じ原始入力上に平均場コピーを実現 |
| 平均場方程式 | Picard構成、有限L4経路クラス内の一意性、適合性、有限時間整合性、独立コピー族 |
| 同期率 | 線形成長Lipschitz核について、各粒子の第4モーメント誤差をC/N²で評価。定数は全Nより先に選択 |
| 母集団設計 | 実時間積分核の可測性・L2性とFubini条件を証明し、実周辺法則μ_t×μ_tの設計へ同定 |
| 連続設計D0 | 粒子対コピーの依存安全なL4×L4評価とiidペアP2を結合し、Frobenius二乗誤差O(M/N) |
| 観測・求積D0 | 偏りと内部依存を許す観測雑音、および供給されたRMS求積予算からCA(1/N+e+q) |
| 同一実現V0 | 実粒子SDEの弱残差、観測摂動、応答求積を同じX上で結合しCV(σ²/N+e+q) |
| 本番定義対応 | 連続・離散設計、`fullPairDesign`、`observedWeakResponse`、`fullRegressionResidual`を厳密同定 |
| 原始回復終点 | 同じY,X,観測系のD0/V0を`WeakAssemblyData`へ渡し、既知support OLSとLASSOへ接続 |
| 行列とノルム | Euclidean空間への写像、作用素ノルム≤Frobenius、active列制限、転置と随伴、成分ベクトルとのノルム同一性 |
| 二乗平均の移行 | Frobenius二乗の可積分性から作用素ノルム二乗の可積分性と積分の上界 |
| Moore–Penrose | 四つの作用素等式、有限次元係数空間での存在、その推定量の最小化性。全列階数は存在の条件にしない |
| OLS | 残差直交性、予測・係数誤差、摂動、定数4の確率的回復 |
| LASSOの存在 | 正のペナルティによる目的関数の発散と連続性から最小化解を構成 |
| LASSOの評価 | 半二乗損失の最小化性から基本不等式、cone包含、定数9の決定論的誤差 |
| LASSOの回復 | cone・列ノルムの摂動、随伴スコア、定数144の確率的誤差、等号ペナルティ代入の定数576 |
| 確率評価 | 明示的な可積分性を伴うMarkov、V=0の場合、独立性なしの事象交差 |
| 条件付き直交性 | E[f\|m]=0とgのm可測性からE‖g−f‖²=E‖g‖²+E‖f‖² |
| 独立標本の分散 | 時刻ごとのP標本に重みを掛けた分散≤C(Σw²)/P |
| 一様有向ペア抽出 | 自己対を除くN(N−1)個の母集団、復元抽出の積測度、独立性と平均0を構成から導出 |
| 観測での条件付け | 任意の観測法と抽出法の積空間で、通常の条件付き期待値を用いて中心化を証明 |
| デザインの組立 | 中心化誤差が標本行列−全ペア行列に等しいこと、(N−1)/Nと1/√Lの正規化 |
| ペア誤差 | 特徴の可測性・L2性・二乗平均を入力に、E‖D‖F²≤M C_A Q/P、E‖Dθ‖²≤C_K Q/P |
| 特徴モーメント | 有界なテスト勾配写像・線形成長する辞書から、観測位置の二乗平均Rを使って3(BGK)²(1+2R)とL2性を導出 |
| 加法観測 | Y=X+εの二乗平均≤2R_X+2R_ε。平均0や独立性を追加しない |
| 観測からの組立 | ψ⟨g(Y_i),Φ_m(Y_i−Y_j)⟩と弱応答の有限和を定義し、可測性・L2性を証明 |
| 辞書の厳密表現 | Σθ_mΦ_m=κから、合成特徴をκの特徴へ同定。係数方向の評価にはκの成長率を使う |
| 実際の回帰残差 | r̃=r−Dθ、E‖r̃‖²=E‖r‖²+E‖Dθ‖²、全ペア上界VからV+C_K Q/Pへ接続 |
| 全デザイン誤差 | 参照行列へのFrobenius二乗平均を全ペア誤差と抽出誤差に分解し、作用素ノルムへ評価 |
| 標本回帰への適用 | 可測性・可積分性を導いてからOLS/LASSOへ適用。標本誤差の上界を別途仮定しない |
| 既知support | 選択列の誤差を全行列で制御。OLSの下界は選択列だけに課し、辞書全列のinjectivityは不要 |

観測を固定した抽出列の独立性を証明しており、観測を平均化した後の特徴の独立性は仮定しません。
全行・原子で抽出列を共有し、係数方向には合成特徴の二乗平均を使うため、不要な係数ノルムを追加しません。
`WMFKI_Stochastic/`では、勾配・Laplacian・時間微分を本物のFrechet微分として同定し、粒子モデルから位置モーメントと連続全ペアD0/V0を供給します。
任意の既存joint realizationへの普遍移送は行わず、原始入力を明示的な積空間上で構成します。

### 接続後の全体像

```text
原始初期乱数 + 独立Brownian入力
   ↓ Picard構成・実粒子SDE・同期結合
平均場Yと相互作用粒子X、同期第4モーメント率 C/N²
   ↓ 実時間特徴核・Fubini・iidペアP2
母集団設計A∞と連続設計誤差 O(1/N)
   ↓ 観測摂動 + 供給された同じX上のRMS求積誤差
D0 ≤ CA(1/N+e+q),  V0 ≤ CV(σ²/N+e+q)
   ↓ 一様有向ペア抽出、条件付き中心化
D = D0 + M C_A Q/P,  V = V0 + C_K Q/P
   ↓ 識別性・smallness・確率・penalty条件
既知support OLS回復 ／ 生デザインLASSO回復
```

`WMFKIJointAssembly.exists_particle_weak_recovery`が原始入力側の入口です。
`WMFKI.WeakAssemblyData.oracle_recovery`と`lasso_recovery`が回復側の既存APIです。
D0は**Frobenius二乗平均上界**として実際に導きます。作用素ノルム上界からFrobenius上界を逆向きに推論していません。

### 回復評価の意味

OLSは、実際の残差y−Bθ*とデザイン誤差について

```text
E ‖B−A∞‖op² ≤ D,  E ‖y−Bθ*‖² ≤ V,
∀u, γ‖u‖ ≤ ‖A∞u‖,  D ≤ δγ²/4
    ↓
確率1−δ−ε以上の可測な事象上で
‖θhat−θ*‖² ≤ 4V/(εγ²)
```

LASSOは、同様の二乗平均条件に加え、真のsupportを含むS、cone上の下界γ、
列ノルム上界R、正のペナルティ
`λ ≥ 2(R+γ/2) sqrt(V/ε)` の下で

```text
確率1−δ−ε以上の可測な事象上で
θhat−θ* ∈ cone(S),  ‖θhat−θ*‖² ≤ 144 |S| λ²/γ⁴
```

を証明しています。λを下限と等しくした右辺は
`576 |S| (R+γ/2)² V/(εγ⁴)` に一致します。
この代入はλ>0という元の条件を取り除くものではありません。

デザインと残差の独立性は仮定していません。
`EstimatorRecovery.lean`では推定量の存在も利用し、最小化性を別の入力仮定にせず回復定理へ接続しています。
ただし、選択した推定量自体の可測性と数値ソルバーの正当性は未検証です。
結論は可測な良事象を明示する形なので、その可測性を暗黙に使ってはいません。

## 公理監査と検証限界

- 初期OLS骨組みの一時公理は5→4→1→0個。今回追加した行列・LASSOの仮置き宣言も全て証明へ置換済み。
- 現在は**プロジェクトの一時公理0、sorry 0**。
- 既存126宣言と新規437宣言、合計**563宣言**の推移的な依存は、Leanの標準公理 `propext`、`Classical.choice`、`Quot.sound` のみ。
- 既存26例と新規6例、合計32例を検査。新規例では、本物の三階Frechet微分、compact bump、偏りと完全依存を持つ観測雑音、非零選択support残差、原始Brownian終点を確認。
- OLSの定義・Showcaseと、追加したLASSO仕様は証明開始時のハッシュから不変。

**公理0は、数値ソルバーや任意の既存確率空間への移送まで検証したという意味ではありません。**
RMS求積精度、識別可能性・restricted-cone geometry、sampling smallness、確率許容値、LASSO penalty条件は定理の明示的な仮定です。選択した推定量の可測性、数値アルゴリズムの正当性、任意の既存joint realizationへの移送、無限時間一様率は対象外です。
検証範囲と外部依存は `WMFKI_Stochastic/README.md` と `WMFKI_Stochastic/THIRD_PARTY.md` に記録しています。

## 再実行

このディレクトリで実行します。

```bash
./scripts/setup.sh
python3 scripts/verify.py --clean
```

今回の作業前の原稿も保護検査する場合は次を使います。
後日原稿を変更した場合に、この検査が失敗するのは意図した挙動です。

```bash
python3 scripts/verify.py --clean --check-paper
```

- Lean **4.34.1**、Mathlib **v4.34.1**、commit `d13f23b723b8a846827a245b89c10fc7d3f11612`。
- 確率解析基盤 `stochasticAnalysis` はcommit `0cb33378176178d269f53a4dada439f8ecd3bf5e`、Apache-2.0で固定。
- elan **4.2.4**、専用環境 `~/.cache/wmfki-lean/`。Mathlibと確率解析依存のビルドキャッシュには数十GBの空き容量を推奨。
- `.lake`は外部キャッシュへのシンボリックリンク。依存・ビルド成果物はリポジトリ外。
- シェル設定・既存のLean環境は変更しません。
- `WMFKI_LEAN_CACHE`で保存先を変更できます。既存`.lake`が別の場所を指す場合は上書きしません。
- 初回にはネット接続と数GB以上の空き容量が必要です。

**引数なしの `lake clean` は使わないでください。** 検証スクリプトは
`lake clean wmfki_formalization`で自作プロジェクトだけを再ビルドします。
単体確認は `./scripts/lake env lean Lean_Code/Human_Check.lean` と
`./scripts/lake env lean WMFKI_Stochastic/Audit.lean`。
Mathlibは公式のコンパイル済みキャッシュを使用しています。
別環境・別研究者による独立再検証は行っていません。

## ファイル案内

- `docs/formalization-map.html`、`docs/formalization-map-en.html`：粒子入力からOLS/LASSOまでの日本語・英語概念図。
- `docs/formalization-dependency.md`、`docs/formalization-dependency-en.md`：主要宣言のMermaid依存グラフと原稿対応表。
- `Blueprint.md`、`EXTENSION_PLAN.md`：設計と依存関係。
- `Lean_Code/Definitions.lean`、`LassoDefinitions.lean`：固定した定義と仮定付き定理文。
- `Showcase.lean`：初期OLS仕様の公開入口。変更していません。
- `Lean_Code/MatrixBridge.lean`、`MatrixMoments.lean`：行列とノルムの接続。
- `Lean_Code/MoorePenrose*.lean`：擬似逆の存在と最小化性。
- `Lean_Code/Lasso*.lean`：LASSOの存在、幾何、決定論的・確率的評価。
- `Lean_Code/EstimatorRecovery.lean`：構成した両推定量への回復定理の適用。
- `Lean_Code/ConditionalOrthogonality.lean`、`SamplingVariance.lean`：確率解析の追加補題。
- `Lean_Code/FiniteSampling.lean`、`PairSampling.lean`：一様母集団と具体的な有向ペア抽出。
- `Lean_Code/SamplingConditional.lean`、`SamplingIntegrability.lean`、`SamplingMoments.lean`：観測と抽出の積空間。
- `Lean_Code/PairDesignMoments.lean`、`PairAssembly.lean`：共有抽出の行列・係数方向評価、実際の組立式との一致。
- `Lean_Code/FeatureMoments.lean`：有界な勾配写像・線形成長と、観測位置の二乗平均からの特徴評価。
- `Lean_Code/ObservationMoments.lean`、`ObservedFeatures.lean`：加法観測から特徴・デザイン・係数方向の二乗平均へ接続。
- `Lean_Code/ResidualOrthogonality.lean`、`SampledResidual.lean`：実際の回帰残差への条件付き直交性の適用。
- `Lean_Code/WeakPairMoments.lean`：弱応答の有限和と、位置モーメント・全ペア残差上界を入力とする結合定理。
- `Lean_Code/SamplingRegularity.lean`：行列・残差の可測性と二乗ノルムの可積分性。
- `Lean_Code/DesignComposition.lean`：全ペア・抽出誤差のFrobenius加法性と作用素評価。
- `Lean_Code/PairRecovery.lean`：生のペア特徴からOLS/LASSOへ適用し、既知supportの列選択も処理。
- `Lean_Code/WeakPairRecovery.lean`：観測・テストから組み立てた行列・応答を両回復定理へ渡す結合定理。
- `Lean_Code/Human_Check.lean`：例題と公理監査。
- `Lean_Code/AXIOM_STATUS.md`：証明台帳。
- `WMFKI_Stochastic/PrimitiveRecovery.lean`：原始粒子入力から回復証明書を返す公開終点。
- `WMFKI_Stochastic/RecoveryCertificate.lean`：既知support OLS・LASSOの明示的な適用条件と結論。
- `WMFKI_Stochastic/HumanCheckJointRecovery.lean`：新規6例。
- `WMFKI_Stochastic/Audit.lean`：採用した437宣言の公理監査。
- `WMFKI_Stochastic/SOURCE_MANIFEST.json`、`THIRD_PARTY.md`：ソース由来・hash・外部依存・ライセンス。
- `statement-lock.json`、`extension-statement-lock.json`：固定仕様のハッシュ。
- `verification/validation.json`、`build.log`、`axioms.log`：再検証結果。

公開用の `docs/` には形式化マップと依存関係資料のみを収録します。原稿本体、入力資料、ビルドキャッシュはこのリポジトリに含めません。
