# 確率解析側の到達点と検証境界

対象環境：

- Lean 4.34.1
- Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`
- `stochasticAnalysis` `0cb33378176178d269f53a4dada439f8ecd3bf5e`（Apache-2.0）

公開終点は次の定理である。

```lean
WMFKIJointAssembly.exists_particle_weak_recovery
```

## 完了した接続

### 原始入力から粒子系

明示的な積確率空間上で、可測L4初期値と独立Brownian族から有限時間の平均場過程をPicard構成する。有限L4経路クラス内の一意性、適合性、有限時間整合性、独立平均場コピーを証明する。

同じ初期配列・Brownian配列を使う相互作用粒子系を構成し、同期差の積分方程式とドリフト分解を証明する。コピーの新しい粒子filtrationへの追加適合性は使わず、共通の原始ドライバと通常の時間積分で比較する。

### 同期第4モーメント率

線形成長を伴うglobally Lipschitz核について、対角除外を保った実際の揺らぎを評価する。共有タグの条件付き独立性を用い、相互作用粒子そのものの独立性は仮定しない。

全定数を粒子数より先に選び、各`N > 0`、各粒子、各`0 ≤ t ≤ T`について

```text
E ‖X_i^N(t) - Y_i(t)‖⁴ ≤ C / N²
```

を得る。`N=0`の率は主張しない。`T=0`、`L=0`、`N=1`も全除算規約の下で処理する。

### 実時間特徴と母集団設計

特徴には本物の`gradient φ`を使う。粒子対コピーの特徴差は独立性ではなく、依存したL4×L4 Cauchy–Schwarzで評価する。時間・粒子・行・列の独立性は仮定しない。

一粒子原始入力対上に実時間核

```text
G(u,v) = ∫₀ᵀ ψ(t) ⟨∇φ(Y_t(u)), Φ(Y_t(u)-Y_t(v))⟩ dt
```

を定義する。積分前に共同可測性、L2性、積可積分性を証明し、その後にFubiniと有限和・時間積分の交換を行う。

非対角`i ≠ j`にだけ原始入力対の積法則を適用する。対角項は先に0とし、`N⁻² Σ_{i≠j}`を`1/[N(N-1)]`へ変更しない。

実周辺法則

```text
μ_t = (π × P).map (Y_t)
```

を使い、コピー設計を`μ_t × μ_t`の母集団設計へ同定する。静的iidペア評価と同期特徴評価を同じ`Y`について合成し、

```text
E ‖A_particle^cts - A_population‖F² ≤ C M / N
```

を得る。

### 観測・求積を含むD0

観測誤差は潜在系との独立性だけを要求する。偏り、ラベル・時間・座標間の任意依存を許し、観測第4モーメントを要求しない。

同じ実粒子`X`について供給された設計RMS求積誤差と観測摂動を合成し、

```text
D0 ≤ CA (1/N + e + q)
```

を得る。三つの行列誤差、行、列の独立性・直交性は使わず、FrobeniusをEuclidean成分ベクトルとして評価する。

`e = Δt^(2p)`、`q = Cε σobs²`と読めば原稿の形になる。RMS求積精度そのものは明示的仮定であり、時間正則性だけから導いたとは主張しない。

### 同じ実現上のV0

実粒子SDEに対する本物のItô公式、Brownian共分散・等長性、時間部分積分から連続弱残差を構成する。応答のRMS求積と観測摂動を、D0と同じ`X`・観測系上で合成し、

```text
V0 ≤ CV (σ²/N + e + q)
```

を得る。観測雑音の無偏性や粒子間独立性は使わない。

### production定義と回復API

以下を厳密に同定した。

- 新しい連続特徴設計と`continuousDictionaryDesign`
- 離散辞書設計とproduction `fullPairDesign`
- `discreteResponseVector`とproduction `observedWeakResponse`
- response-design差とproduction `fullRegressionResidual`

実際の位置、観測雑音、`gradient`、`Laplacian`、`deriv ψ`から`WMFKI.WeakAssemblyData`を構成する。特徴・残差モーメントを構造体の原始フィールドとして追加しない。

得られたD0/V0を既存の

```lean
WMFKI.WeakAssemblyData.oracle_recovery
WMFKI.WeakAssemblyData.lasso_recovery
```

へ渡す。`RecoveryCertificate`は結論を束ねる出力命題であり、仮定ではない。

## ランダムペア回復で残る明示的条件

既知support OLSには、抽出数、選択写像の単射性、選択母集団設計のlower bound、design sampling smallness、正の確率許容値を要求する。

LASSOには、真のsupport、cone lower bound、column bound、design sampling smallness、正のpenalty、および

```text
2 (R + γ/2) sqrt(V/ε) ≤ λ
```

を要求する。

これらは原稿の回復幾何・確率条件であり、自動導出していない。係数回復をsupport回復とは同一視しない。固定観測雑音から潜在一致を、固定正penaltyからLASSO一致を結論しない。

## 対象外または未証明

- 任意の既存joint realizationへの普遍的な分布移送
- 平均場コピーの、新たに構成した粒子filtrationへの追加適合性
- 無限時間の一様評価・普遍的gluing
- 選択した推定量自体の可測性
- 数値ソルバーの正当性
- support回復
- RMS求積精度そのものの導出

これらは今回の有限時間・普通積分によるD0/V0と係数回復定理には使っていない。

## 依存・監査

`stochasticAnalysis`は固定commitをLake依存として取得し、上流原本はこのディレクトリへ複製しない。ソース由来とライセンスは次に記録する。

- `WMFKI_Stochastic/SOURCE_MANIFEST.json`
- `WMFKI_Stochastic/THIRD_PARTY.md`
- `WMFKI_Stochastic/LICENSE-FUKASAWA-APACHE-2.0.txt`

productionでは既存126宣言と新規437宣言、合計563宣言を監査する。依存公理は`propext`、`Classical.choice`、`Quot.sound`のみ。プロジェクト固有公理0、`sorry` 0。既存26例と新規6例、合計32例を検査する。
