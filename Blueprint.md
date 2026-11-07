# WMFKIのLean形式化：設計図

## 目的と検証範囲

最終目標は対応する原稿のランダムペア係数回復定理
(`thm:random-pair-recovery`) である。(i) Oracle OLSと(ii) LASSOを、
確率的粒子解析と抽象回帰解析に分離して実装した。

**現在は、原始初期乱数・独立Brownian入力から平均場過程と実粒子系を構成し、同期率、実時間母集団設計、同じ実現上のD0/V0を経て、ランダムペアOLS・LASSO回復へ接続済み。**
公開終点は`WMFKIJointAssembly.exists_particle_weak_recovery`。

RMS求積精度、母集団設計の識別可能性・restricted-cone geometry、sampling smallness、確率許容値、LASSO penalty条件は、原稿どおり明示的な仮定として残す。これらを証明済み量へ読み替えない。
以下のOLS設計には初期段階の履歴も残す。現在の確率解析範囲は `STOCHASTIC_FRONTIER.md`、外部依存は `WMFKI_Stochastic/THIRD_PARTY.md` を参照。
`Showcase.lean` は初期OLS部分定理の固定仕様であり、変更していない。

## 原稿の最終目標

定理4.12(i)は次を主張する。

- i.i.d.初期値、独立Brownian駆動、Lipschitz・線形成長の真の相互作用。
- 初期4次モーメント有限。
- 観測誤差は潜在系から独立、2次モーメントを制御。誤差同士の独立は不要。
- 固定の有限辞書、真の係数による厳密表現、固定support。
- 軌道に依存しない固定テスト、空間C_b^r (r≥3)、時間C_c^1。
- 二乗平均の求積精度p>0と絶対重み和の制御。
- 時刻・サンプル間で独立な一様有向ペアの復元抽出、観測系から独立。
- 決定論的な連続極限デザインのactive columnsについて、全方向の下界γ>0。
- 0<δ,ε<1、δ+ε<1、および D≤δγ²/4。

このとき確率1−δ−ε以上で、OLS係数二乗誤差≤4V/(εγ²)。
V=Cη(σ²/N+Δt^(2p)+σobs²)+Cpairη Q/P、
D=CA(1/N+Δt^(2p)+σobs²)+CpairA Q/P、Q=Σw_n²。
定数は原稿の固定量に依存し、指定された離散化・標本量に一様。

## 記号の翻訳と初期仕様の監査

- 係数空間E、観測空間Fは実内積空間。有限次元EuclideanSpaceを代入可能。
  通常の関数空間 `Fin n → ℝ` のsupノルムをEuclideanノルムと誤認しない。
- B、A∞は連続線形写像。ノルムは**作用素ノルム**。
  Frobeniusから作用素ノルムへの評価と積分の移行は証明済み。
  有限時刻の観測から具体的な行列・応答を構成し、粒子SDEの強解・一様モーメント・母集団設計から必要なFrobenius予算を供給する。
- `LowerBound A γ := ∀u, γ*‖u‖ ≤ ‖A u‖`。
  幅広行列の「非零特異値の最小値」へのすり替えを避ける。
- `IsLeastSquares B y θhat := ∀θ, ‖B θhat-y‖² ≤ ‖B θ-y‖²`。
  初期定理は任意の最小化解に対して証明した。
  第2段階では有限次元係数空間でMoore–Penroseの四条件を満たす写像を構成し、
  その最小化性と回復定理への適用まで追加した。
- 残差は実際のベクトル `y-B θstar`。抽象的な非負スカラーで代用しない。
- 確率はMathlibの任意の確率測度。有限標本空間への制限はしない。
- 二乗平均仮定には可積分性を明記する。非可積分関数の形式的な積分値0を利用しない。
- デザインと残差の独立性は要求しない。
- 結論は測度を評価した良事象と、その上での係数誤差評価。
- V=0も扱う。Markovで閾値0を割らず、非負関数の積分0からa.e.零を使う。

## 依存グラフ

```text
原始初期乱数 + 独立Brownian入力
  → Picard平均場解・有限L4経路内一意性
  → iid平均場コピー + 同じドライバの相互作用粒子解
  → 同期第4モーメント率 C/N²

実gradient特徴 + 同期率
  → 粒子対コピー設計誤差 O(M/N)
原始入力対の実時間核 + iidペアP2 + μ_t×μ_t同定
  → コピー対母集団設計誤差 O(M/N)
  → 連続全ペアD0

実粒子Itô弱恒等式 + Brownian等長性
  → 連続全ペアV0
観測摂動 + 同じX上のRMS求積仮定
  → D0 ≤ CA(1/N+e+q)
  → V0 ≤ CV(σ²/N+e+q)

一様有向ペア積測度 + 条件付き中心化・共有抽出
  → D = D0 + M C_A Q/P
  → V = V0 + C_K Q/P

production fullPairDesign / observedWeakResponse / fullRegressionResidualとの同定
  → WeakAssemblyData.oracle_recovery / lasso_recovery / lasso_recovery_of_minimizer
  → 既知support OLS定数4、構成した解および任意のLASSO最小化解に対する定数144（代入時576）
```

OLSの下界は既知supportの選択列だけに要求する。全辞書列のinjectivityへ強めない。D0はFrobenius二乗平均であり、作用素ノルム上界から逆向きに導かない。

## 今回の小補題と証明方針

1. `lowerBound_perturb`：逆三角不等式と作用素ノルムからγ−rの下界。
2. `leastSquares_orthogonal`：最小化条件にθhat+t*uを代入。実二次多項式の最小性から一次係数0。
3. `leastSquares_prediction_sq_bound`：直交性からPythagorasの等式を得て、‖B(θhat−θstar)‖²≤‖ξ‖²。
   当初のCauchy–Schwarz案から、この同じ定数1を与える経路に変更した。
4. `leastSquares_error_bound`：g‖誤差‖≤‖B誤差‖≤‖ξ‖から二乗評価。
5. `secondMoment_good_event`：非負可積分関数のMarkov。V=0は別処理。
6. `good_event_intersection`：補集合のunion bound。独立性なし。
7. `oracle_recovery_of_moments`：デザイン誤差≤γ/2と残差二乗≤V/εを交差させる。g=γ/2で定数4。

## ファイル分割

- `Lean_Code/Definitions.lean`：下界・最小二乗解・部分定理の仕様。
- `Lean_Code/Deterministic.lean`：摂動、直交性、OLS安定性。
- `Lean_Code/Probability.lean`：Markovと良事象。
- `Lean_Code/MainTheorem.lean`：二乗平均仮定付きOLS部分定理。
- `Lean_Code/Main.lean`：全実装のimport。
- `Lean_Code/Human_Check.lean`：仕様照合と `#print axioms`。
- `Lean_Code/AXIOM_STATUS.md`：一時公理、除去履歴、未形式化項目を別々に記録。

行列・擬似逆・LASSO・推定量の存在・条件付き直交性・分散の追加モジュールは
`Lean_Code/Main.lean`から全てimportする。現在の一覧はREADMEに記載。

## Mathlib調査の初期結果

固定版v4.34.1、commit `d13f23b723b8a846827a245b89c10fc7d3f11612`。
実内積、作用素ノルム、Bochner積分のMarkov、Gronwall、Brownian motionのファイルは存在。
全ソースのファイル名・宣言・説明を `Ito/Itô/stochastic integral/McKean/pseudoinverse/Moore–Penrose` で検索した範囲では、原稿に直接適用できるItô積分・公式、McKean–Vlasov強解、擬似逆APIは見つからなかった。
これは不存在の完全な証明ではない。擬似逆は後に既存の直交射影と線形な右逆から構成できた。
Brownian motionの構成だけでSDE理論全体が使えるとは判断しない。最新の調査と必要な等長性の形は `STOCHASTIC_FRONTIER.md` に記録。

従って今回、粒子解析全体を巨大な一時公理に包んで「主定理を検証した」とはしない。
未実装の上流数学はこの設計図と台帳に明記し、実際に形式化した部分だけを報告する。
