# 証明台帳

## 現在の状態

抽象OLS・LASSO、行列接続、両推定量の存在、条件付き直交性、具体的な一様有向ペア抽出を実装。
さらに`WMFKI_Stochastic/`で、原始初期乱数・独立Brownian入力から平均場過程と実粒子SDEを構成し、同期第4モーメント率、実時間特徴核、母集団設計、観測・求積D0、同一実現V0を経て、既知support OLSとLASSOへ接続した。

公開終点は`WMFKIJointAssembly.exists_particle_weak_recovery`。
RMS求積精度、母集団設計の識別可能性・restricted-cone geometry、sampling smallness、確率許容値、LASSO penalty条件は明示的な仮定として保持する。

**プロジェクトの一時公理0、sorry 0。**
固定したDefinitions・Showcase・LassoDefinitionsのハッシュは各証明開始前から不変。
検証対象はLean回復層128宣言と確率解析層437宣言の合計565宣言。依存は `propext, Classical.choice, Quot.sound` のみ。
例題は既存26個と新規6個の合計32個。完全な検査結果は `../verification/validation.json` を参照。

## 初期骨組みと現在の状態

初期の一時公理は5個。数学の基礎公理とプロジェクトの一時公理は区別する。

| 名前 | 内容 | 状態 |
|---|---|---|
| lowerBound_perturb | 作用素下界の摂動 | 証明済み |
| leastSquares_error_bound | 最小二乗誤差の決定論的評価 | 証明済み |
| secondMoment_good_event | 非負関数のMarkov、零モーメントを含む | 証明済み |
| good_event_intersection | 独立性を要求しないunion bound | 証明済み |
| oracle_recovery_of_moments | 定数4の抽象OLS定理 | 証明済み、最後に置換 |

行列接続、Moore–Penrose解の存在・最小化性、LASSOの存在・仮定付き回復は追加段階で証明済み。
原稿のSDE、テスト、サンプリングから具体的なV,Dを導く部分は未形式化。
未実装の数学は一時公理の個数に含まれないため、個数0だけでは原稿全体の完了を意味しない。

## 置換履歴

- 初期骨組み：`scripts/lake build` 成功（`01-scaffold.log`）。
- 第1段階：`lowerBound_perturb` を逆三角不等式・作用素ノルム評価で証明。
  `scripts/lake env lean Lean_Code/Deterministic.lean`、`scripts/lake build` 成功。
  一時公理5→4個（`02-perturb.log`）。

- 第2段階：OLSは最小化条件に任意の直線方向を代入し、Mathlibの
  `discrim_le_zero` で直交性を導出。Pythagorasと下界から定数1の誤差評価。
  Markovは `mul_meas_ge_le_integral_of_nonneg` を利用し、V=0は積分零のa.e.零性で処理。
  union boundは `measureReal_union_le` と補集合測度。
  `scripts/lake env lean Lean_Code/Deterministic.lean`、
  `scripts/lake env lean Lean_Code/Probability.lean`、`scripts/lake build` 成功。
  一時公理4→1個（`03-ols-and-probability.log`）。途中の型推論・補集合測度のエラーは修正済み。

- 第3段階：残る定理は上記4補題だけを使って組み立てる。
  デザイン良事象の閾値をγ²/4とし、残差良事象と交差。
  下界γ/2で決定論的OLS評価を適用して定数4を得る。
  証明開始前に使用補題の一時公理が全て除去済みであることを確認した。
  `scripts/lake env lean Lean_Code/MainTheorem.lean`、`scripts/lake build` 成功。
  一時公理1→0個（`04-main-theorem.log`）。
- `scripts/lake env lean Lean_Code/Human_Check.lean` で8宣言の公理監査と7個の例題検査に成功。
  例題には、全入力仮定を具体的に満たす1点確率空間の回帰問題（残差が零・非零の両方）を含む。
  `scripts/setup.sh` の再実行にも成功（既存環境を上書きしない）。
- `python3 scripts/verify.py --clean --check-paper` 成功。
  自作プロジェクトのクリーン再ビルド、仕様ハッシュ、Mathlib固定版、原稿保護ハッシュを照合。
  最終結果は `../verification/validation.json`、ビルド・監査ログは同ディレクトリ。

## 行列・LASSO・確率補題の追加履歴

- `MatrixBridge.lean`：最初の作用素/Frobenius評価の仮置き宣言を証明へ置換。
  列制限、差、転置・随伴、成分ベクトルのEuclideanノルムとの一致まで証明。
- `MoorePenrose.lean`：四条件から最小化性と誤差評価を証明。
  `MoorePenroseConstruction.lean`で四条件を満たす写像の存在を追加した。
- LASSO骨組みは2宣言。仕様を固定し、幾何・基本不等式から決定論的定理を証明して2→1個。
  `12-lasso-deterministic.log`の段階では、回復定理に仮置きが残っていた。
- `LassoTransfer.lean`でcone・列の摂動とスコアを証明し、
  `LassoRecovery.lean`で確率定理を組み立てて1→0個。
  `13-lasso-transfer.log`、`14-lasso-recovery.log`。定数576の代入恒等式も証明。
- `LassoExistence.lean`：L1≥Euclideanノルム、連続性、無限遠での発散から最小化解の存在。
  `EstimatorRecovery.lean`でOLS・LASSOとも最小化性の入力仮定を除いた版を追加。
- `ConditionalOrthogonality.lean`：通常の条件付き期待値とL2射影の橋渡しから直交性・二乗平均加法性。
  `SamplingVariance.lean`：独立標本の重み付き分散とΣw²/P。
  `16-conditional-orthogonality.log`、`18-sampling-variance.log`。
- `MatrixMoments.lean`：Frobeniusから作用素ノルムへの積分の移行と可積分性。
  `19-estimator-existence.log`、`20-extended-audit.log`。
- `Human_Check.lean`を45宣言・13例へ拡大し、再実行スクリプトにLASSOの固定仕様ハッシュも追加。
  初期の8宣言の監査結果は上の履歴に残してある。

## 具体的なペア抽出の統合・監査

- セッション分離後に、未反映だった有限母集団・条件付き期待値・可積分性・行列モーメントの既存証明を回収した。
- 再開時の存在確認不足で `FiniteSampling.lean`、`SamplingIntegrability.lean`、`PairDesignMoments.lean` を一度上書きした。
  保存済み履歴から再構成し、直前の検証結果に記録された3つのSHA-256へ完全一致で復元した。
  重複実装はキャッシュの `recovery-20261007/current/` に保全し、現在のビルド対象には含めない。
  復元コードは既存成果であり、今回新たに証明したものとは数えない。
- `PairAssembly.lean` を追加。標本・全ペアデザインを有限和で定義し、既存の中心化誤差との一致を証明。
  条件付き中心化、Frobenius評価、係数方向評価を実際の行列差へ適用した。
- 全実装を `Main.lean` から読み込み、旧45宣言に未監査だった既存32宣言と今回の4宣言を加え、計81宣言を監査。
  二点一様分布の平均・非零分散、定数特徴の零誤差、N=1の退化などを含め、例題は18個。
- 続いて `FeatureMoments.lean` に2宣言を追加。特徴の成長評価と、観測位置の二乗平均からの特徴L2性・積分上界を証明し、監査は83宣言になった。
  C_b^3テストからの勾配写像の構成、粒子系からの一様位置モーメントは未形式化。

## 観測・特徴・残差の接続

- `ObservationMoments.lean`：潜在位置と加法観測ノイズの二乗平均から観測位置の評価を導出。独立性・平均0は不使用。
- `ObservedFeatures.lean`：観測値から特徴を定義し、可測性・L2性・デザイン誤差を位置モーメントから供給。
  厳密表現Σθ_mΦ_m=κを使い、係数方向の定数はκの成長率で評価した。
- `ResidualOrthogonality.lean`：通常の関数を既存のL2直交性へ接続し、有限Euclideanベクトルの二乗平均加法性を証明。
- `SampledResidual.lean`：実際の残差r̃=b−Ãθとr=b−Aθについてr̃=r−Dθを証明。
  応答・特徴から残差の可測性・L2性を導き、E‖r̃‖²=E‖r‖²+E‖Dθ‖²を証明した。
- `WeakPairMoments.lean`：弱応答を原稿と同じ有限和で定義。有界テストから応答L2性を供給し、加法観測から中心化・デザイン・残差のQ/P評価までを結合。
  潜在位置モーメントと全ペア残差の上界Vは入力として明示したまま。
- 19宣言を追加して計102宣言。完全に相関した観測ノイズ、弱応答の符号・正規化、原子の相殺、観測に依存する誤差の非零二乗平均を追加し、例題は22個。
- 作業前の全Leanファイルを専用キャッシュの `checkpoints/pre-observation-residual/` に保全した。
  従来の実装は `Main.lean` のimportと `Human_Check.lean` の監査・例題以外を変更していない。

## デザイン誤差合成・回復定理への接続

- `SamplingRegularity.lean`：行列成分の可測性・L2性から、作用素・残差ノルム二乗の可測性・可積分性を導いた。
- `DesignComposition.lean`：全ペア誤差と抽出誤差のFrobenius二乗平均の加法性。作用素ノルム二乗はその上から評価し、加法性は主張しない。
- `PairRecovery.lean`：D=D0+M C_A Q/P、V=V0+C_K Q/Pを供給し、構成した擬似逆とLASSOへ適用。
  OLSの既知supportは単射の列選択で明示し、下界は選択列だけに要求。全辞書のinjectivityへ置き換えていない。
- `WeakPairRecovery.lean`：潜在位置・ノイズ・固定テストの評価写像を`WeakAssemblyData`に整理し、実際の組立から両回復定理へ接続。
  特徴・標本デザイン・標本残差のモーメントを構造体の仮定にはせず、位置モーメントと全ペア上界から証明した。
- 原稿4.9の証明で使うFrobenius上界をD0に要求する。作用素ノルムの上界から同じ定数のFrobenius上界を逆に導いてはいない。
- 24宣言と4例を追加して126宣言・26例。符号付き重みの二乗和、選択列だけの下界、非零Frobenius分解、実際の一様抽出で全入力を満たす既知support回復例を検査。
- 作業前のファイルは専用キャッシュの `checkpoints/pre-pair-recovery/` に保全。
  既存の実装変更は `Main.lean` のimportと `Human_Check.lean` の監査・例題のみ。

## 粒子モデルから回復までの採用

- `WMFKI_Stochastic/`に116個の証明・統合モジュールを採用した。内部importだけを`WMFKI_Stochastic.*`へ変更し、名前空間と定理文は隔離監査版から変更していない。
- `stochasticAnalysis` commit `0cb33378176178d269f53a4dada439f8ecd3bf5e`をApache-2.0のLake依存として固定した。上流原本は複製・改変せず、プロジェクト側アダプター44件を明示している。
- Picard構成、有限L4経路クラス内一意性、独立平均場コピー、同期粒子系、第4モーメント率C/N²を接続した。
- 実時間特徴核の可測性・L2性・Fubini条件を証明し、コピーU統計量を実周辺法則の母集団設計へ同定した。
- 粒子対母集団設計のFrobenius二乗誤差O(M/N)を導き、偏りと内部依存を許す観測誤差および供給されたRMS求積誤差と合成した。
- 実際の`gradient`、`Laplacian`、`deriv ψ`をproductionの`fullPairDesign`、`observedWeakResponse`、`fullRegressionResidual`へ厳密に同定した。
- 同じX,Y,観測系についてD0とV0を構成し、`WeakAssemblyData.oracle_recovery`と`lasso_recovery`へ渡した。
- 新規437宣言と6例を監査。既存126宣言・26例と合わせて563宣言・32例。標準公理のみ、プロジェクト固有公理0、`sorry` 0。

ソース由来とhashは`../WMFKI_Stochastic/SOURCE_MANIFEST.json`、外部依存とライセンスは`../WMFKI_Stochastic/THIRD_PARTY.md`に記録した。

## 現行L4DCとの対応強化

- `sampled_lasso_recovery_of_minimizer`と`WeakAssemblyData.lasso_recovery_of_minimizer`を追加し、点ごとにLASSO最小化条件を満たす任意の選択へ、構成済み推定量と同じcone・定数144の評価を適用した。
- `RecoveryCertificate.lasso_any`を追加し、原始粒子入力からの公開終点がこの任意最小化解版も返すようにした。推定量選択の可測性は要求せず、可測なdesign/residual良事象上で点ごとに結論する。
- `l4dc-statement-lock.json`と`verify.py --check-l4dc`を追加し、現行L4DCの標本LASSO定義、誤差スケール、主回復定理、pair-sampling仮定を環境単位で照合する。
- Lean回復層は126宣言から128宣言となり、確率解析層437宣言と合わせて565宣言を監査する。

## 採用前に残っていた接続課題（履歴）

以下は旧126宣言段階の記録である。粒子強解、同期率、実時間母集団設計、D0/V0、実微分との同定、回復APIへの接続は`WMFKI_Stochastic/`で完了した。現在も定理の仮定として残るのはRMS求積精度と回復幾何・smallness・penalty条件であり、任意の既存joint realizationへの移送、無限時間率、数値ソルバーの正当性は対象外である。

1. **原稿の具体的な対象**：有限時刻の観測から応答・デザインを構成済み。
   g,lap,dψをC_b^3/C_c^1テストの勾配・Laplacian・時間微分へ同定する部分、求積誤差の正当化は未完了。
   選択した推定量の可測性、数値アルゴリズムの正当性、A.7の良事象上の期待値版も未検証。
2. **粒子強解とモーメント（A.1、B.1）**：独立初期値・Brownian駆動から強解を構成し、
   局所化、停止Itô公式、Gronwall、Fatou、交換可能性からN一様の2次・4次モーメントを導く。
   固定Nの解の存在だけでは代用しない。
3. **残差（3.1、A.2–A.5、4.8）**：ベクトルItô公式・独立Brownian積分の直交性・
   Itô等長性、時間積分の部分積分、行正規化1/√L、観測摂動と求積誤差を結合。
   組み立てた残差の可測性・L2性は供給済みだが、全ペア残差の具体的なVの評価はここから導く必要がある。
4. **デザイン（B.2–B.3、4.9）**：同期結合による4次誤差O(N^{-2})、
   独立パスU統計量の二乗平均O(N^{-1})、対角除外のバイアス、求積・観測摂動。
   具体的な全ペア上界D0と定数の一様性、参照行列を連続極限デザインとして構成・同定する部分は未証明。
   D0から標本デザインの作用素上界へ合成する部分は証明済み。
5. **ランダムペア（A.6）**：一様復元抽出の積モデル、条件付き平均0、共有抽出、正規化、
   行列・係数方向のQ/P評価、実際の残差への直交性は接続済み。
   特徴定数は位置モーメントから導出した。残るのは潜在SDEからの位置モーメントの一様性、
   任意の既存確率空間との分布移送。決定論的な参照行列への全誤差の結合は証明済み。

OLS/LASSOとも実際の標本回帰へ接続したが、4.12(i),(ii)の上流にある位置モーメントと全ペア上界D0,V0の供給は未完了。
2–5の確率解析は単一の巨大な公理として追加していない。
必要な確率積分の等長性や固定Mathlibで確認した足場は `../STOCHASTIC_FRONTIER.md` を参照。
一時公理0を原稿全体の完了率に読み替えてはならない。

## 有効だった作業指示

- 「最終定理文を変更せず、下界摂動だけを作用素ノルムと逆三角不等式から証明する」
- 「最小二乗解を誤差評価そのもので定義しない。実際の最小化条件から直交性を導く」
- 「Mathlibの二次式判別式の非正値性を使い、任意方向の一次項を0と示す」
- 「MarkovのV=0の場合を分離する。可積分性を落とさない」
- 「デザインと残差の独立性を追加せず、補集合のunion boundを使う」
- 「主張を固定したまま下位補題を結合し、#print axiomsで推移的依存を検査する」

## 実行方針

仕様を固定し、下位補題を一つずつ証明、対象ファイルを確認、`scripts/lake build`。
`#print axioms` で最終依存を確認する。途中ログはリポジトリ外の
`~/.cache/wmfki-lean/logs/` に保存する。
