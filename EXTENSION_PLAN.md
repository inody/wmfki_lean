# 第2段階：行列との接続とLASSO

既存の `Definitions.lean` と `Showcase.lean` は固定したまま、新しい定義・定理を追加する。
原稿は変更しない。粒子解析を仮定で隠して全体の検証完了とはしない。

## 行列・OLS

`MatrixBridge.lean`：実行列をEuclidean空間間の連続線形写像に変換する。
Frobeniusノルムはsqrt(Σ_i Σ_j A_ij²)と明示し、標準の行列ノルムとの取り違えを避ける。
行ごとのCauchy–Schwarzと総和から作用素ノルム≤Frobeniusを証明する。
列制限についても同じ評価を確認する。

`MoorePenrose.lean`：B,PについてBPB=B、PBP=P、BPとPBが自己随伴という
Moore–Penroseの四条件を実際の作用素等式として定義する。
この四条件からP yが最小二乗解であることを証明する。
「P yは最小化解」を擬似逆の定義にして結論を仮定することはしない。
存在の構成も `MoorePenroseConstruction.lean` で完了した。
rangeへの線形右逆とker・rangeの直交射影から四条件を満たす写像を構成する。
係数空間の有限次元性だけで足り、全列階数は仮定しない。

## LASSOの固定仕様

係数空間はEuclideanSpace ℝ (Fin M)、観測空間は実Hilbert空間。
L1(S,u)=Σ_{i∈S}|u_i|、coneはL1(Sᶜ,u)≤3 L1(S,u)。
θ*はSの外で0。Sは真のsupportそのものでも、それを含む集合でもよい。
目的関数は1/2 ‖Bθ−y‖² + λ L1(univ,θ)、λ>0。
λ>0は原稿本文のLASSO定義の条件であり、新たな仮定の強化ではない。

順序：
1. support分解、L1差の不等式、L1(S,u)²≤|S|‖u‖²。
2. 実際の随伴スコアの各成分に2|(B*ξ)_i|≤λを課し、内積を評価。
3. 最小化条件から基本不等式、cone包含、9|S|λ²/g⁴。
4. cone下界の摂動、列ノルムの摂動とスコアの評価。
5. OLSで検証済みのMarkov・union boundを再利用して、二乗平均仮定付きの定数144。
6. λを下限に等しく取った場合の定数576。

LASSO側も具体的な最小化問題から出発する。basic inequalityやcone包含自体を入力仮定にはしない。
新しいモジュールは `LassoDefinitions.lean`、`LassoDeterministic.lean`、`LassoRecovery.lean`。
1–6は証明済み。追加で、正のペナルティの下での最小化解の存在を
`LassoExistence.lean`で証明し、`EstimatorRecovery.lean`で両推定量の存在を回復定理へ接続した。
定数576は下限ペナルティを代入した恒等式として検証し、λ>0の条件は維持する。
この段階で監査対象は45宣言、例題13個へ拡大した。OLS・LASSOの固定仕様のハッシュも検査する。
具体的な抽出と特徴評価の統合時は83宣言・18例。観測・残差の接続で102宣言・22例となり、デザイン合成・回復への接続を追加した現在は126宣言・26例。

## 次の確率解析

原稿A.6で使う条件付き直交性・二乗平均の加法性と、具体的な一様有向ペア抽出を証明した。
観測との積空間で中心化を導き、全行の1/√L正規化、共有抽出、Frobeniusと係数方向のQ/P評価を接続した。
`PairAssembly.lean`では有限和で作る標本・全ペアデザインの差に同定する。
`ObservationMoments.lean`、`ObservedFeatures.lean`で、加法観測と位置二乗平均から特徴・デザインの上界へ接続した。
`SampledResidual.lean`では実際の残差へ直交性を適用し、全ペア上界VからV+C_pair Q/Pを導く。
`WeakPairMoments.lean`は応答も有限和で組み立て、可測性・L2性を供給してこれらを結合する。
`SamplingRegularity.lean`と`DesignComposition.lean`で全デザイン誤差をFrobenius二乗平均から合成し、作用素評価と必要な可測性・可積分性を供給した。
`PairRecovery.lean`は既知supportのOLSと生デザインのLASSOへ適用し、`WeakPairRecovery.lean`が加法観測・テスト評価写像からの組立と接続する。
粒子系からの一様位置モーメント・全ペアFrobenius上界D0・残差上界V0の供給、参照行列の連続極限としての構成、テストの微分関係、任意の既存確率空間への分布移送は未実装。
具体的な残課題、必要なBrownian積分の等長性、固定ライブラリの調査は
`STOCHASTIC_FRONTIER.md`に記録した。SDE由来のV,Dは依然として未証明。
