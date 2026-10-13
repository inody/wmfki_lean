import Lean_Code.Main

/-!
今回の固定仕様：二乗平均仮定からOLS係数回復を導く部分定理。
原稿のSDE仮定から二乗平均評価を導く部分は含まない。
本ファイルの定理文を証明作業中に弱めない。
-/

namespace WMFKI.Showcase

theorem oracle_recovery
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    OracleRecoveryStatement (E := E) (F := F) :=
  WMFKI.oracle_recovery_of_moments

end WMFKI.Showcase
