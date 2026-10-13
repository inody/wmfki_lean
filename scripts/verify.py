#!/usr/bin/env python3
"""固定仕様・ビルド・公理依存を再検証する。原稿保護検査は任意。"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

PROJECT = Path(__file__).resolve().parents[1]
CACHE = Path(os.environ.get("WMFKI_LEAN_CACHE", str(Path.home() / ".cache/wmfki-lean")))
PIN = "d13f23b723b8a846827a245b89c10fc7d3f11612"
STOCHASTIC_PIN = "0cb33378176178d269f53a4dada439f8ecd3bf5e"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    "WMFKI.lowerBound_perturb", "WMFKI.leastSquares_orthogonal",
    "WMFKI.leastSquares_prediction_sq_bound", "WMFKI.leastSquares_error_bound",
    "WMFKI.secondMoment_good_event", "WMFKI.good_event_intersection",
    "WMFKI.oracle_recovery_of_moments", "WMFKI.Showcase.oracle_recovery",
    "WMFKI.matrixMap_apply", "WMFKI.matrixMap_norm_le_frobenius",
    "WMFKI.frobenius_restrict_columns", "WMFKI.matrixMap_restrict_norm_le",
    "WMFKI.matrixMap_sub", "WMFKI.matrixMap_transpose", "WMFKI.frobenius_eq_vector_norm",
    "WMFKI.matrixMap_secondMoment_transfer", "WMFKI.isLeastSquares_of_orthogonal",
    "WMFKI.moorePenrose_isLeastSquares", "WMFKI.moorePenrose_error_bound",
    "WMFKI.exists_moorePenrose", "WMFKI.moorePenrose_spec", "WMFKI.moorePenrose_minimizes",
    "WMFKI.partialL1_nonneg", "WMFKI.partialL1_decomp", "WMFKI.partialL1_sq_le",
    "WMFKI.l1_support_difference", "WMFKI.score_inner_bound",
    "WMFKI.lasso_basic_inequality", "WMFKI.lasso_deterministic",
    "WMFKI.coneLowerBound_perturb", "WMFKI.columnBound_perturb",
    "WMFKI.score_of_column_and_residual", "WMFKI.lasso_recovery_of_moments",
    "WMFKI.lasso_penalty_normalization", "WMFKI.norm_le_l1Norm",
    "WMFKI.lassoObjective_continuous", "WMFKI.exists_lasso", "WMFKI.lassoEstimator_minimizes",
    "WMFKI.oracle_moorePenrose_recovery", "WMFKI.lasso_estimator_recovery",
    "WMFKI.l2_norm_sq_eq_integral", "WMFKI.conditional_centered_inner_zero",
    "WMFKI.conditional_centered_second_moment", "WMFKI.weighted_independent_variance",
    "WMFKI.refreshed_sampling_variance",
    "WMFKI.integral_uniformPopulation", "WMFKI.finite_memLp_two", "WMFKI.integral_draw_eval",
    "WMFKI.draws_independent", "WMFKI.centered_draw_mean", "WMFKI.centered_draw_variance",
    "WMFKI.samplingError_mean", "WMFKI.samplingError_second_moment",
    "WMFKI.samplingError_second_moment_weighted", "WMFKI.populationMean_linear_combination",
    "WMFKI.samplingError_linear_combination", "WMFKI.samplingError_eq_sampled_sub_full",
    "WMFKI.orderedPair_card", "WMFKI.pairCorrection_bounds", "WMFKI.corrected_pair_average",
    "WMFKI.pairPrefactor_sq_le", "WMFKI.pairRowError_mean", "WMFKI.pairRowError_second_moment",
    "WMFKI.single_particle_no_pairs", "WMFKI.product_conditional_centered",
    "WMFKI.pairRowError_conditional_mean", "WMFKI.integrable_finite_fibers",
    "WMFKI.samplingError_observable", "WMFKI.samplingError_observation_memLp",
    "WMFKI.samplingError_joint_memLp", "WMFKI.samplingError_joint_second_moment",
    "WMFKI.pairRowError_joint_memLp", "WMFKI.pairRowError_conditional_mean_of_moments",
    "WMFKI.pairRowError_joint_second_moment", "WMFKI.pairDesignError_second_moment",
    "WMFKI.pairDesignError_mul_coefficients", "WMFKI.pairDesignError_direction_second_moment",
    "WMFKI.pairDesignError_eq_difference", "WMFKI.assembled_design_conditional_centered",
    "WMFKI.assembled_design_second_moment", "WMFKI.assembled_design_direction_second_moment",
    "WMFKI.pairFeature_sq_bound", "WMFKI.pairFeature_second_moment",
    "WMFKI.norm_add_sq_le_twice", "WMFKI.observation_second_moment",
    "WMFKI.observedPairFeature_measurable", "WMFKI.observedPairFeature_moments",
    "WMFKI.observed_design_second_moment", "WMFKI.noisy_observed_design_second_moment",
    "WMFKI.observedPairFeature_realizable", "WMFKI.observed_direction_second_moment",
    "WMFKI.conditional_centered_second_moment_fun", "WMFKI.finite_observation_pythagoras",
    "WMFKI.sampledResidual_decomposition", "WMFKI.fullPairDesign_entry_measurable",
    "WMFKI.fullPairDesign_entry_memLp", "WMFKI.fullResidual_entry_regular",
    "WMFKI.sampledResidual_second_moment_identity", "WMFKI.sampledResidual_second_moment_bound",
    "WMFKI.observed_residual_second_moment_bound", "WMFKI.observedWeakResponse_regular",
    "WMFKI.weak_pair_moment_bounds",
    "WMFKI.continuous_matrixMap", "WMFKI.frobenius_sq_sum",
    "WMFKI.finite_vector_norm_sq_regular", "WMFKI.frobenius_sq_regular",
    "WMFKI.matrix_operator_moment_regular", "WMFKI.sampledPairDesign_entry_regular",
    "WMFKI.sampledResidual_eq_regression", "WMFKI.sampledResidual_norm_sq_regular",
    "WMFKI.matrix_observation_pythagoras", "WMFKI.sampledDesign_second_moment_identity",
    "WMFKI.sampledDesign_operator_moments", "WMFKI.sampled_moorePenrose_recovery",
    "WMFKI.sampled_lasso_recovery", "WMFKI.frobenius_select_sq_le",
    "WMFKI.full_design_selected_second_moment_le", "WMFKI.sampled_oracle_recovery",
    "WMFKI.WeakAssemblyData.radius_nonneg", "WMFKI.WeakAssemblyData.atomBound_nonneg",
    "WMFKI.WeakAssemblyData.kernelBound_nonneg", "WMFKI.WeakAssemblyData.position_moments",
    "WMFKI.WeakAssemblyData.regular", "WMFKI.WeakAssemblyData.selected_direction_bound",
    "WMFKI.WeakAssemblyData.oracle_recovery", "WMFKI.WeakAssemblyData.lasso_recovery",
}
EXPECTED_EXAMPLES = 26
EXPECTED_STOCHASTIC_EXAMPLES = 6
EXPECTED_STOCHASTIC_DECLARATIONS = 437


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def run(args, log=None):
    result = subprocess.run(args, cwd=PROJECT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=1800)
    if log is not None:
        log.write_text(result.stdout)
    require(result.returncode == 0, f"実行失敗: {args}\n{result.stdout}")
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--clean", action="store_true", help="このプロジェクトだけ再ビルド")
    parser.add_argument("--check-paper", action="store_true", help="今回の原稿保護ハッシュを照合")
    args = parser.parse_args()
    out = PROJECT / "verification"
    out.mkdir(exist_ok=True)
    for lock_name in ["statement-lock.json", "extension-statement-lock.json"]:
        lock = json.loads((PROJECT / lock_name).read_text())
        for name, expected in lock.items():
            require(sha(PROJECT / name) == expected, f"固定仕様が変更されています: {name}")
    sources = sorted((PROJECT / "Lean_Code").glob("*.lean")) + [PROJECT / "Showcase.lean"]
    stochastic_sources = sorted((PROJECT / "WMFKI_Stochastic").glob("*.lean"))
    # 意図的にコメント内も検査する保守的な検査。推移的依存は別途Leanで検査する。
    banned = re.compile(r"\b(sorry|admit|axiom|unsafe|native_decide)\b")
    for path in sources + stochastic_sources:
        require(not banned.search(path.read_text()), f"要確認の構文: {path}")
    example_count = len(re.findall(r"^example\b", (PROJECT / "Lean_Code/Human_Check.lean").read_text(), re.M))
    stochastic_example_count = len(re.findall(
        r"^example\b", (PROJECT / "WMFKI_Stochastic/HumanCheckJointRecovery.lean").read_text(), re.M))
    require(example_count == EXPECTED_EXAMPLES, f"既存例題数が不一致: {example_count}")
    require(stochastic_example_count == EXPECTED_STOCHASTIC_EXAMPLES,
            f"粒子回復例題数が不一致: {stochastic_example_count}")
    source_manifest = json.loads((PROJECT / "WMFKI_Stochastic/SOURCE_MANIFEST.json").read_text())
    stochastic_expected = set(source_manifest["audited_public_declarations"])
    require(source_manifest["module_count"] == 116, "採用モジュール数が不一致")
    require(len(stochastic_expected) == EXPECTED_STOCHASTIC_DECLARATIONS,
            "粒子回復の監査対象数が不一致")
    require(len(stochastic_expected) == len(source_manifest["audited_public_declarations"]),
            "粒子回復の監査対象に重複があります")
    declared = set()
    declaration_pattern = re.compile(
        r"^(?:noncomputable\s+)?(?:theorem|def|abbrev|structure)\s+([\w.']+)", re.M)
    for record in source_manifest["modules"]:
        adopted = PROJECT / (record["module"].replace(".", "/") + ".lean")
        require(adopted.exists() and sha(adopted) == record["adopted_sha256"],
                f"採用ソースhashが不一致: {record['module']}")
        text = adopted.read_text()
        namespaces = re.findall(r"^namespace\s+([\w.]+)", text, re.M)
        require(len(namespaces) == 1, f"監査用namespaceを一意に決められません: {record['module']}")
        declared.update(namespaces[0] + "." + name for name in declaration_pattern.findall(text))
    require(declared == stochastic_expected,
            f"採用ソースの公開宣言一覧が不一致: {declared ^ stochastic_expected}")
    audit_prints = set(re.findall(
        r"^#print axioms\s+([\w.']+)", (PROJECT / "WMFKI_Stochastic/Audit.lean").read_text(), re.M))
    require(audit_prints == stochastic_expected,
            f"粒子回復Audit.leanの対象が不一致: {audit_prints ^ stochastic_expected}")
    manifest = json.loads((PROJECT / "lake-manifest.json").read_text())
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    stochastic = next(p for p in manifest["packages"] if p["name"] == "stochasticAnalysis")
    require(mathlib["rev"] == PIN, "Mathlibのmanifestが固定版と異なります")
    require(stochastic["rev"] == STOCHASTIC_PIN, "stochasticAnalysisのmanifestが固定版と異なります")
    checkout = CACHE / "lake/packages/mathlib"
    stochastic_checkout = CACHE / "lake/packages/stochasticAnalysis"
    head = run(["git", "-C", str(checkout), "rev-parse", "HEAD"]).strip()
    stochastic_head = run(["git", "-C", str(stochastic_checkout), "rev-parse", "HEAD"]).strip()
    require(head == PIN, "Mathlibのcheckoutが固定版と異なります")
    require(stochastic_head == STOCHASTIC_PIN, "stochasticAnalysisのcheckoutが固定版と異なります")
    require(not run(["git", "-C", str(checkout), "status", "--porcelain",
                     "--untracked-files=no"]).strip(), "Mathlibに追跡対象ファイルの変更があります")
    require(not run(["git", "-C", str(stochastic_checkout), "status", "--porcelain",
                     "--untracked-files=no"]).strip(), "stochasticAnalysisに追跡対象ファイルの変更があります")
    require(sha(PROJECT / "WMFKI_Stochastic/LICENSE-FUKASAWA-APACHE-2.0.txt") ==
            sha(stochastic_checkout / "LICENSE"), "Apache-2.0ライセンス写しが上流と異なります")
    lake = str(PROJECT / "scripts/lake")
    if args.clean:
        run([lake, "clean", "wmfki_formalization"], out / "clean.log")
    build_output = run([lake, "build"], out / "build.log")
    project_warnings = re.findall(r"warning: (?:Lean_Code|WMFKI_Stochastic)/", build_output)
    require(not project_warnings, "自作Leanソースに警告があります")
    external_warning_count = len(re.findall(r"warning: src/", build_output))
    audit = run([lake, "env", "lean", "Lean_Code/Human_Check.lean"], out / "axioms.log")
    stochastic_audit = run([lake, "env", "lean", "WMFKI_Stochastic/Audit.lean"],
                           out / "stochastic-axioms.log")

    def parse_audit(text):
        entries = re.findall(r"'([^'\n]+)' depends on axioms: \[([^\]]*)\]", text, re.S)
        entries += [(name, "") for name in re.findall(
            r"'([^'\n]+)' does not depend on any axioms", text)]
        require(len({name for name, _ in entries}) == len(entries), "公理監査に重複があります")
        dependencies = {}
        for name, raw in entries:
            deps = {s.strip() for s in raw.split(",") if s.strip()}
            require(deps <= ALLOWED_AXIOMS, f"追加公理への依存: {name}: {deps - ALLOWED_AXIOMS}")
            dependencies[name] = sorted(deps)
        return dependencies

    dependencies = parse_audit(audit)
    stochastic_dependencies = parse_audit(stochastic_audit)
    require(set(dependencies) == EXPECTED,
            f"既存公理監査の対象が不一致: {set(dependencies) ^ EXPECTED}")
    require(set(stochastic_dependencies) == stochastic_expected,
            f"粒子回復公理監査の対象が不一致: {set(stochastic_dependencies) ^ stochastic_expected}")
    protected = None
    if args.check_paper:
        baseline = json.loads((out / "source-baseline.json").read_text())
        protected = baseline["protected_sha256"]
        for name, expected in protected.items():
            require(sha(PROJECT.parent.parent / name) == expected, f"原稿の変更を検出: {name}")
    report = {
        "scope": "有限時間の明示的積確率モデル上で、原始初期乱数・独立Brownian入力から平均場過程と相互作用粒子系を構成し、同期第4モーメント率、実時間特徴核、母集団設計、観測・求積D0、同一実現V0を経て、productionのランダムペア既知support OLSとLASSOへ接続。公開終点はWMFKIJointAssembly.exists_particle_weak_recovery。RMS求積、識別幾何、sampling smallness、確率許容値、penalty条件は明示的仮定。",
        "lean": run([lake, "env", "lean", "--version"]).strip(),
        "mathlib_commit": head,
        "stochastic_analysis_commit": stochastic_head,
        "stochastic_analysis_license": "Apache-2.0",
        "statement_lock_unchanged": True,
        "extension_statement_lock_unchanged": True,
        "legacy_audited_declaration_count": len(dependencies),
        "stochastic_audited_declaration_count": len(stochastic_dependencies),
        "audited_declaration_count": len(dependencies) + len(stochastic_dependencies),
        "legacy_checked_example_count": example_count,
        "stochastic_checked_example_count": stochastic_example_count,
        "checked_example_count": example_count + stochastic_example_count,
        "adopted_module_count": source_manifest["module_count"],
        "clean_project_rebuild": args.clean,
        "build_passed": True,
        "project_warning_count": len(project_warnings),
        "external_dependency_warning_count": external_warning_count,
        "project_axioms": 0,
        "sorry_count": 0,
        "axiom_dependencies": dependencies,
        "stochastic_axiom_dependencies": stochastic_dependencies,
        "protected_paper_files_checked": len(protected) if protected is not None else None,
        "source_sha256": {str(p.relative_to(PROJECT)): sha(p)
                          for p in sources + stochastic_sources},
        "configuration_sha256": {name: sha(PROJECT / name) for name in
                                  ["lean-toolchain", "lakefile.toml", "lake-manifest.json",
                                   "statement-lock.json", "extension-statement-lock.json",
                                   "scripts/lake", "scripts/setup.sh", "scripts/verify.py",
                                   "WMFKI_Stochastic/SOURCE_MANIFEST.json",
                                   "WMFKI_Stochastic/THIRD_PARTY.md",
                                   "WMFKI_Stochastic/LICENSE-FUKASAWA-APACHE-2.0.txt"]},
        "limits": ["RMS求積精度は同じ実粒子Xについての明示的仮定であり、時間正則性だけからは導出しない",
                   "母集団設計の識別可能性・restricted-cone geometry、sampling smallness、確率許容値、LASSO penalty条件は回復適用時の仮定",
                   "有向ペア抽出と粒子入力は具体的な積確率空間で形式化。任意の既存joint realizationへの普遍移送は未形式化",
                   "コピーの新粒子filtrationへの追加適合性と無限時間一様率は未形式化。ただし今回の有限時間普通積分評価には不要",
                   "選択した推定量の可測性、数値ソルバーの正当性、support回復は未形式化",
                   "Mathlib全体はソース再ビルドせず公式キャッシュを利用",
                   "stochasticAnalysisは固定commitから必要な推移的モジュールをビルド。上流linter警告は記録するが、採用した自作ソースの警告0とは区別する",
                   "独立した別環境・別研究者による再検証ではない"],
    }
    (out / "validation.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print("検証成功：固定仕様不変、563宣言・32例、ビルド成功、一時公理0、sorry 0、標準公理のみ。")
    print("RMS求積・回復幾何・smallness・penalty条件は明示的仮定として残ります。")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, subprocess.TimeoutExpired) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
