#!/usr/bin/env bash
# 専用キャッシュだけを使用し、シェル設定や既存のLean環境は変更しない。
set -euo pipefail
cd "$(dirname "$0")/.."
CACHE="${WMFKI_LEAN_CACHE:-$HOME/.cache/wmfki-lean}"
export ELAN_HOME="$CACHE/elan"
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_CACHE_DIR="$CACHE/mathlib-cache"
mkdir -p "$CACHE/bootstrap" "$CACHE/lake/packages" "$CACHE/logs"

if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
  case "$(uname -s)-$(uname -m)" in
    Darwin-arm64) target=aarch64-apple-darwin ;;
    Darwin-x86_64) target=x86_64-apple-darwin ;;
    Linux-x86_64) target=x86_64-unknown-linux-gnu ;;
    Linux-aarch64) target=aarch64-unknown-linux-gnu ;;
    *) echo '未対応のプラットフォームです。' >&2; exit 1 ;;
  esac
  curl -fSL "https://github.com/leanprover/elan/releases/download/v4.2.4/elan-${target}.tar.gz" \
    -o "$CACHE/bootstrap/elan.tar.gz"
  tar xzf "$CACHE/bootstrap/elan.tar.gz" -C "$CACHE/bootstrap"
  "$CACHE/bootstrap/elan-init" -y --no-modify-path --default-toolchain none
fi
"$ELAN_HOME/bin/elan" toolchain install leanprover/lean4:v4.34.1

if [[ -L .lake ]]; then
  if [[ "$(readlink .lake)" != "$CACHE/lake" ]]; then
    echo '.lakeは別の場所を指しています。既存設定を保護するため停止します。' >&2
    exit 1
  fi
elif [[ -e .lake ]]; then
  echo '.lakeが既に存在します。上書きせず停止します。' >&2
  exit 1
else
  ln -s "$CACHE/lake" .lake
fi

if [[ ! -d "$CACHE/lake/packages/mathlib" ]]; then
  git clone --depth 1 --branch v4.34.1 https://github.com/leanprover-community/mathlib4.git \
    "$CACHE/lake/packages/mathlib"
fi
PIN=d13f23b723b8a846827a245b89c10fc7d3f11612
if [[ "$(git -C "$CACHE/lake/packages/mathlib" rev-parse HEAD)" != "$PIN" ]]; then
  echo 'Mathlibの既存checkoutが固定版と異なります。上書きせず停止します。' >&2
  exit 1
fi
STOCHASTIC_PIN=0cb33378176178d269f53a4dada439f8ecd3bf5e
if [[ -d "$CACHE/lake/packages/stochasticAnalysis" ]] && \
   [[ "$(git -C "$CACHE/lake/packages/stochasticAnalysis" rev-parse HEAD)" != "$STOCHASTIC_PIN" ]]; then
  echo 'stochasticAnalysisの既存checkoutが固定版と異なります。上書きせず停止します。' >&2
  exit 1
fi
MATHLIB_NO_CACHE_ON_UPDATE=1 ./scripts/lake update
if [[ "$(git -C "$CACHE/lake/packages/stochasticAnalysis" rev-parse HEAD)" != "$STOCHASTIC_PIN" ]]; then
  echo 'stochasticAnalysisのcheckoutが固定版と異なります。' >&2
  exit 1
fi
cmp -s "$CACHE/lake/packages/stochasticAnalysis/LICENSE" \
  WMFKI_Stochastic/LICENSE-FUKASAWA-APACHE-2.0.txt || {
  echo 'stochasticAnalysisのApache-2.0ライセンス写しが一致しません。' >&2
  exit 1
}
./scripts/lake exe cache get \
  Mathlib.Analysis.InnerProductSpace.PiL2 \
  Mathlib.Analysis.InnerProductSpace.Adjoint \
  Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional \
  Mathlib.Analysis.Matrix.Normed \
  Mathlib.Analysis.Normed.Group.Bounded \
  Mathlib.Topology.Order.Compact \
  Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic \
  Mathlib.Probability.Moments.Variance \
  Mathlib.Probability.Distributions.Uniform \
  Mathlib.Probability.ProbabilityMassFunction.Integrals \
  Mathlib.MeasureTheory.Integral.Pi \
  Mathlib.MeasureTheory.Integral.Bochner.Basic \
  Mathlib.MeasureTheory.Measure.Real \
  Mathlib.Tactic
./scripts/lake build
