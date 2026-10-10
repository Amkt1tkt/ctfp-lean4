#!/usr/bin/env bash
# 在隔离目录中构建站点（多人/多代理并行写作时互不干扰）。
#   scripts/build-isolated.sh <名字>            # 只构建
#   scripts/build-isolated.sh <名字> serve 4180 # 构建后在 4180 端口预览
set -euo pipefail
NAME=${1:?用法: build-isolated.sh <名字> [serve <端口>]}
ROOT=$(cd "$(dirname "$0")/.." && pwd)
WORK=/tmp/vp-$NAME
mkdir -p "$WORK"
rsync -a --delete --exclude '.vitepress/cache' --exclude '.vitepress/dist' "$ROOT/docs/" "$WORK/docs/"
ln -sfn "$ROOT/node_modules" "$WORK/node_modules"
cp "$ROOT/package.json" "$WORK/package.json"
cd "$WORK"
npx vitepress build docs
if [ "${2:-}" = "serve" ]; then
  npx vitepress preview docs --port "${3:-4180}"
fi
