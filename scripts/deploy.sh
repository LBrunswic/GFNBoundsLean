#!/usr/bin/env bash
# Ship `dashboard/` to node1. Refuses to deploy a tree whose gate is not green, because a
# dashboard that reports a build it did not run is worse than no dashboard.
#
#   scripts/deploy.sh            build the dashboard and rsync it
#   FORCE=1 scripts/deploy.sh    deploy anyway, gate or no gate
#
# Host and destination are overridable: DEPLOY_HOST, DEPLOY_DIR, DEPLOY_URL.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HOST="${DEPLOY_HOST:-node1}"
DIR="${DEPLOY_DIR:-/var/www/gfnbounds-blueprint}"
# The LAN address, because that is what actually answers. The public IP 188.211.162.184
# is the Huawei gateway, which forwards :22 to node1 and nothing else; until 8080 is
# forwarded there, "public" stops at the router. See nginx/gfnbounds-blueprint.conf.
URL="${DEPLOY_URL:-http://192.168.1.200:8080/}"

cd "$ROOT"

fail() { echo "deploy: $*" >&2; exit 1; }

if [ "${FORCE:-0}" != "1" ]; then
  [ -f build.log ] || fail "no build.log — run \`make check\` first (or FORCE=1)"
  tail -c 4000 build.log | grep -q "Build completed successfully" \
    || fail "build.log does not end in a successful build — run \`make check\` (or FORCE=1)"
  # A build.log older than a source file describes a tree that no longer exists. `-newer` is
  # mtime-based, which is exactly the question being asked.
  stale="$(find GFNBounds scaffold -name '*.lean' -newer build.log -print -quit 2>/dev/null || true)"
  [ -z "$stale" ] || fail "$stale is newer than build.log — re-run \`make check\` (or FORCE=1)"
  [ "$(cat docs/sorry.json 2>/dev/null || echo null)" = "[]" ] \
    || fail "docs/sorry.json is not empty — the strict library is not sorry-free (or FORCE=1)"
fi

[ -f dashboard/index.html ] || fail "dashboard/ not built — run \`make dashboard\`"

echo "deploy: $ROOT/dashboard/ -> $HOST:$DIR"
rsync -a --delete --omit-dir-times --no-perms --chmod=D755,F644 \
      dashboard/ "$HOST:$DIR/"

# Prove it is actually being served rather than merely copied.
code="$(curl -s -o /dev/null -w '%{http_code}' -m 15 "$URL" || echo 000)"
echo "deploy: $URL -> HTTP $code"
[ "$code" = "200" ] || fail "the site did not answer 200 — check nginx on $HOST"
echo "deploy: done"
