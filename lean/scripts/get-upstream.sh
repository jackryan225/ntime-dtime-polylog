#!/bin/sh
# Fetch the third-party Lean sources of the proof at the audited commits, apply the patches, and check every file.
#
#   sh scripts/get-upstream.sh            (run from lean/; needs git >= 2.27, patch, and network access to github.com)
#
# What it does:
#   1. openai/math at commit 3344da59991ed94f9ba711217b29c1d760badfa6 (Apache License 2.0): a sparse, blob-less clone of
#      lean/OAI and lean/patches only. The 2,290 files listed in upstream/openai-files.txt are copied to OAI/.
#      Six of them are then changed by our two patches (patches/field-uniform.patch, then patches/port-over.patch).
#   2. ZIB-IOL/lemmata at commit a2dd430f283febd755a6ee6932d0b0fdabfb330c (the commit that openai/math pins). The 31 files
#      listed in upstream/lemmata-files.txt are copied to Lemmata/ and patched with openai/math's own
#      lean/patches/lemmata-lean4341.patch (its hunks for these 31 files).
#   3. Every source file of the proof (ours and the fetched ones, 3,067 files) is checked against CLOSURE-SHA256SUMS.
#      The script stops with an error if one file differs.
#
# To use existing checkouts instead of cloning: OPENAI_MATH_DIR=<openai/math checkout> LEMMATA_DIR=<lemmata checkout>.
# They must be at the commits above (the script checks the commit when the folder is a git checkout).
set -eu
cd "$(dirname "$0")/.."
OAI_COMMIT=3344da59991ed94f9ba711217b29c1d760badfa6
LEMMATA_COMMIT=a2dd430f283febd755a6ee6932d0b0fdabfb330c
TOP=$(pwd)
WORK="$TOP/.upstream"
mkdir -p "$WORK"

checkrev() {  # $1 folder, $2 commit
  if [ -e "$1/.git" ]; then
    rev=$(git -C "$1" rev-parse HEAD)
    [ "$rev" = "$2" ] || { echo "error: $1 is at $rev, not at $2" >&2; exit 1; }
    echo "  $1 is at $2"
  else
    echo "  $1 is not a git checkout; its files are checked by sha256 below"
  fi
}

echo "1. openai/math @ $OAI_COMMIT"
if [ -n "${OPENAI_MATH_DIR:-}" ]; then
  OM="$OPENAI_MATH_DIR"
else
  OM="$WORK/openai-math"
  if [ ! -d "$OM/.git" ]; then
    git clone --quiet --filter=blob:none --no-checkout https://github.com/openai/math.git "$OM"
    git -C "$OM" sparse-checkout init --cone
    git -C "$OM" sparse-checkout set lean/OAI lean/patches
  fi
  git -C "$OM" checkout --quiet "$OAI_COMMIT"
fi
checkrev "$OM" "$OAI_COMMIT"

n=0
while IFS= read -r p; do
  [ -n "$p" ] || continue
  mkdir -p "$(dirname "$p")"
  cp "$OM/lean/$p" "$p"
  n=$((n + 1))
done < upstream/openai-files.txt
echo "  copied $n files to OAI/"

W="$WORK/oai-patch"
rm -rf "$W"; mkdir -p "$W/OAI/Computability/MultitapeWeakETH"
for f in Cloud FieldLower FoldedGeometry GraphGeometry Main Padding Placement PortTemplates Price; do
  cp "$OM/lean/OAI/Computability/MultitapeWeakETH/$f.lean" "$W/OAI/Computability/MultitapeWeakETH/"
done
(cd "$W" && patch -p1 -s --no-backup-if-mismatch < "$TOP/patches/field-uniform.patch" \
         && patch -p1 -s --no-backup-if-mismatch < "$TOP/patches/port-over.patch")
for f in Cloud GraphGeometry Padding Placement PortTemplates Price; do
  cp "$W/OAI/Computability/MultitapeWeakETH/$f.lean" "OAI/Computability/MultitapeWeakETH/$f.lean"
done
echo "  applied patches/field-uniform.patch and patches/port-over.patch (6 files of the closure changed)"

echo "2. ZIB-IOL/lemmata @ $LEMMATA_COMMIT"
if [ -n "${LEMMATA_DIR:-}" ]; then
  LM="$LEMMATA_DIR"
else
  LM="$WORK/lemmata"
  if [ ! -d "$LM/.git" ]; then
    git clone --quiet --filter=blob:none --no-checkout https://github.com/ZIB-IOL/lemmata.git "$LM"
  fi
  git -C "$LM" checkout --quiet "$LEMMATA_COMMIT"
fi
checkrev "$LM" "$LEMMATA_COMMIT"

W="$WORK/lemmata-patch"
rm -rf "$W"; mkdir -p "$W"
n=0
while IFS= read -r p; do
  [ -n "$p" ] || continue
  mkdir -p "$W/lean/$(dirname "$p")"
  cp "$LM/lean/$p" "$W/lean/$p"
  n=$((n + 1))
done < upstream/lemmata-files.txt
# keep only the hunks of openai/math's lemmata patch that touch the 31 files
awk -v list="upstream/lemmata-files.txt" '
  BEGIN { while ((getline l < list) > 0) if (l != "") keep["a/lean/" l] = 1 }
  /^diff --git / { on = ($3 in keep) }
  on' "$OM/lean/patches/lemmata-lean4341.patch" > "$W/lemmata-closure.patch"
(cd "$W" && patch -p1 -s --no-backup-if-mismatch < lemmata-closure.patch)
while IFS= read -r p; do
  [ -n "$p" ] || continue
  mkdir -p "$(dirname "$p")"
  cp "$W/lean/$p" "$p"
done < upstream/lemmata-files.txt
echo "  copied $n files to Lemmata/ and applied lean/patches/lemmata-lean4341.patch of openai/math"

echo "3. sha256 of all source files of the proof"
if command -v sha256sum >/dev/null 2>&1; then SUM="sha256sum"; else SUM="shasum -a 256"; fi
if $SUM -c --quiet CLOSURE-SHA256SUMS; then
  echo "  all $(grep -c . CLOSURE-SHA256SUMS) files match CLOSURE-SHA256SUMS"
else
  echo "error: some files differ from CLOSURE-SHA256SUMS (see above); do not trust a build of them" >&2
  exit 1
fi
echo "Done. Next: lake exe cache get && lake build"
