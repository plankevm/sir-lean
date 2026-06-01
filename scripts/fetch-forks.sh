#!/usr/bin/env sh
set -eu

ROOT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
FORKS_DIR="$ROOT_DIR/forks"

mkdir -p "$FORKS_DIR"

clone_or_update() {
  name="$1"
  url="$2"
  rev="$3"
  dest="$FORKS_DIR/$name"

  if [ -d "$dest/.git" ]; then
    echo "Updating $name"
    git -C "$dest" fetch origin
  else
    echo "Cloning $name"
    git clone "$url" "$dest"
  fi

  git -C "$dest" checkout "$rev"
}

clone_or_update "EVMYulLean" "https://github.com/NethermindEth/EVMYulLean.git" "047f63070309f436b66c61e276ab3b6d1169265a"
clone_or_update "verity" "https://github.com/lfglabs-dev/verity.git" "30777c293e1cb9e7ce307833cb69f01d1400a666"
clone_or_update "verifereum" "https://github.com/verifereum/verifereum.git" "114e4d3d6b605c84d9b27bf772fb2a76dc93bff2"
clone_or_update "vyper-hol" "https://github.com/verifereum/vyper-hol.git" "fbb5a4043229da8d769c8f18a28389bc1fd4fc38"
clone_or_update "plank-monorepo" "https://github.com/plankevm/plank-monorepo.git" "adc751211c404f33210fa5a48417474c9302913b"

echo "Done. Forks are available under $FORKS_DIR."
