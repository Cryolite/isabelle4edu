#/usr/bin/env bash

set -e

THIS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if [ "$#" -ne 1 ]; then
    echo 'usage: build_documents.sh ISABELLE_HOME' >&2
    exit 1
fi

ISABELLE_HOME="$(realpath "$1")"
ISABELLE_HOME_USER="$("$ISABELLE_HOME/bin/isabelle" getenv -b ISABELLE_HOME_USER)"
ISABELLE_BROWSER_INFO="$("$ISABELLE_HOME/bin/isabelle" getenv -b ISABELLE_BROWSER_INFO)"
BIN_DIR="$(realpath "$THIS_DIR/../bin")"

if [ "$("$ISABELLE_HOME/bin/isabelle" getenv -b ISABELLE_PDFLATEX)" != "$BIN_DIR/uplatex2pdf" ]; then
    echo "ISABELLE_PDFLATEX=$BIN_DIR/uplatex2pdf" >> "$ISABELLE_HOME_USER/etc/settings"
fi

rm -rf "$ISABELLE_BROWSER_INFO/Unsorted/Matsuzaka1968"
(cd "$THIS_DIR" && "$HOME/isabelle/bin/isabelle" build -D . -c -j `nproc` -v -o 'browser_info' -o 'document=pdf')

(cd "$THIS_DIR" && rm -rf output && mkdir -p output)
cp -r "$ISABELLE_BROWSER_INFO/Unsorted/Matsuzaka1968" -t output
