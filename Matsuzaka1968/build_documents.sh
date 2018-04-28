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

if [ "$("$ISABELLE_HOME/bin/isabelle" getenv -b ISABELLE_LATEX)" != "uplatex" ]; then
    echo 'ISABELLE_LATEX=uplatex' >> "$ISABELLE_HOME_USER/etc/settings"
fi

rm -rf "$ISABELLE_BROWSER_INFO/Unsorted/Matsuzaka1968"
(cd "$THIS_DIR" && "$HOME/isabelle/bin/isabelle" build -D . -c -j `nproc` -v -o 'browser_info' -o 'document=dvi')
(cd "$ISABELLE_BROWSER_INFO/Unsorted/Matsuzaka1968" && dvipdfmx document.dvi && rm document.dvi)

(cd "$THIS_DIR" && rm -rf output && mkdir -p output)
cp -r "$ISABELLE_BROWSER_INFO/Unsorted/Matsuzaka1968" -t output
