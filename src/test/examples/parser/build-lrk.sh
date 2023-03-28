#!/usr/bin/env sh

#mi compile /mnt/test/examples/parser/lrk-lr2.mc && ./lrk-lr2 && mi compile lrk-lr2-gen.mc

DIR="$(dirname "$0")"

set -e

for f in $(ls "$DIR"/lrk-*.mc); do
    bn=$(basename $f)
    binname=${bn%.mc}
    mi compile "$f" && ./$binname
done
