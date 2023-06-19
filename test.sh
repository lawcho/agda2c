#! /usr/bin/env bash

# ./agda2c.hs agda-src/Examples/Pure/Builtins.agda
./agda2c.hs fptalk/Demo.agda 2>_build/main.c

gcc _build/main.c bubs/src/bubs.c -I _build/ -I bubs/src/ -I /usr/include/ -o _build/out.run -rdynamic -g -ldl \
#  -DCONFIG_USE_DLADDR \
#  -DCONFIG_ENABLE_DEBUG_PRINTFLN \
#  -DCONFIG_DUMP_DOT_ON_WHNF \
#  -DCONFIG_DUMP_DOT_IN_REDUCTION

mkdir -p bubs/build/

{ ./_build/out.run || echo "Program crashed (exit not implemented yet)"; } 2>/dev/null

# cd bubs && make build/trace.data.js
