#!/bin/sh
set -e -u -o pipefail
mkdir slang
curl -s -L https://github.com/MikePopoloski/slang/archive/refs/heads/master.tar.gz | tar -x -z -f - -C  slang  --strip-components=1
cd slang
patch -p1 < ../slang-eval.p
cd ..
cmake slang -B slang/build -GNinja -DMI_PROFILE=OFF
cmake --build slang/build -j --target bin/slang
