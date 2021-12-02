#!/bin/bash -xe

rm -rf dependencies/
mkdir dependencies
cd dependencies
git clone https://github.com/Linyxus/extended-pdot-calculus.git
git clone https://github.com/amaurremi/dot-calculus.git

pushd dot-calculus/src/extensions/paths/
git checkout c9086d10e23d82f4d5cb41c46e2d9e1ebe989eec
make
popd
pushd extended-pdot-calculus/src/
git checkout 4ce81d7a6445826c6697962764fa9db0028ad6db
make
popd