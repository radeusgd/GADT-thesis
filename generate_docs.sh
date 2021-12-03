#!/bin/bash -xe

[ -d "coqdocjs" ] && echo "CoqDocJS is installed." || git clone https://github.com/coq-community/coqdocjs.git

EXTRA_DIR=$(pwd)/coqdocjs/extra
DOCOPTS="-utf8 --toc --toc-depth 0 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $EXTRA_DIR/header.html --with-footer $EXTRA_DIR/footer.html"

rm -rf doc

mkdir -p doc/lambda2Gmu
pushd lambda2Gmu
coqdoc $DOCOPTS -R . GMu -d ../doc/lambda2Gmu *.v
cp $EXTRA_DIR/resources/* ../doc/lambda2Gmu/
popd

mkdir -p doc/lambda2Gmu_annotated
pushd lambda2Gmu_annotated
coqdoc $DOCOPTS -R . GMuAnnot --external ../lambda2Gmu GMu -d ../doc/lambda2Gmu_annotated *.v
cp $EXTRA_DIR/resources/* ../doc/lambda2Gmu_annotated/
popd

mkdir -p doc/translation_pdot
pushd translation_pdot
coqdoc $DOCOPTS -R . Top --external ../lambda2Gmu GMu --external ../lambda2Gmu_annotated GMuAnnot -d ../doc/translation_pdot *.v
cp $EXTRA_DIR/resources/* ../doc/translation_pdot/
popd

mkdir -p doc/translation_extended
pushd translation_extended
coqdoc $DOCOPTS -R . Top --external ../lambda2Gmu GMu --external ../lambda2Gmu_annotated GMuAnnot -d ../doc/translation_extended *.v
cp $EXTRA_DIR/resources/* ../doc/translation_extended/
popd