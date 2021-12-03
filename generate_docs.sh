#!/bin/bash -xe

[ -d "coqdocjs" ] && echo "CoqDocJS is installed." || git clone https://github.com/coq-community/coqdocjs.git

EXTRA_DIR=$(pwd)/coqdocjs/extra
DOCOPTS="-utf8 --toc --toc-depth 0 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $EXTRA_DIR/header.html --with-footer $EXTRA_DIR/footer.html"

OUTDIR=$(pwd)/docs/latest

rm -rf $OUTDIR

mkdir -p $OUTDIR/lambda2Gmu
pushd lambda2Gmu
coqdoc $DOCOPTS -R . GMu -d $OUTDIR/lambda2Gmu *.v
cp $EXTRA_DIR/resources/* $OUTDIR/lambda2Gmu/
popd

mkdir -p $OUTDIR/lambda2Gmu_annotated
pushd lambda2Gmu_annotated
coqdoc $DOCOPTS -R . GMuAnnot --external ../lambda2Gmu GMu -d $OUTDIR/lambda2Gmu_annotated *.v
cp $EXTRA_DIR/resources/* $OUTDIR/lambda2Gmu_annotated/
popd

mkdir -p $OUTDIR/translation_pdot
pushd translation_pdot
coqdoc $DOCOPTS -R . Top --external ../lambda2Gmu GMu --external ../lambda2Gmu_annotated GMuAnnot -d $OUTDIR/translation_pdot *.v
cp $EXTRA_DIR/resources/* $OUTDIR/translation_pdot/
popd

mkdir -p $OUTDIR/translation_extended
pushd translation_extended
coqdoc $DOCOPTS -R . Top --external ../lambda2Gmu GMu --external ../lambda2Gmu_annotated GMuAnnot -d $OUTDIR/translation_extended *.v
cp $EXTRA_DIR/resources/* $OUTDIR/translation_extended/
popd