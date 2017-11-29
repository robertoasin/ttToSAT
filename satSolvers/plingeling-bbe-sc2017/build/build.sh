#!/bin/sh
rm -rf lingeling*
tar xf ../archives/lingeling*
mv lingeling* lingeling
cd lingeling
./configure.sh
make plingeling
install -s plingeling ../../bin/
