#!/bin/sh

LC_TIME="en_US"
export LC_TIME

die () {
   echo "*** mkconfig.sh: $*" 1>&2
   exit 1
}

[ -f makefile ] || die "can not find 'makefile'"

cat<<EOF
/*************************************************************/
/* Automatically generated by './mkconfig.sh': do note edit! */
/*************************************************************/
EOF

echo "#define LGL_OS \"`uname -srmn`\""
echo "#define LGL_COMPILED \"`date`\""
cat<<EOF
#define LGL_RELEASED "Wed Jun  7 15:19:03 CEST 2017"
#define LGL_VERSION "bbe"
#define LGL_ID "d35430ca305be47ff998f3af610579bfa6f1fbac"
EOF
