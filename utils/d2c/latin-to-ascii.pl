#!/bin/perl -w

# Transliterate 8-bit latin-1 chars used in the .d files to 7-bit
# ascii equivalents.

use strict;


# � (FC) (1078 instances) -> ue
# � (E4) (766 instances)  -> ae
# � (F6) (348 instances)  -> oe
# � (DC) (224 instances)  -> Ue
# � (DF) (92 instances)   -> ss
# � (BF) (19 instances)   -> ?
# � (E9) (5 instances)    -> e
# � (B5) (2 instances)    -> micro
# � (D6) (2 instances)    -> Oe
# � (E8) (2 instances)    -> e
# � (AB) (1 instance)     -> "
# � (BB) (1 instance)     -> "
# � (FB) (1 instance)     -> u

while (<>) {
  s/�/ue/g;
  s/�/ae/g;
  s/�/oe/g;
  s/�/Ue/g;
  s/�/ss/g;
  s/�/?/g;
  s/�/e/g;
  s/�/micro/g;
  s/�/Oe/g;
  s/�/e/g;
  s/\�/\"/g;
  s/\�/\"/g;
  s/�/u/g;
  print;
}

__END__
