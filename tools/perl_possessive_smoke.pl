#!/usr/bin/perl
use strict;
use warnings;

my $subject = "ababa";
my @cases = (
  ["possessive", qr/^(aba|ab|a)*+$/, "no"],
  ["greedy",     qr/^(aba|ab|a)*$/,  "yes"],
);

my $ok_all = 1;
for my $case (@cases) {
  my ($name, $re, $expected) = @$case;
  my $actual = ($subject =~ /$re/) ? "yes" : "no";
  print "$name\t$actual\texpected=$expected\n";
  $ok_all &&= ($actual eq $expected);
}

exit($ok_all ? 0 : 1);