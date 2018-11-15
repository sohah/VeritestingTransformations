#!/usr/bin/perl

use strict;
$| = 1;
my @args = (
"/Library/Java/JavaVirtualMachines/jdk1.8.0_144.jdk/Contents/Home/bin/java",
 "-Djava.library.path=/Users/vaibhav/git_repos/VeritestingTransformations/lib/",
 "-Xmx1024m", "-ea", "-Dfile.encoding=UTF-8", "-jar",
  "/Users/vaibhav/git_repos/jpf-core/build/RunJPF.jar",
  "/Users/vaibhav/git_repos/VeritestingTransformations/src/examples/replace.jpf");
open(LOG, "-|", @args);
while (<LOG>) {
  if (/^elapsed time/) {
    print $_;
  }
}
