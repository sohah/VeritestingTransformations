#!/usr/bin/perl

use strict;
$| = 1;

my $max_region_count = 12;

$ENV{'VERIDIR'} = '/export/scratch/vaibhav/VeritestingTransformations-minPrint/';
$ENV{'TARGET_CLASSPATH_WALA'} = $ENV{'VERIDIR'} . '/build/examples';
$ENV{'LD_LIBRARY_PATH'} = $ENV{'LD_LIBRARY_PATH'} . ':' . $ENV{'VERIDIR'} . '/lib';
print $ENV{'VERIDIR'} . "\n";
print $ENV{'TARGET_CLASSPATH_WALA'} . "\n";
print $ENV{'LD_LIBRARY_PATH'} . "\n";
my @args = (
   "java", "-Djava.library.path=/export/scratch/vaibhav/VeritestingTransformations-minPrint/lib", "-Xmx1024m", "-ea", 
"-Dfile.encoding=UTF-8", "-jar", "/export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar",
"/export/scratch/vaibhav/VeritestingTransformations-minPrint/src/examples/replace.mode2.jpf" 
    );
my $min_time = 86400000;
my $min_region_index = -1;
my $min_instances = 0;
for (my $i = 1; $i < (1 <<17); $i++) {
    my $count  = 0;
    my $bin_vec = $i;
    do {
	$count++ if $bin_vec & 1;
	$bin_vec = $bin_vec >> 1;
    } while ($bin_vec > 0);
    # print $count . "\n";
    if ($count <= $max_region_count) {
      $ENV{'REGION_BV'} = $i;
      open(LOG, "-|", @args);
      my $region_instances = -1;
      while (<LOG>) {
	  #print $_;
	  if (/^Number of Veritested Regions Instances = (.*)$/) {
	      $region_instances = $1;
	      print 'region instances = ' . $region_instances . "\n";
	  }
        if (/elapsed time:.*\((.*) msecs\)/) {
          if ($region_instances > 0) {
            print $_;
	    my $this_time = $1;
            print 'time = ' . $this_time . "\n";
	    if ($this_time < $min_time) {
		$min_time = $this_time;
		$min_region_index = $i;
		$min_instances = $region_instances;
	    }
	    print 'i = ' . $i . ', min time = ' . $min_time . ', min region index = ' . $min_region_index . ", min instances = " . $min_instances . "\n\n";
          } else {
	      print "didn't veritest with i = " . $i . "\n";
	  }
	}
      }
    }
}
