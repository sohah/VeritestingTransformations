#!/usr/bin/perl

use List::Util 'shuffle';
use strict;
$| = 1;

# run this script with args 0 16 <log-file> <rand-seed>
my ($this_bucket, $num_buckets, $log_file, $rand_seed) = @ARGV;
srand($rand_seed);
my $error_log_file = $log_file . ".error";
open (STDOUT, "| tee -ai $log_file");
open (STDERR, "| tee -ai $error_log_file");
die "incorrect this_bucket number given" unless $this_bucket < $num_buckets && $this_bucket >= 0; 


$ENV{'VERIDIR'} = '/export/scratch/vaibhav/VeritestingTransformations-minPrint/';
$ENV{'TARGET_CLASSPATH_WALA'} = $ENV{'VERIDIR'} . '/build/examples';
$ENV{'LD_LIBRARY_PATH'} = $ENV{'LD_LIBRARY_PATH'} . ':' . $ENV{'VERIDIR'} . '/lib';
print $ENV{'VERIDIR'} . "\n";
print $ENV{'TARGET_CLASSPATH_WALA'} . "\n";
print $ENV{'LD_LIBRARY_PATH'} . "\n";
my @args = (
   "java", "-Djava.library.path=/export/scratch/vaibhav/VeritestingTransformations-minPrint/lib", "-Xmx1024m", "-ea", 
"-Dfile.encoding=UTF-8", "-jar", "/export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar",
"/export/scratch/vaibhav/VeritestingTransformations-minPrint/src/examples/replace.mode3.jpf" 
    );
my $min_time = 86400000;
my $min_region_index = -1;
my $min_instances = 0;
my $min_regions = "";
my $max_ind = (1 << 17);
my $min_path_count = 0;
my $bucket_size = int(($max_ind / ($num_buckets - 0.0)) + 0.99); # computes ceiling fn

my $i_from = $this_bucket * $bucket_size;
my $i_to = ($this_bucket + 1) * $bucket_size;
$i_to = $i_to > $max_ind ? $max_ind : $i_to;

print "i_from = $i_from, i_to = $i_to\n";
my @array = [];
for (my $i = $i_from; $i < $i_to; $i++) {
  push @array, $i;	
}

my @shuffled_array = shuffle(@array);

for my $ind (0 .. $#shuffled_array)
{
    my $i = $shuffled_array[$ind];
    $ENV{'REGION_BV'} = $i;
    open(LOG, "-|", @args);
    my $region_instances = -1;
    my $grab_regions = 0;
    my $this_regions = "";
    my $this_path_count = 0;
    my $this_time = 86400000;
    while (<LOG>) {
        chomp $_;
        # print $_ . "\n";
        if (/^Number of Veritested Regions Instances = (.*)$/) {
            $region_instances = $1;
            # print 'region instances = ' . $region_instances . "\n";
        }
        if (/new=(.*),visited=(.*),backtracked=(.*),end=(.*)$/) {
            $this_path_count = $4;
            # print "this_path_count = $this_path_count, $this_time, $min_time\n";
            if ($this_time < $min_time && $region_instances > 0) {
        	$min_time = $this_time;
        	$min_region_index = $i;
        	$min_instances = $region_instances;
        	$min_regions = $this_regions;
        	$min_path_count = $this_path_count;
          }
        }
        if (/^Finished printing keys of regions that were instantiated at least once/) {
            $grab_regions = 0;
        }
        if ($grab_regions == 1) {
            $this_regions = $this_regions . $_ . ", ";
        }
        if (/^Printing keys of regions that were instantiated at least once/) {
            $grab_regions = 1;
        }
        if (/elapsed time:.*\((.*) msecs\)/) {
          if ($region_instances > 0) {
            # print $_;
            $this_time = $1;
            # print 'time = ' . $this_time . "\n";
          } 
        }
    }
    print "i = $i, ";
    if ($region_instances <= 0) {
      print "didn't veritest, ";
    }
    my $this_region_count= $this_regions =~ tr/,//;
    my $min_region_count= $min_regions =~ tr/,//;
    print "this_time = $this_time, this instances = $region_instances, this_path_count = $this_path_count, this region count = $this_region_count, this regions = $this_regions\n";
    print "min time = $min_time, min region index = $min_region_index, min instances = $min_instances, min path count = $min_path_count, min region count = $min_region_count, min regions = $min_regions\n\n";
}
close(STDOUT);
close(STDERR);
