#!/usr/bin/perl

use strict;

$| = 1;

die "Usage: adapter-synth.pl <SPF directory path> <RunJPF.jar path> <seed> <default adaptor(0=zero,1=identity)"
	unless @ARGV == 4;
my($spf_dir_path, $runjpf_jar_path, $rand_seed, $default_adaptor_pref) = @ARGV;

srand($rand_seed);
print "start time = " . localtime() . "\n";

my @args = ("java", "-Djava.library.path=" . $spf_dir_path . "/lib/", "-Xmx1024m", "-ea", "-Dfile.encoding=UTF-8",
	"-jar", $runjpf_jar_path, $spf_dir_path . "/src/adaptersynth/AdapterSynth.jpf");
my @printable;
for my $a (@args) {
	if ($a =~ /[\s|<>]/) {
		push @printable, "'$a'";
	} else {
		push @printable, $a;
	}
}
print "@printable\n";

sub createInitialAdapter() {
	my @args = ("java", "-cp",
		$spf_dir_path . "/build/examples:" . $spf_dir_path . "/build/adaptersynth:" . $spf_dir_path . "/build/jpf-symbc.jar",
		"-Dfile.encoding=UTF-8", "AdapterSynth", ($default_adaptor_pref == 0 ? "writeZeroAdapter" : "writeIdentityAdapter"), "args");
	open(LOG, "-|", @args);
	while (<LOG>) {
		print "  $_";
	}
	close LOG;
}

my $done = 0;
my @test_inputs = ();
# Given the specification of an adaptor, execute it with symbolic
# inputs to either check it, or produce a counterexample.
sub check_adaptor {
	my $found_ce = 0;
	open(LOG, "-|", @args);
	while (<LOG>) {
		print "  $_";
		if (/^concretizeCounterExample wrote counterExample: (.*)$/) {
			$found_ce = 1;
			push @test_inputs, $1;
			last;
		}
	}
	close LOG;
	return $found_ce;
}

my $last_adapter;
# Given a set of tests, run with the adaptor symbolic to see if we can
# synthesize an adaptor that works for those tests.
sub try_synth {
	my $found_adapter = 0;
	open(LOG, "-|", @args);
	while (<LOG>) {
		print "  $_";
		if (/^concretizeAdapter wrote adapter: (.*)$/) {
			$last_adapter = $1;
			$found_adapter = 1;
			last;
		}
	}
	close LOG;
	return $found_adapter;
}


my $start_time = time();
my $reset_time = time();
my $diff;
my $diff1;
createInitialAdapter();
while (!$done) {
	printf "Running counterexample search";
	my $res = check_adaptor();
	$diff = time() - $start_time;
	$diff1 = time() - $reset_time;
	print "elapsed time = $diff, last CE search time = $diff1\n";
	$reset_time = time();
	if ($res != 1) {
		print "Success!\n";
		$done = 1;
		for my $tr (@test_inputs){
			print " $tr\n";
		}
		print "last adapter = $last_adapter\n";
		print "end time = " . localtime();
		last;
	} else {
		print "Mismatch found\n";
	}
	if (try_synth() != 1) {
		print "Failure!\n";
		$done = 1;
		for my $tr (@test_inputs){
			print " $tr\n";
		}
		print "end time = " . localtime();
		last;
	}
	$diff = time() - $start_time;
	$diff1 = time() - $reset_time;
	print "elapsed time = $diff, last AS search time = $diff1\n";
	$reset_time = time();
}
