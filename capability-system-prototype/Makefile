# set the path of Verifier
Verifier = ./../../verus/source/target-verus/release/verus

all:
	$(Verifier) ./main.rs

time:
	$(Verifier) --time ./main.rs

compile:
	$(Verifier) --compile ./main.rs

debug:
	$(Verifier) --expand-errors ./main.rs