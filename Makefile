%: %.idr
	idris -o $@ $<
	time ./$@