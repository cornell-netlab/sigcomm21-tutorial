all:
	touch coq/extraction/Extract.v
	make -C coq
	dune build
