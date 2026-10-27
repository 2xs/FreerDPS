all: Makefile.rocq PoS-NSB/Makefile.rocq
	@set -e; \
	build_start=$$(date +%s); \
	$(MAKE) -f Makefile.rocq all; \
	$(MAKE) pos; \
	build_elapsed=$$(( $$(date +%s) - build_start )); \
	echo "====== Full build succeeded in $${build_elapsed}s ======"

pos: internships/PoS-NSB/Makefile.rocq
	$(MAKE) -C internships/PoS-NSB -f Makefile.rocq all

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq cleanall
	$(MAKE) clean-pos

clean-pos: PoS-NSB/Makefile.rocq
	$(MAKE) -C internships/PoS-NSB -f Makefile.rocq cleanall

PoS-NSB/Makefile.rocq: internships/PoS-NSB/_CoqProject
	$(MAKE) -C internships/PoS-NSB -f ../../Makefile Makefile.rocq

Makefile.rocq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.rocq

_CoqProject Makefile: ;

%: Makefile.rocq
	$(MAKE) -f Makefile.rocq $@

.PHONY: all clean pos clean-pos
