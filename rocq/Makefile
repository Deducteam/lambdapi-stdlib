.PREFIX:

.PHONY: default
default:
	$(MAKE) lp
	$(MAKE) dk
	$(MAKE) dko
	$(MAKE) v
	$(MAKE) vo

LPFILES := $(wildcard ../*.lp)

.PHONY: lp
lp: $(LPFILES:../%.lp=%.lp)

%.lp: ../%.lp
	sed -e 's/^opaque //' $< > $@

.PHONY: clean-lp
clean-lp: clean-dk
	-rm -f $(LPFILES)

DKFILES := $(LPFILES:../%.lp=%.dk)

.PHONY: dk
dk: $(DKFILES)

%.dk: %.lp
	lambdapi export -o dk $< > $@

.PHONY: clean-dk
clean-dk: clean-dko clean-v
	-rm -f $(DKFILES) dko.mk

.PHONY: dko
dko: $(DKFILES:%.dk=%.dko)

#DKCHECK := dk check -e
DKCHECK := lambdapi check -c --lib-root=.

%.dko: %.dk
	$(DKCHECK) $<

include dko.mk

dko.mk: $(DKFILES)
	dk dep $(DKFILES) > $@

.PHONY: clean-dko
clean-dko:
	-rm -f *.dko

VFILES := $(DKFILES:%.dk=%.v)

.PHONY: v
v: $(VFILES)

%.v: encoding.lp mapping.lp renaming.lp %.dk
	lambdapi export -o stt_coq --encoding encoding.lp --renaming renaming.lp --mapping mapping.lp --requiring mapping --use-notations $*.dk > $@

.PHONY: clean-v
clean-v: clean-vo
	-rm -f $(VFILES) rocq.mk rocq.mk.conf *.glob

rocq.mk: _CoqProject
	rocq makefile -f _CoqProject -o $@

.PHONY: vo
vo: rocq.mk
	$(MAKE) -f rocq.mk

%.vo: rocq.mk
	$(MAKE) -f rocq.mk $@

.PHONY: clean-vo
clean-vo:
	rm -f *.vo*

.PHONY: clean
clean: clean-dk
