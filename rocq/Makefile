LPFILES := $(wildcard ../*.lp)
VFILES := $(LPFILES:../%.lp=%.v)
VOFILES := $(VFILES:%=%o)

default: v

v: $(VFILES)

%.v: encoding.lp mappings.lp ../%.lp
	lambdapi export -o stt_coq --encoding encoding.lp --use-notations --mapping mappings.lp --requiring mappings ../$*.lp > $@ #--renaming $(HOL2DK_DIR)/renaming.lp --requiring "$(REQUIRING)"

clean-v:
	rm -f $(VFILES)

rocq.mk: _CoqProject
	rocq makefile -f _CoqProject -o $@

vo: rocq.mk
	$(MAKE) -f rocq.mk

clean-vo:
	rm -f $(VOFILES)
