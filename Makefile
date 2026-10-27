MAKEFLAGS += -r -k -j$(shell nproc)

LPO_MK := lpo.mk

EXCLUDE := _opam
EXCEPT := $(EXCLUDE:%=-path ./% -prune -o)

LP := $(shell find . $(EXCEPT) -name '*.lp')

.PHONY: default
default: $(LP:%=%o)

%.lpo: %.lp
	@echo lambdapi check $< ...
	@lambdapi check -c -v 0 $<

include $(LPO_MK)

$(LPO_MK): $(LP)
	@echo create/update $@ ...
	lambdapi depend $(LP) > $@

.PHONY: clean
clean:
	-find . $(EXCEPT) -name '*.lpo' -delete
	-rm $(LPO_MK)
