MAKEFLAGS += -r -k -j$(shell nproc)

LPO_MK := lpo.mk

EXCLUDE := _opam
EXCEPT := $(EXCLUDE:%=! -path './%*')

LP := $(shell find . -name '*.lp' $(EXCEPT) -print)

.PHONY: default
default: $(LP:%=%o)

%.lpo: %.lp
	@echo lambdapi check $< ...
	@lambdapi check -c -v 0 $<

include $(LPO_MK)

$(LPO_MK): $(LP)
	@echo create/update $@ ...
	@lambdapi depend $(LP) > $@

.PHONY: clean
clean:
	-find . -name '*.lpo' $(EXCEPT) -delete
	-rm $(LPO_MK)
