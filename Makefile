LP_FILES := $(shell ls *.lp)
LPO_FILES := $(LP_FILES:%=%o)

default: $(LPO_FILES)

%.lpo: %.lp
	lambdapi --gen-obj $<

clean:
	rm -f $(LPO_FILES)
