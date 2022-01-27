SRC = $(wildcard *.lp)
OBJ = $(SRC:%.lp=%.lpo)

default:
	lambdapi check $(SRC)

lpo: $(OBJ)

$(OBJ)&: $(SRC)
	lambdapi check -c $^

clean:
	rm -f $(OBJ)

install: lpo
	lambdapi install lambdapi.pkg $(SRC) $(OBJ)

uninstall:
	lambdapi uninstall lambdapi.pkg
