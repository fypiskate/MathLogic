GENERATE= Synt.hs Lex.hs
SRC= Main.hs Expr.hs FindMin.hs ProofGenerate.hs Merger.hs

.PHONY: all run pack clean

all: parser

run: parser
	./parser

parser: $(GENERATE) $(SRC)
	ghc -i./ -tmpdir . ./Main.hs -o parser

$(GENERATE): Synt.y Lex.x $(SRC)
	alex Lex.x -o Lex.hs
	happy Synt.y -o Synt.hs

pack: $(GENERATE) 
	zip task4.zip *

clean:
	rm -rf *.hi *.o  
	rm -rf $(GENERATE)
