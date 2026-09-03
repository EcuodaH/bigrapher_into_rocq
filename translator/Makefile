ROCQ  := rocq c -R . BigTool
VFILES := BigAst.v BigParser.v PrintV.v Lexer.v Translate.v Extract.v

.PHONY: all driver clean run

all: driver

BigParser.v: BigParser.vy
	menhir --coq $<

big2v.ml big2v.mli: $(VFILES)
	$(ROCQ) BigAst.v
	$(ROCQ) BigParser.v
	$(ROCQ) PrintV.v
	$(ROCQ) Lexer.v
	$(ROCQ) Translate.v
	$(ROCQ) Extract.v

driver: big2v.ml
	dune build ./driver.exe

# usage : make run IN=tests/deadlock.big OUT=tests/deadlock.v
run: driver
	dune exec ./driver.exe -- $(IN) $(OUT)

clean:
	rm -f *.vo *.vok *.vos *.glob *.aux BigParser.v big2v.ml big2v.mli
	rm -rf _build
