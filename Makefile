.PHONY: BT
BT: BT.pdf

BT.pdf: BT.tex
	latexmk -pdf BT

BT.tex: BT.lhs
	lhs2TeX --agda BT.lhs -o BT.tex

.PHONY: clean
clean:
	latexmk -C BT
	rm BT.tex
