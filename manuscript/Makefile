.PHONY: all clean

all:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex
	cp build/main.pdf finite-extraction.pdf

clean:
	latexmk -C -outdir=build main.tex
