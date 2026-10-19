.PHONY: all clean

all:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex
	cp build/main.pdf shifted-chains.pdf

clean:
	latexmk -C -outdir=build main.tex
