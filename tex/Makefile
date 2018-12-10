.PHONY: outline.pdf all clean

all: outline.pdf

outline.pdf: outline.tex
	latexmk -pdf -pdflatex="pdflatex -interaction=nonstopmode" -use-make $<

clean:
	latexmk -CA
