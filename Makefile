all: publications.bib
	node bibtexgen/bibtexgen.js publications.bib > publications.html

clean:
	rm publications.html