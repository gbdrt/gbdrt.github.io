all: publications selected

publications: publications.bib
	node bibtexgen/bibtexgen.js publications.bib > publications.html

selected: selected_publications.bib
	node bibtexgen/bibtexgen.js selected_publications.bib > selected_publications.html


clean:
	rm publications.html selected_publications.html