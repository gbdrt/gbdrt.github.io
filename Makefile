DATE=`date "+%Y-%m-%d"`
SRC2HTML=./src2html $(DATE)
BIBTEX2HTML=bibtex2html

GENERATED= index.html talks.html

all: $(GENERATED)

.PHONY: $(GENERATED)

index.html: footer.html index.src.html
	$(SRC2HTML) footer.html index.src.html > $@

talks.html: footer.html talks.src.html
	$(SRC2HTML) footer.html talks.src.html > $@

clean: 
	rm -f *~ 

cleanall: clean
	rm -f $(GENERATED)
