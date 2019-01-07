var bibtexParse = require('bibtex-parse-js');
var fs = require('fs');

var file = fs.readFileSync('publications.bib', "utf8");

var sample = bibtexParse.toJSON(file);

console.log(sample);
