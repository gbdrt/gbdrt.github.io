const bibtexParse = require('bibtex-parse-js');
const fs = require('fs');

const html = (type, style, body) => {
    var content = ''

    if (body) {
        content += '<' + type + (style ? ' class=' + style + '>' : '>')
        content += body.replace(/[\{\}\\]/g, "")
        content += '</' + type + '> '
    }
    return content
}

const cleansort = bib => {
    var res = {}
    bib.forEach(elem => {
        const entry = elem.entryTags
        entry.bibtype = elem.entryType.toLowerCase()
        year = parseInt(entry.year)
        if (res[year]) {
            res[year].push(entry)
        } else {
            res[year] = [entry]
        }
    })
    return res
}

const file = fs.readFileSync(process.argv[2], "utf8");
var bib = bibtexParse.toJSON(file);
var sortbib = cleansort(bib)

Object.keys(sortbib).sort((a, b) => { return b - a }).forEach(year => {
    var content = ''
    content += html('div', "col-sm-1", year)
    var body = ''
    sortbib[year].forEach(entry => {
        var list = ""
        list += html('div', 'title', entry.title + ",")
        list += html('span', 'author', entry.author)
        if (entry.bibtype === 'inproceedings' || entry.bibtype === 'incollection') {
            list += html('span', 'desc', ' in ' + entry.booktitle)
        } else if (entry.bibtype === 'article') {
            list += html('span', 'desc', ' in ' + entry.journal + ' ' + entry.volume + '(' + entry.number + ')')
        } else if (entry.bibtype === 'techreport') {
            list += html('span', 'desc', entry.type + " " + entry.number)
        } else if (entry.bibtype === 'phdthesis') {
            list += html('span', 'desc', "PhD Thesis")
        }
        if (entry.note) {
            list += html('div', 'note', entry.note)
        }
        body += html('div', 'bibitem', list)
    })
    content += html('div', "col-sm-11", body)
    content = html('div', "row contact", content)
    console.log(content)
})

