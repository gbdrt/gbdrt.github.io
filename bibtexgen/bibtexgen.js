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

const link = (file, url, body) => {
    var content = ''
    var target = file ? file : (url ? url : '')
    content += '<a href="' + target + '">' + body + '</a>'
    return content
}

const cleansort = (bib, kinds) => {
    var res = {}
    bib.forEach(elem => {
        const entry = elem.entryTags
        entry.bibtype = elem.entryType.toLowerCase()
        if (kinds.includes(entry.bibtype)) {
            year = parseInt(entry.year)
            if (res[year]) {
                res[year].unshift(entry)
            } else {
                res[year] = [entry]
            }
        }
    })
    return res
}

const dump = (sortbib) => {
    Object.keys(sortbib).sort((a, b) => { return b - a }).forEach(year => {
        var content = ''
        content += html('div', "col-sm-1", year)
        var body = ''
        sortbib[year].forEach(entry => {
            var list = ""
            if (entry.bibtype !== 'inbook') {
                list += html('div', 'title', link(entry.file, entry.url, entry.title) + ",")
            } else {
                list += html('div', 'title', link(entry.file, entry.url, entry.chapter) + ",")
            }

            list += html('span', 'author', entry.author).replace(/ and /g, ", ")
            if (entry.bibtype === 'inproceedings' || entry.bibtype === 'incollection' || entry.bibtype === 'unpublished') {
                list += html('span', 'desc', ' in ' + entry.booktitle)
            } else if (entry.bibtype === 'inbook') {
                list += html('span', 'desc', ' in ' + entry.title)
            } else if (entry.bibtype === 'article') {
                list += html('span', 'desc', ' in ' + entry.journal + '&nbsp;' + entry.volume + '(' + entry.number + ')')
            } else if (entry.bibtype === 'techreport') {
                list += html('span', 'desc', entry.type + " " + entry.institution + "&nbsp;" + entry.number)
            } else if (entry.bibtype === 'phdthesis') {
                list += html('span', 'desc', "PhD Thesis")
            }
            if (entry.note) {
                list += html('div', 'note', entry.note)
            }
            body += html('div', 'bibitem', list)
        })
        content += html('div', "col-sm-11", body)
        content = html('div', "row", content)
        console.log(content)
    })
}

const file = fs.readFileSync(process.argv[2], "utf8");
var bib = bibtexParse.toJSON(file);
var sortbib = cleansort(bib, ['inproceedings', 'article', 'phdthesis', 'inbook', 'incollection', 'misc'])
console.log('<h2> Publications </h2>')
console.log('<p>See also <a href="https://dblp.org/pid/137/3096.html">DBLP</a> or <a href="https://scholar.google.com/citations?user=8A29HxcAAAAJ">Google Scholar</a></p>')
dump(sortbib)

// var sortbib_patent = cleansort(bib, ['misc'])
// console.log('<h2> Patents </h2>')
// dump(sortbib_patent)

// var sortbib_draft = cleansort(bib, ['techreport', 'unpublished'])
// console.log('<h2> Preprints, Posters </h2>')
// dump(sortbib_draft)
