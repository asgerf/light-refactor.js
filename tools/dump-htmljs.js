#!/usr/bin/env node
var htmljs = require('../htmljs')
var fs = require('fs')
var code = fs.readFileSync(process.argv[2], 'utf8');
var chunks = htmljs(code);
for (i in chunks) {
    var obj = chunks[i]
    for (k in obj) {
        if (obj[k].start) {
            obj[k].txt = code.substring(obj[k].start, obj[k].end);
        }
    }
}
console.dir(chunks);
