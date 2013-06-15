#!/usr/bin/env node
var JavaScriptBuffer = require('../type-inference'),
    fs = require('fs'),
    clc = require('cli-color');

var filename = process.argv[2];
var text = fs.readFileSync(filename, {encoding:"utf8"});
var lines = text.split(/\r?\n|\r/);
var buffer = new JavaScriptBuffer;
buffer.add(filename, text);
var groups = buffer.renamePropertyName(process.argv[3] || "add");
groups.forEach(function(group) {
    console.log(clc.green("---------------- (" + group.length + ")"));
    group.forEach(function (item,index) {
        if (index > 0) console.log(clc.blackBright("--"));
        var idx = item.start.line - 1;
        var line = lines[idx];
        line = clc.black(line.substring(0,item.start.column)) + 
               clc.red(line.substring(item.start.column, item.end.column)) +
               clc.black(line.substring(item.end.column));
        console.log(clc.black(lines[idx-1]) || '');
        console.log(line);
        console.log(clc.black(lines[idx+1]) || '');
    });
});
console.log(clc.green("----------------"));
