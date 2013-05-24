// Parse command-line arguments
var files = [];
for (var i=2; i<process.argv.length; i++) {
	var arg = process.argv[i];
	if (arg[0] === '-') {
		console.error("Unknown option " + arg);
		process.exit(1);
	}
	files.push(arg);
}

var lr = require('./type-inference');
var fs = require('fs');
var clc = require('cli-color');
var readline = require('readline');

// Load files
var buffer = new lr.JavaScriptBuffer;
var file2lines = {};
files.forEach(function (filename) {
	var text = fs.readFileSync(filename, {encoding:"utf8"});
	file2lines[filename] = text.split(/\r?\n|\r/);
	buffer.add(filename, text);
});

var rl = readline.createInterface({input:process.stdin, output:process.stdout});

rl.question("Name of property to rename?\n> ", function (name) {
	var renaming = buffer.renamePropertyName(name);
	renaming.forEach(function (group) {
		var item = group[0];
		console.log(file2lines[item.file][item.start.line]);
	});
	var text = texts[]
	rl.close();
});
