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

function print(txt) {
	console.log(clc.black(txt));
}
function highlight(txt, start, end) {
	return clc.black(txt.substring(0, start)) + clc.red(txt.substring(start,end)) + clc.black(txt.substring(end));
}

function printRange(item) {
	print(file2lines[item.file][item.start.line-2]);
	console.log(highlight(file2lines[item.file][item.start.line-1], item.start.column, item.end.column));
	print(file2lines[item.file][item.start.line]);
}

rl.question("Name of property to rename?\n> ", function (name) {
	var renaming = buffer.renamePropertyName(name);
	var selected = {};
	function queryNextRename(index) {
		if (index >= renaming.length) {
			finishRenaming();
			return;
		}
		var group = renaming[index];
		var item = group[0];
		printRange(item);
		rl.question(clc.black("Rename this? (Y/n) "), function(answer) {
			switch (answer) {
				case 'y':
					selected[index] = true;
					queryNextRename(index+1);
					break;
				case 'n':
					selected[index] = false;
					queryNextRename(index+1);
					break;
				case 'b':
					queryNextRename(index-1);
					break;
				case 'q':
					abortRenaming();
					break;
				default:
					queryNextRename(index); // keep bothering the user
			}
		});
	}
	queryNextRename(0);

	function abortRenaming() {
		rl.close();
	}

	function finishRenaming() {
		var num_modifications = {};
		files.forEach(function (file) {num_modifications[file] = 0;});
		renaming.forEach(function(group, index) {
			if (!selected[index])
				return;
			group.forEach(function (item) {
				num_modifications[item.file]++;
			});
		});
		files.forEach(function (file) {
			console.log(clc.green(file + " (" + num_modifications[file] + " modifications)"));
		});
		rl.close();
	}
});
