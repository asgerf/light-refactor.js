var lr = require('./type-inference');
var fs = require('fs');
var clc = require('cli-color');
var readline = require('readline');
var _ = require('underscore');
var Map = require('./map').Map;

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


// Load files
var buffer = new lr.JavaScriptBuffer;
var file2text = new Map; // TODO: avoid overhead from double representation
var file2lines = new Map;
files.forEach(function (filename) {
	var text = fs.readFileSync(filename, {encoding:"utf8"});
	file2text.put(filename, text);
	file2lines.put(filename, text.split(/\r?\n|\r/));
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
	print(file2lines.get(item.file)[item.start.line-2]);
	console.log(highlight(file2lines.get(item.file)[item.start.line-1], item.start.column, item.end.column));
	print(file2lines.get(item.file)[item.start.line]);
}

rl.question("Name of property to rename?\n> ", function (name) {
	rl.question("New of property?\n> ", function (newName) {
		queryRename(name, newName);
	});
});

function queryRename(oldName, newName) {
	var renaming = buffer.renamePropertyName(oldName);
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
					quit();
					break;
				default:
					queryNextRename(index); // keep bothering the user
			}
		});
	}
	queryNextRename(0);

	function flatten(arrays) {
		return Array.prototype.concat.apply([], arrays);
	}

	function finishRenaming() {
		var selectedGroups = renaming.filter(function (g,index) {return selected[index]});
		var items = flatten(selectedGroups);
		previewChanges(items);
	}

	function previewChanges(items) {
		var num_modifications = {};
		files.forEach(function (file) {num_modifications[file] = 0});
		items.forEach(function (item) {num_modifications[item.file]++});
		print('');
		print("----------SUMMARY-----------")
		files.forEach(function (file) {
			print(clc.green(file + " (" + num_modifications[file] + " modifications)"));
		});
		print("----------------------------");
		queryCommand(items);
	}

	function queryCommand(items) {
		print("Commit these changes?");
		print("(p) PRINT files to stdout");
		print("(w) OVERWRITE files now");
		print("(q) QUIT and discard changes");
		rl.question("> ", function(cmd) {
			switch (cmd) {
				case 'p':
					var file2text = applyChanges(items, newName)
					file2text.forEach(function (file,sb) {
						print(">> " + file);
						print(sb.toString());
					});
					queryCommand(items);
					break;
				case 'w':
					var file2text = applyChanges(items, newName);
					writeToFiles(file2text, null, quit);
					break;
				case 'q':
					quit()
					break;
				default:
					previewChanges(items);
			}
		});
	}
};

function patchDirName(dir) {
	if (dir[dir.length-1] !== '/' && dir[dir.length-1] !== '\\')
		dir += '/';
	return dir;
}

function identity(x) {
	return x;
}

function writeToFiles(file2texts, file2path, callback) {
	file2path = file2path || identity;
	var num_saved = 0;
	file2texts.forEach(function (file,text) {
		file = file2path(file);
		fs.writeFile(file, text, function(err) {
			if (err) {
				console.error("Could not write to file: " + file);
				console.error(err);
			}
			num_saved++;
			if (num_saved === files.length) {
				callback();
			}
		});
	});
}

function StringBuilder() {
	this.chunks = [];
}
StringBuilder.prototype.append = function(start) {
	this.chunks.push(start.toString());
};
StringBuilder.prototype.toString = function() {
	return this.chunks.join('');
};
StringBuilder.prototype.clear = function() {
	this.chunks = [];
};

function applyChanges(items, newName) {
	var result = new Map;
	var file2changes = Map.groupBy(items, 'file');
	files.forEach(function (file) {
		result.put(file, applyChangesToFile(file2changes.get(file), newName, file));
	});
	return result;
}

function applyChangesToFile(items, newName, file) {
	var sb = new StringBuilder;
	var text = file2text.get(file);
	items = _.sortBy(items, function (item) { return item.start.offset; });
	var offset = 0;
	for (var i=0; i<items.length; i++) {
		var item = items[i];
		sb.append(text.substring(offset, item.start.offset));
		sb.append(newName);
		offset = item.end.offset;
	}
	sb.append(text.substring(offset));
	return sb;
}

function quit() {
	rl.close();
}