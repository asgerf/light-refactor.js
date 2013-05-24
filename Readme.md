Lightweight analysis tools for JavaScript, geared towards automated refactoring support.

Usage (so far):
	
	var jsb = new JavaScriptBuffer;
	jsb.add(<filename>, <source code>);
	var groups = jsb.renameTokenAt(<file>, <offset>);
	
The groups returned are of type `Range[][]` given the following type schema:

    interface Position {
    	offset: int;
    	line: int;
    	column: int;
    }
    interface Range {
    	file: string;
    	start: Position
    	end: Position
    }

Each `Range[]` object in the topmost array is one group of identifiers that should be renamed together.