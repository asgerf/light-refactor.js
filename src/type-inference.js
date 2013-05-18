// Unification-Based Type Inference for JavaScript
// ===============================================
 
// We use Esprima's AST definition (which itself is based on Mozilla's API) but with the following additions:
//
// - There is a new type of node called `ProgramCollection`:
//       interface ProgramCollection {
//           programs : [Program | ProgramCollection]
//           file : String | null
//       }
// - The `Program` node may have a `file` attribute:
//       interface Program {
//          ...
//          file : String | null
//       }
//
// Any Program that does not have a `file` should be placed inside a `ProgramCollection` that has a file.
// This design allows code bases with many files to be represented in a unified AST.
// Two nodes should not have the same `file`. 

// Types and Union-Find
// --------------------
// A `TypeNode` is a node in an augmented union-find data structure. Root nodes represent types.
// The `prty` field maps strings (property names) to type nodes.
// The `namespace` boolean denotes whether the type seems to be a namespace object.
// The `id` field is a unique identifier for each node.
var type_node_id = 0;
function TypeNode() {
    this.id = ++type_node_id;
    this.parent = this;
    this.rank = 0;
    this.prty = new TypeMap;
    this.namespace = false;
}
TypeNode.prototype.rep = function() {
    if (this.parent != this) {
        this.parent = this.parent.rep();
    }
    return this.parent;
};
TypeNode.prototype.getPrty = function(name) {
    if (typeof name !== "string")
        throw "Not a string: " + name;
    var map = this.rep().prty;
    var t = map.get(name);
    if (!t) {
        t = new TypeNode;
        map.put(name, t);
    }
    return t;
}

// A `TypeMap` maps strings to type nodes. It is used to store the property types of
// type nodes, and for environments.
function TypeMap() {
}
TypeMap.prototype.put = function(key, val) {
    this['$' + key] = val;
};
TypeMap.prototype.get = function(key) {
    return this['$' + key];
};
TypeMap.prototype.has = function(key) {
    return this.hasOwnProperty('$' + key);
};
TypeMap.prototype.remove = function(key) {
    delete this['$' + key];
};
TypeMap.prototype.forEach = function(callback) {
    for (var k in this) {
        if (!this.hasOwnProperty(k)) {
            continue;
        }
        callback(k.substring(1), this[k]);
    }
};

// The `TypeUnifier` implements the unification procedure of the union-find algorithm.
// Calling `unify(x,y)` will unify x and y. The `prty` maps of x and y will be partially
// merged; the merging will be completed by calling the `complete` method.
function TypeUnifier() {
    this.queue = [];
}
TypeUnifier.prototype.unify = function(x,y) {
    x = x.rep();
    y = y.rep();
    if (x === y)
        return;
    if (x.rank < y.rank) {
        var z = x; // swap x,y so x has the highest rank
        x = y;
        y = z;
    } else if (x.rank === y.rank) {
        x.rank += 1;
    }
    y.parent = x;
    x.namespace |= y.namespace;
    var src = y.prty;
    var dst = x.prty;
    for (var k in src) {
        if (k[0] !== '$')
            continue;
        if (!src.hasOwnProperty(k))
            continue;
        if (dst.hasOwnProperty(k)) {
            this.unifyLater(src[k], dst[k]);
        } else {
            dst[k] = src[k];
        }
    }
    delete y.rank;
    delete y.prty;
    delete y.namespace;
};
TypeUnifier.prototype.unifyLater = function(x,y) {
    if (x != y) {
        this.queue.push(x);
        this.queue.push(y);
    }
};
TypeUnifier.prototype.complete = function() {
    var q = this.queue;
    while (q.length > 0) {
        var x = q.pop();
        var y = q.pop();
        this.unify(x,y);
    }
};

// Type Inference
// --------------
// The type inference procedure initially assumes all expressions have distinct
// types, and then unifies types based on a single traversal of the AST.
function inferTypes(asts) {
    var unifier = new TypeUnifier;

    var global = new TypeNode; // type of the global object

    // We maintain a stack of type maps to hold the types of local variables in the current scopes.
    // `env` always holds the top-most environment.
    var env = new TypeMap;
    var envStack = [env]; 

    /** Get type of variable with the given name */
    function getVar(name) {
        for (var i=envStack.length-1; i>=0; i--) {
            var t = envStack[i].get(name);
            if (t)
                return t;
        }
        return global.getPrty(name);
    }

    /** Add variable to current environment. Used when entering a new scope. */
    function addVarToEnv(name) {
        if (typeof name !== "string")
            throw "Not a string: " + name;
        if (!env.has(name)) {
            env.put(name, new TypeNode);
        }
    }

    /** Scans a function body for variable declarations and adds them to the current environment */
    function scanVars(node) {
        if (node === null)
            return;
        if (typeof node === "undefined")
            throw "Missing node in scanVars";
        switch (node.type) {
            case "BlockStatement":
                node.body.forEach(scanVars);
                break;
            case "IfStatement":
                scanVars(node.consequent);
                scanVars(node.alternate);
                break;
            case "LabeledStatement":
                scanVars(node.body);
                break;
            case "WithStatement":
                scanVars(node.body);
                break;
            case "SwitchStatement":
                node.cases.forEach(scanVars);
                break;
            case "SwitchCase":
                scanVars(node.consequent);
                break;
            case "TryStatement":
                scanVars(node.block);
                scanVars(node.handler);
                node.guardedHandlers.forEach(scanVars);
                break;
            case "CatchClause":
                scanVars(node.body);
                break;
            case "WhileStatement":
                scanVars(node.body);
                break;
            case "DoWhileStatement":
                scanVars(node.body);
                break;
            case "ForStatement":
                scanVars(node.init);
                scanVars(node.body);
                break;
            case "ForInStatement":
                scanVars(node.left);
                scanVars(node.body);
                break;
            case "VariableDeclaration":
                node.declarations.forEach(scanVars);
                break;
            case "VariableDeclarator":
                addVarToEnv(node.id.name);
                break;
            case "FunctionDeclaration":
                addVarToEnv(node.id.name);
                break;
        }
    }

    // We create type nodes on-demand and inject them into the AST using `getType` and `getEnv`.
    /* Type of the given expression. For convenience acts as identity on type nodes */
    function getType(node) {
        if (node instanceof TypeNode)
            return node;
        if (!node.type_node) {
            node.type_node = new TypeNode;
        }
        return node.type_node;
    }
    /** Environment of the given scope node (function or catch clause) */
    function getEnv(scope) {
        return scope.env_type || (scope.env_type = new TypeMap);
    }

    // We model the type of "this" using a fake local variable called `@this`.
    // The return type of a function is modeled with a variable called `@return`.
    function thisType(fun) {
        return getEnv(fun).getPrty("@this");
    }
    function returnType(fun) {
        return getEnv(fun).getPrty("@return");
    }
    function argumentType(fun, index) {
        if (index < fun.params.length) {
            return getEnv(fun).getPrty(fun.params[index]);
        } else {
            return new TypeNode;
        }
    }

    // The `unify` function takes a number of AST nodes and/or type nodes and unifies their types.
    // It will be used a lot during the AST traversal.
    function unify(x) {
        x = getType(x);
        for (var i=1; i<arguments.length; i++) {
            unifier.unify(x, getType(arguments[i]));
        }
    }

    // To properly infer the receiver type of methods, we need a way to distinguish methods
    // from constructors in namespaces. These methods are called during the first traversal
    // to indicate potential methods, and what objects appear to be used as namespaces.
    var potentialMethods = [];
    function addPotentialMethod(base, receiver) {
        potentialMethods.push(getType(base));
        potentialMethods.push(getType(receiver));
    }

    function markAsNamespace(node) {
        getType(node).rep().namespace = true;
    }
    function markAsConstructor(node) {
        if (node.type === "MemberExpression") {
            markAsNamespace(node.object);
        }
    }

    // We use these constants to avoid confusing boolean constants
    var Primitive = true;
    var NotPrimitive = false;

    var Void = true;
    var NotVoid = false;

    var Expr = true;
    var NotExpr = false;

    // The AST traversal consists of three mutually recursive functions:
    //
    // - `visitStmt(node)`
    // - `visitExp(node, void_ctx)`.
    // - `visitFunction(fun, expr)`.
    function visitFunction(fun, expr) {
        fun.env_type = env = new TypeMap; // create new environment
        envStack.push(env);
        for (var i=0; i<fun.params.length; i++) {
            addVarToEnv(fun.params[i].name); // add params to env
            fun.params[i].type_node = env.get(fun.params[i].name);
        }
        scanVars(fun.body); // add var decls to env
        if (expr && fun.id !== null) {
            addVarToEnv(fun.id.name); // add self-reference to environment
            unify(fun, env.get(fun.id.name));
            fun.id.type_node = fun.type_node;
        }
        addVarToEnv("@this");
        addVarToEnv("@return");
        addVarToEnv("arguments");
        visitStmt(fun.body); // visit function body
        envStack.pop(); // restore original environment
        env = envStack[envStack.length-1];
    }

    function visitExp(node, void_ctx) {
        if (typeof void_ctx !== "boolean")
            throw "No void_ctx given";
        if (node === null)
            return null;
        if (typeof node !== "object" || !node.type)
            throw new Error("visitExp not called with node: " + node);
        switch (node.type) {
            case "FunctionExpression":
                visitFunction(node, Expr);
                return NotPrimitive;
            case "ThisExpression":
                unify(node, getVar("@this"));
                return NotPrimitive;
            case "ArrayExpression":
                var typ = getType(node);
                for (var i=0; i<node.elements.length; i++) {
                    var elm = node.elements[i];
                    visitExp(elm, NotVoid);
                    unify(typ.getPrty("@array"), elm);
                }
                return NotPrimitive;
            case "ObjectExpression":
                var typ = getType(node);
                for (var i=0; i<node.properties.length; i++) {
                    var prty = node.properties[i];
                    var name;
                    if (prty.key.type === "Identifier") {
                        name = prty.key.name;
                    } else if (typeof prty.key.value === "string") {
                        name = prty.key.value;
                    } else {
                        continue;
                    }
                    switch (prty.kind) {
                        case "init":
                            visitExp(prty.value, NotVoid);
                            unify(typ.getPrty(name), prty.value);
                            break;
                        case "get":
                            visitFunction(prty.value);
                            unify(typ.getPrty(name), returnType(prty.value));
                            unify(typ, thisType(prty.value));
                            break;
                        case "set":
                            visitFunction(prty.value);
                            unify(typ.getPrty(name), argumentType(prty.value, 0));
                            unify(typ, thisType(prty.value));
                            break;
                    }
                }
                return NotPrimitive;
            case "SequenceExpression":
                for (var i=0; i<node.expressions.length-1; i++) {
                    visitExp(node.expressions[i], Void);
                }
                var p = visitExp(node.expressions[node.expressions.length-1], void_ctx);
                unify(node, node.expressions[node.expressions.length-1]); // return value of last expression
                return p;
            case "UnaryExpression":
                visitExp(node.argument, Void);
                return Primitive;
            case "BinaryExpression":
                visitExp(node.left, Void);
                visitExp(node.right, Void);
                return Primitive;
            case "AssignmentExpression":
                if (typeof node.operator !== "string")
                    throw "node.operator" // TODO: debugging
                visitExp(node.left, NotVoid);
                var p = visitExp(node.right, NotVoid);
                if (node.operator === "=") {
                    if (!p) {
                        unify(node, node.left, node.right);
                    }
                    return p;
                } else {
                    return Primitive; // compound assignment operators
                }
            case "UpdateExpression":
                visitExp(node.argument, Void);
                return Primitive;
            case "LogicalExpression":
                if (node.operator === "&&") {
                    visitExp(node.left, Void);
                    var p2 = visitExp(node.right, void_ctx);
                    unify(node, node.right);
                    return p2;
                } else if (node.operator === "||") {
                    var p1 = visitExp(node.left, void_ctx);
                    var p2 = visitExp(node.right, void_ctx);
                    if (!void_ctx) {
                        unify(node, node.left, node.right);
                    }
                    return p1 && p2;
                }
            case "ConditionalExpression":
                visitExp(node.test, Void);
                var p1 = visitExp(node.consequent, void_ctx);
                var p2 = visitExp(node.alternate, void_ctx);
                if (!void_ctx) {
                    unify(node, node.consequent, node.alternate);
                }
                return p1 && p2;
            case "NewExpression":
            case "CallExpression":
                var args = node.arguments || [];
                visitExp(node.callee, NotVoid);
                for (var i=0; i<args.length; i++) {
                    visitExp(args[i], NotVoid);
                }
                if (node.callee.type === "FunctionExpression") {
                    var numArgs = Math.min(args.length, node.callee.params.length);
                    for (var i=0; i<numArgs; i++) {
                        unify(args[i], argumentType(node.callee, i));
                    }
                    unify(node, returnType(node.callee));
                    if (node.type === "NewExpression") {
                        unify(node, thisType(node.callee));
                    } else {
                        unify(global, thisType(node.callee));
                    }
                }
                if (node.type === "NewExpression") {
                    markAsConstructor(node.callee);
                }
                return NotPrimitive;
            case "MemberExpression":
                visitExp(node.object, NotVoid);
                if (node.computed) {
                    visitExp(node.property, Void);
                    if (node.property.type === "Literal" && typeof node.property.value === "string") {
                        unify(node, getType(node.object).getPrty(node.property.value));
                    } else {
                        unify(getType(node.property).getPrty("@prty-of"), node.object);
                    }
                } else {
                    unify(node, getType(node.object).getPrty(node.property.name));
                    if (node.property.name === "prototype") {
                        markAsConstructor(node.object);
                    }
                }
                return NotPrimitive;
            case "Identifier":
                if (node.name === "undefined") {
                    return Primitive;
                }
                unify(node, getVar(node.name));
                return NotPrimitive;
            case "Literal":
                return Primitive;
        }
        /* The cases must return Primitive or NotPrimitive */
        throw "Expression " + node.type + " not handled";
    }

    function visitStmt(node) {
        if (node === null)
            return;
        if (!node || !node.type)
            throw new Error("Not a statement node: " + node);
        switch (node.type) {
            case "EmptyStatement":
                break;
            case "BlockStatement":
                node.body.forEach(visitStmt);
                break;
            case "ExpressionStatement":
                visitExp(node.expression, Void);
                break;
            case "IfStatement":
                visitExp(node.test, Void);
                visitStmt(node.consequent);
                visitStmt(node.alternate);
                break;
            case "LabeledStatement":
                visitStmt(node.body);
                break;
            case "BreakStatement":
                break;
            case "ContinueStatement":
                break;
            case "WithStatement":
                visitExp(node.object, NotVoid);
                visitStmt(node.body);
                break;
            case "SwitchStatement":
                var pr = visitExp(node.discriminant, NotVoid);
                for (var i=0; i<node.cases.length; i++) {
                    var caze = node.cases[i];
                    visitExp(caze.test, pr ? Void : NotVoid);
                    caze.consequent.forEach(visitStmt);
                }
                break;
            case "ReturnStatement":
                if (node.arguments !== null) {
                    visitExp(node.argument, NotVoid);
                    unify(node.argument, getVar("@return"));
                }
                break;
            case "ThrowStatement":
                visitExp(node.argument, Void);
                break;
            case "TryStatement":
                visitStmt(node.block);
                node.handlers.forEach(visitStmt);
                node.guardedHandlers.forEach(visitStmt);
                visitStmt(node.finalizer);
                break;
            case "CatchClause":
                node.env_type = env = new TypeMap; // create environment with exception var
                envStack.push(env);
                addVarToEnv(node.param.name);
                visitStmt(node.body);
                envStack.pop(); // restore original environment
                env = envStack[envStack.length-1];
                break;
            case "WhileStatement":
                visitExp(node.test, Void);
                visitStmt(node.body);
                break;
            case "DoWhileStatement":
                visitStmt(node.body);
                visitExp(node.test, Void);
                break;
            case "ForStatement":
                if (node.init !== null && node.init.type === "VariableDeclaration") {
                    visitStmt(node.init);
                } else {
                    visitExp(node.init, Void);
                }
                visitExp(node.test, Void);
                visitExp(node.update, Void);
                visitStmt(node.body);
                break;
            case "ForInStatement":
                if (node.left.type === "VariableDeclaration") {
                    visitStmt(node.left);
                } else {
                    visitExp(node.left, Void);
                }
                visitExp(node.right, NotVoid);
                visitStmt(node.body);
                /* note: `each` is always false in Esprima */
                break;
            case "DebuggerStatement":
                break;
            case "FunctionDeclaration":
                visitFunction(node);
                unify(node, getVar(node.id.name)); // put function into its variable
                break;
            case "VariableDeclaration":
                for (var i=0; i<node.declarations.length; i++) {
                    var decl = node.declarations[i];
                    if (decl.init !== null) {
                        var pr = visitExp(decl.init, NotVoid);
                        if (!pr) {
                            unify(getVar(decl.id.name), decl.init)
                        }
                    }
                    decl.id.type_node = getVar(decl.id.name);
                }
                break;
            default:
                throw "Unknown statement: " + node.type;
        }
    }

    // We start the AST traversal with a call to visitRoot
    function visitRoot(node) {
        switch (node.type) {
            case 'Program':
                node.body.forEach(visitStmt);
                break;
            case 'ProgramCollection':
                node.programs.forEach(visitRoot);
                break;
        }
    }

    visitRoot(asts);

    // After the initial traversal, we satisfy the saturation rules to ensure we have detected namespaces.
    // Then we apply receiver-type inference and complete the unification again.
    unifier.complete();
    for (var i=0; i<potentialMethods.length; i += 2) {
        var base = potentialMethods[i].rep();
        var receiver = potentialMethods[i+1].rep();
        if (!base.namespace && !receiver.namespace) {
            /* unify later to ensure deterministic behaviour */
            unifier.unifyLater(base, receiver); 
        }
    }
    unifier.complete();
} /* end of inferTypes */

// Type Schemas
// ------------
// Type schemas are a way to showing types for human inspection and for exporting to other systems.
// This converts a type node to a type schema. For far, recursion is controlled in a fairly mundane manner.
function typeSchema(type, names) {
    type = type.rep();
    names = names || {};
    if (names[type.id]) {
        return names[type.id];
    }
    var schema = {};
    names[type.id] = "recursive[" + type.id + "]";
    type.prty.forEach(function (key,val) {
        schema[key] = typeSchema(val, names);
    });
    delete names[type.id];
    return schema;
}

function children(node) {
    var result = [];
    for (var k in node) {
        if (!node.hasOwnProperty(k))
            continue;
        var val = node[k];
        if (!val)
            continue;
        if (typeof val === "object" && typeof val.type === "string") {
            result.push(val);
        }
        else if (val instanceof Array) {
            for (var i=0; i<val.length; i++) {
                var elm = val[i];
                if (typeof elm === "object" && typeof elm.type === "string") {
                    result.push(elm);
                }
            }
        } 
    }
    return result;
}
function printTypes(ast) {
    function visit(node) {
        switch (node.type) {
            case "VariableDeclarator":
                var type = node.id.type_node.rep();
                var schema = typeSchema(type);
                console.log(node.id.name + " " + JSON.stringify(schema));
                break;
        }
        children(node).forEach(visit);
    }
    visit(ast);
}

/**
 * Denotes a position in a file.
 * - `file` is a string uniquely identifying the file in question
 * - `position` is the absolute index in the source code of the given file
 * 
 * The `file` field need not be a valid path in any file system; it may be any string.
 */
function Location(file, position) {
    this.file = file;
    this.position = position;
}
function Range(file, start, end) {
    this.file = file;
    this.start = start;
    this.end = end;
}

function Access(base, id) {
    this.base = base;
    this.id = id;
}

function inRange(range, x) {
    return range[0] <= x && x <= range[1];
}
function findAccess(node, offset) {
    if (!inRange(node.range, offset))
        return null;
    if (node.type === "MemberExpression" && !node.computed && inRange(node.property.range, offset)) {
        return {type:"property", base:node.object, id:node.property};// new Access(node.object, node.property);
    } else if (node.type === "ObjectExpression") {
        for (var i=0; i<node.properties.length; i++) {
            var prty = node.properties[i];
            if (inRange(prty.id, offset)) {
                return {type:"property", base:node, id:node.property};// new Access(node, node.property);
            }
        }
    } else if (node.type === "LabeledStatement" && inRange(node.label.range, offset)) {
        return {type:"label", base:null, id:node.label};
    } else if ((node.type === "BreakStatement" || node.type === "ContinueStatement") && node.label && inRange(node.label.range, offset)) {
        return {type:"label", base:null, id:node.label};
    } else if (node.type === "Identifier") {
        return {type:"global", base:null, id:node};
    }
    // access not found here, recurse on children
    var ch = children(node);
    for (var i=0; i<ch.length; i++) {
        var acc = findAccess(ch[i]);
        if (ac !== null) {
            if (ac.type === "global" && (node.type === "FunctionDeclaration" || node.type === "FunctionExpression")) {
                var vars = scanVars(node);
            }
            return ac;
        }
    }
    return null;
}

function computeRenamingGroupsForName(ast, name) {
    var currentFile = null;
    var group2members = {};
    function add(base, id) {
        var key = base.type_node.rep().id;
        if (!group2members[key]) {
            group2members[key] = [];
        }
        var range;
        if (id.type === 'Identifier') {
            range = new Range(currentFile, id.range[0], id.range[1]);
        } else if (id.type === 'Literal' && typeof id.value === 'string') {
            range = new Range(currentFile, id.range[0]+1, id.range[1]-1); // skip quotes on string literal
        } else {
            return; // ignore integer literals
        }
        group2members[key].push(range);
    }
    function visit(node) {
        if (node.type === 'MemberExpression' && !node.computed && node.property.name === name) {
            add(node.object, node.property);
        } else if (node.type === 'ObjectExpression') {
            for (var i=0; i<node.properties.length; i++) {
                var prty = node.properties[i];
                if (prty.id.name === name) {
                    add(node, prty.id);
                }
            }
        }
        if (node.type === 'Program') {
            currentFile = node.file;
        }
        children(node).forEach(visit);
        if (node.type === 'Program') {
            currentFile = null;
        }
    }
    visit(ast);
    var groups = [];
    for (var k in group2members) {
        if (!group2members.hasOwnProperty(k))
            continue;
        groups.push(group2members[k]);
    }
    return groups;
}

function reorderGroupsStartingAt(groups, targetLoc) {
    // TODO
}

/**
 * Computes a Range[][] object such that each Range[] in the topmost array should be renamed together.
 * The `asts` argument can be a `Program` or a `ProgramCollection` satisfying the following:
 * - Must be parsed with Esprima option `ranges:true`
 * - Must have types inferred using `inferTypes`
 * - All `Program` nodes must have a `file` field, and one of those must hold a value equal to `targetLoc.file`.
 */
function computeRenaming(ast, targetLoc) {
    var targetAst = null;
    if (ast.type === "Program" && ast.file === targetLoc.file) {
        targetAst = ast;
    } else if (ast.type === "ProgramCollection") {
        for (var i=0; i<ast.programs.length; i++) {
            if (ast.programs[i].file === targetLoc.file) {
                targetAst = ast.programs[i];
                break;
            }
        }
    }
    if (targetAst === null) {
        throw new Error("Could not find AST for file " + targetLoc.file);
    }
    var targetAccess = findAccess(targetAst, targetLoc.offset);
    var targetName = targetAccess.id.name;
    var groups = computeRenamingGroupsForName(targetName);
    reorderGroupsStartingAt(groups, targetLoc);
    return groups;
}

if (require.main === module) {
    var es = require('../lib/esprima'), fs = require('fs');
    var text = fs.readFileSync(process.argv[2], {encoding:"utf8"});
    var ast = es.parse(text, {range:true});
    // console.d
    //console.dir(ast.range);
    // console.log(JSON.stringify(ast));
    inferTypes(ast);
    var groups = computeRenamingGroupsForName(ast, "add");
    groups.forEach(function(group) {
        var texts = group.map(function(range) {return text.substring(range.start, range.end);});
        console.log(texts.join(", "));
    });
    // console.dir(groups);
    // computeRenaming(ast);
    // printTypes(ast);

}
