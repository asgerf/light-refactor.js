// Unification-Based Type Inference for JavaScript
// ===============================================

(function (root, factory) { // Universal Module Definition (https://github.com/umdjs/umd)
    if (typeof exports === 'object') {
        module.exports = factory(require('./map'), require('./lib/esprima'));
    } else if (typeof define === 'function' && define.amd) {
        define(['map', 'lib/esprima'], factory);
    } else {
        root.JavaScriptBuffer = factory(root.Map, root.esprima);
    }
}(this, function (Map, esprima) {

// Ast Manipulation
// ----------------
// To simplify our work with ASTs, we define the following utility functions.
// First, to enable generic AST traversal, we define a function to get the list of
// children of an AST node.
// We use the convention that any property starting with `$` should not be considered a child node.
function children(node) {
    var result = [];
    for (var k in node) {
        if (!node.hasOwnProperty(k))
            continue;
        if (k[0] === '$')
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

// We inject parent pointers into every node. Pointer pointers let refer directly to AST nodes
// without needing to piggy-back a lot of contextual information.
// I once did the refactoring logic without parent pointers, and it wasn't pretty. Parent pointers are good.
function injectParentPointers(node, parent) {
    node.$parent = parent;
    var list = children(node);
    for (var i=0; i<list.length; i++) {
        injectParentPointers(list[i], node);
    }
}

function getEnclosingFunction(node) {
    while  (node.type !== 'FunctionDeclaration' && 
            node.type !== 'FunctionExpression' && 
            node.type !== 'Program') {
        node = node.$parent;
    }
    return node;
}

// We annotate each scope with the set of variables they declare.
function buildEnvs(node, scope) {
    if (node.type === 'Program') {
        scope = node;
        scope.$env = new Map;
    }
    switch (node.type) {
        case 'FunctionDeclaration':
        case 'FunctionExpression':
            if (node.type == 'FunctionDeclaration') {
                scope.$env.put(node.id.name, node.id);
            }
            scope = node;
            node.$env = new Map;
            for (var i=0; i<node.params.length; i++) {
                scope.$env.put(node.params[i].name, node.params[i]);
            }
            node.$env.put("arguments", node);
            break;
        case 'VariableDeclarator':
            scope.$env.put(node.id.name, node.id);
            break;
        case 'CatchClause':
            node.$env = new Map;
            node.$env.put(node.param.name, node.id);
            break;
    }
    var list = children(node);
    for (var i=0; i<list.length; i++) {
        buildEnvs(list[i], scope);
    }
}

function getVarDeclScope(node) {
    var name = node.name;
    while (node) {
        switch (node.type) {
            case 'Program':
                return node;
            case 'FunctionDeclaration':
            case 'FunctionExpression':
            case 'CatchClause':
                if (node.$env.has(name))
                    return node;
                break;
        }
        node = node.$parent;
    }
    return null;
}


// `findNodeAt` finds an AST node from an absolute source file position. More precisely, it finds the
// deepest nested node whose range contains the given position. It lets us find the identifier token
// under the user's curser when the refactoring is initiated.
function inRange(range, x) {
    return range[0] <= x && x <= range[1];
}
function findNodeAt(node, offset) {
    if (!inRange(node.range, offset))
        return null;
    var list = children(node);
    for (var i=0; i<list.length; i++) {
        var r = findNodeAt(list[i], offset);
        if (r !== null)
            return r;
    }
    return node;
}

// We extend Esprima's AST definition with a new type of node: `ProgramCollection`, and we add the `file`
// field to the Program node as well. The following should be seen as an extension to the 
// [Mozilla Parser API](https://developer.mozilla.org/en-US/docs/SpiderMonkey/Parser_API):
//
//       interface ProgramCollection {
//           programs : [Program | ProgramCollection]
//           file : String | null
//       }
//
//       interface Program {
//          ...
//          file : String | null
//       }
//
// Any Program that does not have a `file` should be placed inside a `ProgramCollection` that has a file.
// This design allows code bases with many files to be represented in a unified AST.
// Two nodes should not have the same `file`. 
function findAstForFile(node, file) {
    if (node.file === file)
        return node;
    if (node.type === 'ProgramCollection') {
        for (var i=0; i<node.programs.length; i++) {
            var r = findAstForFile(node.programs[i], file);
            if (r !== null)
                return r;
        }
    }
    return null;
}

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
    this.prty = new Map;
    this.namespace = false;
}
/** Returns root node, and performs path compression */
TypeNode.prototype.rep = function() {
    if (this.parent != this) {
        this.parent = this.parent.rep();
    }
    return this.parent;
};
/** Returns type of the given property; creating it if necessary.
    Result will be a root node. */
TypeNode.prototype.getPrty = function(name) {
    if (typeof name !== "string")
        throw "Not a string: " + name;
    var map = this.rep().prty;
    var t = map.get(name);
    if (!t) {
        t = new TypeNode;
        map.put(name, t);
    }
    return t.rep();
}


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
// There are a couple of utility functions we must establish before we do the traversal, though.
function inferTypes(asts) {
    var unifier = new TypeUnifier;

    var global = new TypeNode; // type of the global object

    // We maintain a stack of type maps to hold the types of local variables in the current scopes.
    // `env` always holds the top-most environment.
    var env = new Map;
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
        return scope.env_type || (scope.env_type = new Map);
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
            return getEnv(fun).getPrty(fun.params[index].name);
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
    // from constructors in namespaces. The following functions are called during the first traversal
    // to indicate potential methods, and what objects appear to be used as namespaces.
    var potentialMethods = []; // interleaved (base,receiver) pairs
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
    var Primitive = true; // returned to indicate expression was a primitive
    var NotPrimitive = false;

    var Void = true; // argument to indicate expression occurs in void context
    var NotVoid = false;

    var Expr = true; // argument to visitFunction to indicate it is an expression
    var NotExpr = false;

    // The AST traversal consists of three mutually recursive functions:
    //
    // - `visitStmt(node)`
    // - `visitExp(node, void_ctx)`.
    // - `visitFunction(fun, expr)`.
    function visitFunction(fun, expr) {
        fun.env_type = env = new Map; // create new environment
        envStack.push(env);
        for (var i=0; i<fun.params.length; i++) {
            addVarToEnv(fun.params[i].name); // add params to env
            fun.params[i].type_node = env.get(fun.params[i].name);
        }
        fun.$env.forEach(function (key,val) {
            addVarToEnv(key);
        });
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
                node.env_type = env = new Map; // create environment with exception var
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

    asts.global = global; // expose global object type
} /* end of inferTypes */

// Renaming Identifiers
// --------------------
// `classifyId` classifies an identifier token as a property, variable, or label.
// Property identifiers additionally have a *base* expression, denoting the object on
// which the property is accessed. Variables may be global or local.
function classifyId(node) {
    if (node.type != 'Identifier' && (node.type !== 'Literal' || typeof node.value !== 'string'))
        return null; // only identifiers and string literals can be IDs
    var parent = node.$parent;
    switch (parent.type) {
        case 'MemberExpression':
            if (!parent.computed && parent.property === node && node.type === 'Identifier') {
                return {type:"property", base:parent.object, name:node.name};
            } else if (parent.computed && parent.property === node && node.type === 'Literal') {
                return {type:"property", base:parent.object, name:node.value};
            }
            break;
        case 'Property':
            if (parent.key === node) {
                if (node.type === 'Identifier') {
                    return {type:"property", base:parent.$parent, name:node.name};
                } else if (node.type === 'Literal') {
                    return {type:"property", base:parent.$parent, name:node.value};
                }
            }
            break;
        case 'BreakStatement':
        case 'ContinueStatement':
            if (parent.label === node) {
                return {type:"label", name:node.name};
            }
            break;
        case 'LabeledStatement':
            if (parent.label === node) {
                return {type:"label", name:node.name};
            }
            break;
    }
    if (node.type === 'Identifier')
        return {type:"variable", name:node.name};
    else
        return null;
}

// To rename an identifier given some position, we find the identifier token, classify it, and then dispatch
// to the proper renaming function (defined below).
function computeRenaming(ast, file, offset) {
    var targetAst = findAstForFile(ast);
    if (targetAst === null) {
        throw new Error("Could not find AST for file " + file);
    }
    var node = findNodeAt(ast, offset);
    if (node === null)
        return null;
    var idClass = classifyId(node);
    if (idClass === null)
        return null;
    var groups;
    switch (idClass.type) {
        case 'variable':
            var scope = getVarDeclScope(node);
            if (scope.type === 'Program') {
                inferTypes(ast);
                groups = computeGlobalVariableRenaming(ast, node.name);
            } else {
                groups = computeLocalVariableRenaming(scope, name);
            }
            break;
        case 'label':
            groups = computeLabelRenaming(node);
            break;
        case 'property':
            inferTypes(ast);
            if (node.base.type_node.rep() === ast.global.rep()) {
                groups = computeGlobalVariableRenaming(ast, node.name);
            } else {
                groups = computePropertyRenaming(ast, node.name);
                reorderGroupsStartingAt(groups, file, offset);
            }
            break;
        default: throw new Error("unknown id class: " + idClass.type);
    }
    return groups;
}

// `computeRenamingGroupsForName` computes the groups for a given property name. The token
// selected by the user is not an input, because the concrete token chosen does not influence
// the choice of renaming groups.
function computePropertyRenaming(ast, name) {
    var group2members = {};
    var global = ast.global.rep().id;
    function add(base, id) {
        var key = base.type_node.rep().id;
        if (key === global)
            return; // global variables are kept separate
        if (!group2members[key]) {
            group2members[key] = [];
        }
        group2members[key].push(id);
    }
    function visit(node) {
        var clazz = classifyId(node);
        if (clazz != null && clazz.type === 'property' && clazz.name === name) {
            add(clazz.base, node);
        }
        children(node).forEach(visit);
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

function reorderGroupsStartingAt(groups, file, offset) {
    /* TODO */
}

// To rename labels, we find its declaration (if any) and then search its scope for possible references.
function getLabelDecl(node) {
    var name = node.name;
    while (node && node.type !== 'LabeledStatement' && node.label.name !== name) {
        node = node.$parent;
        if (node.type === 'FunctionDeclaration' || node.type === 'FunctionExpression')
            return null;
    }
    return node || null;
}
function computeLabelRenaming(node) {
    var name = node.label.name;
    var decl = getLabelDecl(node);
    var result;
    function visit(node) {
        switch (node.type) {
            case 'LabeledStatement':
                if (node.label.name === name)
                    return; // shadowed label
                break;
            case 'FunctionDeclaration':
            case 'FunctionExpression':
                return; // labels don't propagte inside functions
            case 'BreakStatement':
            case 'ContinueStatement':
                if (node.label !== null && node.label.name === name)
                    result.add(node.label);
                break;
        }
        children(node).forEach(visit);
    }
    var search;
    if (decl === null) { // gracefully handle error case where label was undeclared
        result = [];
        search = getEnclosingFunction(node);
    } else {
        result = [decl.label];
        search = decl.body;
    }
    visit(search);
}

// To rename global variables, we enumerate all ASTs looking for direct references as well as indirect ones through
// the global object (i.e. `window.foo`). 
// Somewhat optimistically, we assume that the user wants to rename the both types of references.
function computeGlobalVariableRenaming(ast, name) {
    var ids = [];
    var global = ast.global.rep();
    function visit(node, shadowed) {
        switch (node.type) {
            case 'Identifier':
            case 'Literal':
                var clazz = classifyId(node);
                if (clazz != null && clazz.name === name) {
                    if (clazz.type === 'variable' && !shadowed) {
                        ids.push(node);
                    } else if (clazz.type === 'property' && clazz.base.type_node.rep() === global) {
                        ids.push(node);
                    }
                }
                break;
            case 'FunctionDeclaration':
            case 'FunctionExpression':
            case 'CatchClause':
                if (node.$env.has(name)) {
                    if (!shadowed && node.type === 'FunctionDeclaration' && node.id.name === name) {
                        ids.push(node.id); // name belongs to outer scope
                    }
                    shadowed = true;
                }
                break;
        }
        var list = children(node);
        for (var i=0; i<list.length; i++) {
            visit(list[i], shadowed);
        }
    }
    visit(ast, false);
    return [ids];
}

// To rename local variables, we search its scope for references and cut off the search if the
// variable gets shadowed.
// We choose to ignore with statements because their use is frowned upon and seldom seen in practice;
// they just don't seem worth the trouble.
function computeLocalVariableRenaming(scope, name) {
    var ids = [];
    function visit(node) {
        switch (node.type) {
            case 'Identifier':
                if (node.name === name && classifyId(node).type === 'variable') {
                    ids.push(node);
                }
                break;
            case 'FunctionDeclaration':
            case 'FunctionExpression':
            case 'CatchClause':
                if (node.$env.has(name)) { // shadowed?
                    if (node.type === 'FunctionDeclaration' && node.id.name === name) {
                        ids.push(node.id); // belongs to outer scope, hence not shadowed 
                    }
                    return;
                }
                break;
        }
        children(node).forEach(visit);
    }
    visit(scope);
    return [ids];
}

// Public API
// -----------------------------------------------
// `JavaScriptBuffer` provides an AST-agnostic interface that deals with abstract file names
// and source code offsets instead of node pointers. Abstract file names are strings used to
// uniquely identify a script loaded into the buffer; they need not be paths in any file system.
// We use the following two types to describe ranges in the source code.
//
//     type Range = { range:int[2], 
//                    loc: { start:Loc, 
//                           end:Loc }}
//     type Loc = {line:int, column:int}
// 
function JavaScriptBuffer() {
    this.asts = {type:'ProgramCollection', programs:[]};
}

/**  Adds a file to this buffer. 
     `file` can be any string unique to this file, typically derived from the file name.
     Files with the same `global_id` share the same global object. */
JavaScriptBuffer.prototype.add = function(file, source_code, global_id) {
    global_id = global_id || "default";
    var ast = esprima.parse(source_code, {range:true, tolerant:true, loc:true});
    this.addAST(file, ast, global_id);
};

/** Adds a file to this buffer provided the AST of the source code. 
    The AST must have been produced with the Esprima option `ranges:true`.
    If you don't already have an AST, then use `add` instead. */
JavaScriptBuffer.prototype.addAST = function(file, ast, global_id) {
    ast.file = file;
    ast.global_id = global_id;
    injectParentPointers(ast);
    buildEnvs(ast);
    this.asts.programs.push(ast);
};

/** If true, renaming the identifier at the given offset does not affect other files */
JavaScriptBuffer.prototype.canRenameLocally = function(file, offset) {
    var c = this.classify(file,offset);
    return c === 'local' || c === 'label';
};

/** Returns "local", "global", "property", or "label" or null.
    For non-null return values, the identifier at the given offset can be renamed */
JavaScriptBuffer.prototype.classify = function(file, offset) {
    var ast = findAstForFile(this.asts, file);
    if (ast === null)
        return null;
    var node = findNodeAt(ast, offset);
    if (node === null)
        return null;
    var clazz = classifyId(node);
    if (clazz === null)
        return null;
    switch (clazz.type) {
        case "variable": return getVarDeclScope(node).type === 'Program' ? "global" : "local";
        case "property": return "property";
        case "label": return "label";
    }
};

/** Returns null or a Range[][] object where each Range[] is a group of tokens that are related,
    and Range denotes the type {0:<start>, 1:<end>}. */
JavaScriptBuffer.prototype.renameTokenAt = function(file,offset) {
    var list = computeRenaming(this.asts, file, offset);
    list.forEach(identifiersToRanges);
    return list;
};

JavaScriptBuffer.prototype.renamePropertyName = function(name) {
    inferTypes(this.asts);
    var list = computePropertyRenaming(this.asts, name);
    list.forEach(identifiersToRanges);
    return list;
};

/** Removes all contents of the buffer */
JavaScriptBuffer.prototype.clear = function() {
    this.asts.programs = [];
};

exports.JavaScriptBuffer = JavaScriptBuffer;


function getNodeFile(node) {
    while (node && !node.file) {
        node = node.$parent;
    }
    return node && node.file;
}
function identifierRange(node) {
    delta = node.type === 'Literal' ? 1 : 0; // skip quote
    return {
        file: getNodeFile(node),
        start: {
            offset: node.range[0] + delta,
            line: node.loc.start.line,
            column: node.loc.start.column + delta
        },
        end : {
            offset: node.range[1] - delta,
            line: node.loc.end.line,
            column: node.loc.end.column - delta
        }
    };
}
function identifiersToRanges(list) {
    for (var i=0; i<list.length; i++) {
        list[i] = identifierRange(list[i]);
    }
}
    
return JavaScriptBuffer

})); // end of UMD
