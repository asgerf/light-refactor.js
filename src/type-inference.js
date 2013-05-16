es = require('esprima');

function TypeMap() {
}
TypeMap.prototype.put = function(key, val) {
    this['$' + key] = val;
};
TypeMap.prototype.get = function(key) {
    return this['$' + key];
};
TypeMap.prototype.has = function(key) {
    return Object.hasOwnProperty(this, '$' + key);
};
TypeMap.prototype.remove = function(key) {
    delete this['$' + key];
};
TypeMap.prototype.forEach = function(callback) {
    for (var k in this) {
        if (!Object.hasOwnProperty(this,k)) {
            continue;
        }
        callback(k.substring(1), this[k]);
    }
};

function TypeNode() {
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

function TypeUnifier() {
    this.queue = [];
}
TypeUnifier.prototype.unify = function(x,y) {
    x = x.rep();
    y = y.rep();
    if (x == y)
        return;
    if (x.rank < y.rank) {
        // swap x,y so x has the highest rank
        var z = x;
        x = y;
        y = z;
    } else if (x.rank == y.rank) {
        x.rank += 1;
    }
    y.parent = x;
    x.namespace |= y.namespace;
    var src = y.prty;
    var dst = x.prty;
    for (var k in src) {
        if (!Object.hasOwnProperty(src,k))
            continue;
        if (Object.hasOwnProperty(dst,k)) {
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

/**
 * Infer types for the given ProgramCollection.
 */
function inferTypes(asts) {

    var unifier = new TypeUnifier;

    var global = new TypeNode;
    var envStack = [];
    var env = new TypeMap; // alias of top-most environment

    var Primitive = true;
    var NotPrimitive = false;

    var Void = true;
    var NotVoid = false;

    var Expr = true;
    var NotExpr = false;

    function addVarToEnv(name) {
        if (typeof name !== "string")
            throw "Not a string: " + name;
        if (!env.has(name)) {
            env.put(name, new TypeNode);
        }
    }

    function getVar(name) {
        for (var i=envStack.length-1; i>=0; i--) {
            var t = envStack[i].get(name);
            if (t)
                return t;
        }
        return global.getPrty(name);
    }
    function getType(node) {
        if (node instanceof TypeNode)
            return node;
        if (!node.type_node) {
            node.type_node = new TypeNode;
        }
        return node.type_node;
    }
    function getEnv(scope) {
        return scope.env_type || (scope.env_type = new TypeMap);
    }
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

    function unify(x) {
        x = getType(x);
        for (var i=1; i<arguments.length; i++) {
            unifier.unify(x, getType(arguments[i]));
        }
    }

    /** Scans statements for variable declarations and adds them to `env` */
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

    function visitFunction(fun, expr) {
        fun.env_type = env = new TypeMap; // create new environment
        envStack.push(env);
        for (var i=0; i<fun.params.length; i++) {
            addVarToEnv(fun.params[i].id.name); // add params to env
        }
        scanVars(node.body); // add var decls to env
        if (expr && fun.id !== null) {
            addVarToEnv(fun.id.name); // add self-reference to environment
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
            return;
        if (typeof node !== "object" || !node.type)
            throw "visitExp not called with node";
        switch (node.type) {
            case "FunctionExpression":
                visitFunction(node, Expr);
                return NotPrimitive;
            case "ThisExpression":
                unify(node, getVar("@this"));
                return NotPrimitive;
            case "ArrayExpression":
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
                return p;
            case "UnaryExpression":
                visitExp(node.argument, NotVoid);
                return Primitive;
            case "BinaryExpression":
                visitExp(node.left, NotVoid);
                visitExp(node.right, NotVoid);
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
                    unify(typ, node.consequent, node.alternate);
                }
                return p1 && p2;
            case "NewExpression":
            case "CallExpression":
                var args = node.arguments || [];
                visitExpr(node.callee, NotVoid);
                for (var i=0; i<args.length; i++) {
                    visitExpr(args, NotVoid);
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
                return Primitive;
            case "MemberExpression":
                visitExp(node.object, NotVoid);
                if (node.computed) {
                    visitExp(node.property, Void);
                    if (node.property.type === "Literal" && typeof node.property.value === "string") {
                        unify(node, getType(node.object).getPrty(node.property.value));
                    }
                } else {
                    unify(node, getType(node.object).getPrty(node.property.name));
                }
                return NotPrimitive;
            case "Identifier":
                if (node.name === "undefined") {
                    return Primitive;
                }
                unify(node, getVar(node.id.name));
                return NotPrimitive;
            case "Literal":
                return Primitive;
        }
        // The cases must return Primitive or NotPrimitive
        throw "Expression " + node.type + " not handled";
    }

    function visitStmt(node) {
        switch (node.type) {
            case "EmptyStatement":
                break;
            case "BlockStatement":
                break;
            case "ExpressionStatement":
                break;
            case "IfStatement":
                break;
            case "LabeledStatement":
                break;
            case "BreakStatement":
                break;
            case "ContinueStatement":
                break;
            case "WithStatement":
                break;
            case "SwitchStatement":
                break;
            case "ReturnStatement":
                break;
            case "ThrowStatement":
                break;
            case "TryStatement":
                break;
            case "WhileStatement":
                break;
            case "DoWhileStatement":
                break;
            case "ForStatement":
                break;
            case "ForInStatement":
                break;
            case "DebuggerStatement":
                break;
            case "FunctionDeclaration":
                break;
            case "VariableDeclaration":
                break;
            default:
                throw "Unknown statement: " + node.type;
        }
    }

    // TODO: visit AST

    unifier.complete();

}
