// htmljs.js: Locates JavaScript in HTML
// =====================================

module.exports = function(code) {
	var state = 0;

	// Lexer states				// examples:
	var Init = 0;				// ""
	var OpenTag = 1; 			// "<"
	var InsideTagName = 1;		// "<foo"
	var BetweenAttributes = 2;	// "<foo "  "<foo bar=5 "
	var InsideAttrName = 3;
	var BeforeAttrValue = 4;
	var InsideAttrValue = 5;
	var InsideQuotedAttrValue = 6;
	var InsideScriptTag = 7;
	var InsideComment = 8;

	var isCloseTag = false;
	var isSelfClosingTag = false;

	var startOfTagName = -1;
	var endOfTagName = -1;
	var startOfAttrName = -1;
	var endOfAttrName = -1;
	var startOfAttrValue = -1;
	var endOfAttrValue = -1;

	// TODO: handle style tags??

	var quote = '\0';

	function match(text, start, end) {
		// TODO: experiment with faster implementations
		if (typeof end === 'undefined') {
			end = start + text.length;
		} else if (end - start !== text.length) {
			return false;
		}
		if (end >= codeLen)
			return false;
		return code.substring(start,end).toLowerCase() === text;
	}

	var codeLen = code.length;
	for (var i=0; i<codeLen; i++) {
		var c = code[i];
		switch (state) {
			case Init:
			// TODO: use inner loop to speed up?
			if (c === '<') {
				state = OpenTag;
				isCloseTag = false;
				isSelfClosingTag = false;
				startOfAttrName = endOfAttrName = -1;
			}
			break; // else stay in Init

			case OpenTag:
			switch (c) {
				case '/':
					isCloseTag = true;
					break; // stay in OpenTag
				case ' ':
				case '\r':
				case '\n':
				case '\t':
				case '\v':
					break; // stay in OpenTag
				case '>':
					state = Init; // error tolerance
					break;
				default:
					startOfTagName = i;
					state = InsideTagName;
					onEnterTagName();
					break;
			}
			break;

			case InsideTagName:
			switch (c) {
				case ' ':
				case '\r':
				case '\n':
				case '\t':
				case '\v':
					endOfTagName = i;
					state = BetweenAttributes;
					break;
				case '>':
					endOfTagName = i; // TODO: check tag
					state = Init;
					break;
				case '/':
					isSelfClosingTag = true;
					state = BetweenAttributes;
					break;
				case '-': // check for html comment: <!-- 
					if (2 == i - startOfTagName && code[startOfTagName] === '!' && code[startOfTagName+1] === '-') {
						state = InsideComment;
					}
					break;
				default:
					break;
			}
			break;

			case BetweenAttributes: // note: state also used in case space between attr name and equals
			switch (c) {
				case ' ':
				case '\r':
				case '\n':
				case '\t':
				case '\v':
					break;
				case '>':
					state = Init; // TODO: check tag
					break;
				case '/':
					isSelfClosingTag = true;
					break;
				case '=':
					if (endOfAttrName !== -1) {
						state = BeforeAttrValue; // whitespace separated attribute name from '=' symbol
					}
					break; // ignore if no attribute name preceeded us
				default:
					startOfAttrName = i;
					state = InsideAttrName;
					break;
			}
			break;

			case InsideAttrName:
			switch (c) {
				case ' ':
				case '\r':
				case '\n':
				case '\t':
				case '\v':
					state = BetweenAttributes;
					break;
				case '>':
					state = Init; // TODO: check tag
					break;
				case '/':
					isSelfClosingTag = true;
					state = BetweenAttributes;
					break;
				case '=':
					endOfAttrName = i;
					state = BeforeAttrValue;
				default:
					break;
			}
			break;

			case BeforeAttrValue:
			switch (c) {
				case ' ':
				case '\r':
				case '\n':
				case '\t':
				case '\v':
					break;
				case '>':
					state = Init; // TODO: check tag
					break;
				case '/':
					startOfAttrValue = i;
					state = InsideAttrValue;
					break;
				case '=':
					break; // multiple '=' signs
				case '"':
				case '\'':
					quote = c;
					startOfAttrValue = i+1;
					state = InsideQuotedAttrValue;
					break;
				default:
					startOfAttrValue = i;
					state = InsideAttrValue;
					break;
			}
			break;

			case InsideAttrValue:
			switch (c) {
				case ' ':
				case '\r':
				case '\n':
				case '\t':
				case '\v':
					endOfAttrValue = i;
					state = BetweenAttributes; // TODO: check attribute
					break;
				case '>':
					if (code[i-1] === '/') {
						isSelfClosingTag = true;
						endOfAttrValue = i-1;
					} else {
						endOfAttrValue = i;
					}
					// TODO: check attribute
					state = Init; // TODO: check tag
					break;
				case '/': // handle '/' as regular attribute value
				default:
					break;

			}
			break;

			case InsideQuotedAttrValue:
			if (c === quote) {
				endOfAttrValue = i; // TODO: check attribute
				state = BetweenAttributes;
			} else if (c === '\r' || c === '\n') {
				state = BetweenAttributes; // bail out if line-break inside attribute value
				// TODO: test experimentally what is the best strategy here. compare with browser behaviour.
			}
			break;

			case InsideScriptTag: // TODO: detect CDATA trick and comment trick
			// TODO: use inner loop to speed up?
			if (c === '>') {
				var j = i-1;
				loop: while (true) {
					switch (code[j]) {
						case ' ':
						case '\r':
						case '\n':
						case '\t':
						case '\v':
							j--;
							continue loop;
						case 't':
							if (match('</scrip', j-7)) {
								state = Init;
							}
							break loop;
						default:
							break loop;
					}
				}
			}
			break;

			case InsideComment:
			if (c === '>') { // end of comment: -->
				// take care not to match <!--> and <!---> (but <!----> is ok)
				if (i - startOfTagName > 3 && code[i-1] === '-' && code[i-2] === '-') {
					state = Init;
				}
			}
			break;
		}
	}
	// TODO: Try ways to avoid closure vars, and compare performance

	var isScriptTag;
	var scriptTagIsJavaScript;
	var scriptTagSrc;

	function onEnterTagName() {
		if (isCloseTag)
			return;
		isScriptTag = match('script', startOfTagName, endOfTagName);
		scriptTagSrc = null;
		scriptTagIsJavaScript = true;
	}

	function onFinishAttr() {
		if (isScriptTag) {
			if (match('type', startOfAttrName, endOfAttrName)) {
				var type = code.substring(startOfAttrValue, endOfAttrValue);
				if (!/javascript/i.test(type) && !/ecmascript/i.test(type)) {
					scriptTagIsJavaScript = false; // it's another type of script
				}
			}
			else if (match('src', startOfAttrName, endOfAttrName)) {
				scriptTagSrc = code.substring(startOfAttrName, endOfAttrName);
			}
		}
		tryEventHandler();
		tryHrefJavaScript();
	}
	function onFinishTag() {
		if (isScriptTag) {

		}
		tryScript();
	}

	function tryScript() {
		if (!isScriptTag)
			return;
		if (scriptTagSrc !== null) {
			insideScriptTag = true;
		} else {

		}
	}
	
	function tryEventHandler() {
		// TODO: handle namespace prefixes?
		// check that the atribute name starts with "on" (as in, "onload")
		if (!match('on', startOfAttrName))
			return;
		outputJavaScript({
			type: "event",
			code: {
				start: startOfAttrValue,
				end: endOfAttrValue
			},
			attr: {
				start: startOfAttrName,
				end: endOfAttrName,
			},
			tag: {
				start: startOfTagName,
				end: endOfTagName
			}
		});
	}

	function tryHrefJavaScript() {
		if (!match('a', startOfTagName, endOfTagName))
			return;
		if (!match('href', startOfAttrName, endOfAttrName))
			return;
		if (!match('javascript:', startOfAttrValue))
			return;
		outputJavaScript({
			type: "href",
			code: {
				start: startOfAttrValue+11,
				end: endOfAttrValue
			}
		});
	}

	function outputJavaScript(obj) {
		
	}

};
