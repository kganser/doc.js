// Copyright 2014, Klaus Ganser <http://kganser.com>
// MIT Licensed, with this copyright and permission notice
// <http://opensource.org/licenses/MIT>

var doc = function() {
  var self, tokens = {
    id: /[a-zA-Z_$][a-zA-Z0-9_$]*/,
    number: /[0-9]+/,
    string: /'[^']*'|"[^"]*"/,
    code: /`[^`]+`/,
    '': /\s+/
  };
  var parse = function(grammar, start, tokens) {
    var symbols = {}, states = [], tokens_ = {}, grammar_ = {}, nonterminals = Object.keys(grammar);
    
    Object.keys(tokens || {}).forEach(function(token) {
      tokens_[token] = new RegExp(tokens[token].source.replace(/^\^?/, '^(?:')+')', tokens[token].ignoreCase ? 'i' : '');
    });
    tokens = tokens_;
    
    nonterminals.forEach(function(nonterminal) {
      var productions = [], production = [];
      grammar[nonterminal].forEach(function(elem) {
        var type = typeof elem;
        if (type == 'string') {
          production.push(elem);
        } else {
          productions.push([production, type == 'function' ? elem : function(values) {
            return function copy(elem) {
              var type = typeof elem;
              if (type != 'object' || !elem)
                return type == 'number' && elem >= 0 && elem < values.length && !(elem % 1)
                  ? values[elem] : elem;
              var value = {};
              if (Array.isArray(elem)) {
                value = [];
                elem.forEach(function(elem) {
                  value = value.concat(Array.isArray(elem = copy(elem)) ? elem : [elem]);
                });
              } else {
                Object.keys(elem).forEach(function(key) {
                  value[key] = copy(elem[key]);
                });
              }
              return value;
            }(elem);
          }]);
          production = [];
        }
      });
      grammar_[nonterminal] = productions;
    });
    grammar = grammar_;
    
    start[0].forEach(function(symbol) { symbols[symbol] = 1; });
    (states = start.slice(1).map(function(state) {
      return {transitions: {}, reductions: {}, raw: state};
    })).forEach(function(state, i) {
      var t = Array.isArray(state.raw) ? state.raw[0] : state.raw,
          r = Array.isArray(state.raw) ? state.raw[1] : {};
      Object.keys(t).forEach(function(symbol) {
        state.transitions[start[0][symbol-1]] = states[t[symbol]];
      });
      Object.keys(r).forEach(function(symbol) {
        var value = r[symbol],
            nonterminal = start[0][Array.isArray(value) ? value[0]-1 : value-1],
            production = nonterminal ? grammar[nonterminal][Array.isArray(value) ? value[1] : 0] : [[Object.keys(states[0].transitions)[0]], function(e) { return e; }];
        state.reductions[+symbol ? start[0][symbol-1] : ''] = [nonterminal, production[0], null, null, production[1] || function(o) { return o; }];
      });
      delete state.raw;
    });
    
    return function(string) {
      var token, match, ignore = tokens[''], substring = string, values = [], stack = [], state = states[0], i = 0;
      
      while (state) {
        token = undefined;
        
        if (ignore && (match = ignore.exec(substring))) {
          substring = substring.substr(match[0].length);
          i += match[0].length;
          continue;
        }
        
        (function(process) {
          Object.keys(state.transitions).forEach(process(false));
          Object.keys(state.reductions).forEach(process(true));
        })(function(reduce) {
          return function(symbol) {
            if (symbol && tokens.hasOwnProperty(symbol)) {
              if ((match = tokens[symbol].exec(substring)) && (!token || match[0].length > token.value.length))
                token = {symbol: symbol, value: match[0], reduce: reduce};
            } else if (!grammar.hasOwnProperty(symbol) && substring.substr(0, symbol.length) == symbol && (!token || symbol.length >= token.value.length) && (symbol || i == string.length)) {
              token = {symbol: symbol, value: symbol, reduce: reduce};
            }
          };
        });
        
        if (!token) {
          var before = string.substr(0, i),
              newlines = before.match(/\n/g),
              lastNewline = before.lastIndexOf('\n') + 1;
          throw {
            message: i == string.length ? 'Unexpected end of input' : 'Unexpected token',
            index: i,
            line: string.substring(lastNewline, (string+'\n').indexOf('\n', lastNewline)),
            row: newlines ? newlines.length : 0,
            column: i - lastNewline,
            toString: function() {
              return [this.message, this.line.replace(/\t/g, ' '), new Array(this.column+1).join(' ')+'^'].join('\n');
            }
          };
        }
        
        if (token.reduce) {
          var args = [],
              reduction = state.reductions[token.symbol];
          for (var j = reduction[1].length; j; j--) {
            state = stack.pop();
            args.unshift(values.pop());
          }
          stack.push(state);
          state = state.transitions[reduction[0]];
          values.push(reduction[4](args));
        } else {
          stack.push(state);
          values.push(token.value);
          state = state.transitions[token.symbol];
          substring = substring.substr(token.value.length);
          i += token.value.length;
        }
      }
      
      return values.pop().pop();
    };
  }({
    spec: [
      'id', ':', 'types', {name: 0, type: 2}
    ],
    named_value: [
      'id', '=', 'literal', ':', 'types', {name: 0, default: 2, type: 4},
      'spec', 0,
      '...', 0 // limit these?
    ],
    named_values: [
      'named_value', ',', 'named_values', [0, 2],
      'named_value', 0
    ],
    value: [
      'named_value', 0,
      'types', {type: 0}
    ],
    values: [
      'value', ',', 'values', [0, 2],
      'value', 0
    ],
    type: [
      'id', 0,
      'function', 0,
      'function', '(', 'values', ')', {function: {args: 2}},
      '{', 'named_values', '}', {object: 1},
      '[', 'values', ']', {array: 1}
    ],
    types: [
      'type', '|', 'types', [0, 2],
      'function', '->', 'types', {function: {returns: 2}},
      'function', '(', 'values', ')', '->', 'types', {function: {args: 2, returns: 5}},
      'type', 0
    ],
    literal: [
      'null', 0,
      'undefined', 0,
      'true', 0,
      'false', 0,
      'string', 0,
      'number', 0,
      'code', 0
    ]
  }, [
    ['spec','id',':','types','named_value','=','literal','...','named_values',',','value','values','type','function',
    '(',')','{','}','[',']','|','->','null','undefined','true','false','string','number','code'],{1:1,2:2},[{},{0:0}],
    {3:3},{2:7,4:4,13:5,14:6,17:8,19:9},[{},{0:1,10:1,16:1,18:1,20:1}],[{21:10},{0:[4,3],10:[4,3],16:[4,3],18:[4,3],
    20:[4,3]}],[{15:12,22:11},{0:[13,1],10:[13,1],16:[13,1],18:[13,1],20:[13,1],21:[13,1]}],[{},{0:13,10:13,16:13,
    18:13,20:13,21:13}],{1:16,2:15,5:14,8:17,9:13},{1:16,2:22,4:21,5:20,8:17,11:19,12:18,13:5,14:6,17:8,19:9},{2:7,
    4:23,13:5,14:6,17:8,19:9},{2:7,4:24,13:5,14:6,17:8,19:9},{1:16,2:22,4:21,5:20,8:17,11:19,12:25,13:5,14:6,17:8,
    19:9},{18:26},[{10:27},{18:[9,1]}],{3:3,6:28},[{},{10:[5,1],16:[5,1],18:[5,1],20:[5,1]}],[{},{10:[5,2],16:[5,2],
    18:[5,2],20:[5,2]}],{20:29},[{10:30},{16:[12,1],20:[12,1]}],[{},{10:11,16:11,20:11}],[{},{10:[11,1],16:[11,1],
    20:[11,1]}],[{3:3,6:28},{10:13,16:13,20:13,21:13}],[{},{0:4,10:4,16:4,18:4,20:4}],[{},{0:[4,1],10:[4,1],16:[4,1],
    18:[4,1],20:[4,1]}],{16:31},[{},{0:[13,3],10:[13,3],16:[13,3],18:[13,3],20:[13,3],21:[13,3]}],{1:16,2:15,5:14,8:17,
    9:32},{7:33,23:34,24:35,25:36,26:37,27:38,28:39,29:40},[{},{0:[13,4],10:[13,4],16:[13,4],18:[13,4],20:[13,4],
    21:[13,4]}],{1:16,2:22,4:21,5:20,8:17,11:19,12:41,13:5,14:6,17:8,19:9},[{22:42},{0:[13,2],10:[13,2],16:[13,2],
    18:[13,2],20:[13,2],21:[13,2]}],[{},{18:9}],{3:43},[{},{3:7}],[{},{3:[7,1]}],[{},{3:[7,2]}],[{},{3:[7,3]}],[{},
    {3:[7,4]}],[{},{3:[7,5]}],[{},{3:[7,6]}],[{},{16:12,20:12}],{2:7,4:44,13:5,14:6,17:8,19:9},{2:7,4:45,13:5,14:6,
    17:8,19:9},[{},{0:[4,2],10:[4,2],16:[4,2],18:[4,2],20:[4,2]}],[{},{10:5,16:5,18:5,20:5}]
  ], tokens);
  
  /** doc: {
        generate: function(code:string) -> [Block, ...],
        stringify: function(code:string, breakLimit=1:number) -> string,
        stringifySpec: function(spec:Value|Type, breakLimit=1:number, depth=0:number, type=false:boolean) -> string,
        parseFile: function(path:string, callback:function([Block, ...]))
      }
      
      Documentation is parsed from comments in `code` beginning with `/**`, which are split into blocks separated by
      one or more empty lines. The first block is parsed using the doc spec grammar below. If the parse succeeds, the
      result is returned in `spec`. Otherwise, `spec` is null, `error` is set to jscc's `ParseError`, and the block is
      parsed as `text` along with subsequent blocks.
      
     `        <spec> ::= <id> ':' <types>
       <named_value> ::= <id> '=' <literal> ':' <types>
                       | <spec>
                       | '...'
      <named_values> ::= <named_value> ',' <named_values>
                       | <named_value>
             <value> ::= <named_value>
                       | <types>
            <values> ::= <value> ',' <values>
                       | <value>
              <type> ::= <id>
                       | 'function'
                       | 'function' '(' <values> ')'
                       | '{' <named_values> '}'
                       | '[' <values> ']'
             <types> ::= <type> '|' <types>
                       | 'function' '->' <types>
                       | 'function' '(' <values> ')' '->' <types>
                       | <type>
           <literal> ::= 'null' | 'undefined' | 'true' | 'false' | <string> | <number> | <code>`
      
      See source for regular expressions corresponding to `<id>`, `<string>`, `<number>`, and `<code>`, and for
      examples.
      
      Text blocks following the spec block support code spans between backticks. If an entire block is surrounded in
      backticks, it is parsed as a preformatted block aligned with the right side of the opening backtick.
      
      `stringify` returns a plain-text version of the doc structure returned by `generate`, and `stringifySpec` does
      the same for the `spec` structure within `Block`. `breakLimit` sets the `depth` at which nested object properties
      stop being separated by line breaks.

      `parseFile` is a convenience method that makes an ajax request for the file at `path`, calls `generate` on the
      response text, and issues `callback` with the result. */
      
  /** Block: {spec:Value|null, error:ParseError|undefined, text:[[string|{code:string}, ...]|{pre:string}, ...]} */
  /** Value: [Value, ...]|string|{name:string|undefined, default:string|undefined, type:Type} */
  /** Type: [Type, ...]|string|{function:{args:Value, returns:Type|undefined}}|{object:Value}|{array:Value} */
  return self = {
    generate: function(code) {
      return (code.match(/\/\*\*\s*[\s\S]+?\s*\*\//g) || []).map(function(comment) {
        var blocks = comment.substring(3, comment.length-2).trim().split(/\n\s*\n/),
            spec = blocks.shift(), error = null;
        try {
          spec = parse(spec);
        } catch (e) {
          blocks.unshift(spec);
          spec = null;
          error = e;
        }
        return {
          spec: spec,
          error: error,
          text: blocks.map(function(block) {
            var chunks = [], code;
            if (code = block.match(/^(\s*)`([^`]+)`\s*$/))
              return {pre: code[2].replace(new RegExp('\n'+code[1]+' ', 'g'), '\n')};
            block = block.trim().replace(/\s*\n\s*|\s\s+/g, ' ');
            while (code = tokens.code.exec(block)) {
              if (code.index) chunks.push(block.substr(0, code.index));
              chunks.push({code: code[0].substring(1, code[0].length-1)});
              block = block.substr(code.index+code[0].length);
            }
            if (block) chunks.push(block);
            return chunks;
          })
        };
      });
    },
    stringify: function(code, breakLimit) {
      return self.generate(code).map(function(block) {
        var spec = self.stringifySpec(block.spec, breakLimit);
        return (spec ? [spec] : []).concat(block.text.map(function(chunks) {
          return chunks.pre ? chunks.pre : chunks.map(function(chunk) {
            return typeof chunk == 'string' ? chunk : '`'+chunk.code+'`';
          }).join('');
        })).join('\n\n');
      }).join('\n\n');
    },
    stringifySpec: function spec(node, breakLimit, depth, type) {
      if (typeof node != 'string' && !(typeof node == 'object' && node)) return;
      if (breakLimit == null) breakLimit = 1;
      depth = depth || 0;
      var indent = new Array(depth).join('  ');
      if (type) {
        if (Array.isArray(node))
          return node.map(function(node) { return spec(node, breakLimit, depth, true); }).join('|');
        if (typeof node == 'string')
          return node;
        node = node[type = Object.keys(node)[0]];
        if (type == 'function')
          return type+(node.args ? '('+spec(node.args, 0, depth+1)+')' : '')+(node.returns ? ' → '+spec(node.returns, breakLimit, depth, true) : '');
        if (type == 'object')
          return depth > breakLimit ? '{'+spec(node, breakLimit, depth)+'}' : '{\n  '+indent+spec(node, breakLimit, depth)+'\n'+indent+'}';
        return '['+spec(node, 0, depth)+']';
      }
      if (Array.isArray(node))
        return node.map(function(node) { return spec(node, breakLimit, depth+1); }).join(depth > breakLimit ? ', ' : ',\n  '+indent);
      if (typeof node == 'string')
        return node;
      return (node.name ? node.name+(node.default ? '='+node.default : '')+': ' : '')+spec(node.type, breakLimit, depth+1, true);
    },
    parseFile: function(path, callback) {
      var xhr = new XMLHttpRequest();
      xhr.open('GET', path);
      xhr.onload = function(e) {
        callback(self.generate(e.target.responseText));
      };
      xhr.send();
    }
  };
}();
