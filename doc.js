// Copyright 2014, Klaus Ganser <http://kganser.com>
// MIT Licensed, with this copyright and permission notice
// <http://opensource.org/licenses/MIT>

var doc = function() {
  var parser = function() {
    var identity = function(o) { return o; };
    var unique = function(symbol, symbols, obj) {
      while (symbols.hasOwnProperty(symbol)) symbol += "'";
      if (obj) obj[symbol] = 1;
      return obj || symbol;
    };
    var merge = function(to, from) {
      var added;
      Object.keys(from).forEach(function(key) {
        if (!to.hasOwnProperty(key))
          added = to[key] = 1;
      });
      return added;
    };
    var stringify = function(item) {
      return item[0]+' → '+item[1].map(function(symbol, i) {
        return i != item[2] ? i ? ' '+symbol : symbol : '•'+symbol;
      }).join('')+(item[2] == item[1].length ? '•' : '');
    };
    return {
      generate: function(grammar, start, tokens) {
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
        
        if (Array.isArray(start)) {
        
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
              state.reductions[+symbol ? start[0][symbol-1] : ''] = [nonterminal, production[0], null, null, production[1] || identity];
            });
            delete state.raw;
          });
        
        } else {
        
          var firsts = {}, oldStart = start, done;
          
          var getFirsts = function(production, start) {
            var symbol, current = {'': 1};
            for (var i = start || 0; (symbol = production[i]) && current.hasOwnProperty(''); i++) {
              delete current[''];
              if (grammar.hasOwnProperty(symbol)) {
                merge(current, firsts[symbol]);
              } else {
                current[symbol] = 1;
              }
            }
            return current;
          };
          
          // validate, prepare grammar
          nonterminals.forEach(function(nonterminal) {
            firsts[nonterminal] = {};
            symbols[nonterminal] = 1;
            grammar[nonterminal].forEach(function(production) {
              for (var symbol, i = 0; i < production[0].length; i++) {
                if (symbol = production[0][i]) {
                  symbols[symbol] = 1;
                } else { // empty strings are reserved as EOF token
                  production[0].splice(i--, 1);
                }
              }
            });
          });
          
          if (!grammar.hasOwnProperty(oldStart)) throw 'Start symbol does not appear in grammar';
          grammar[start = unique(oldStart, symbols)] = [[[oldStart], function(e) { return e; }]];
          
          // compute first sets
          do {
            done = true;
            nonterminals.forEach(function(nonterminal) {
              grammar[nonterminal].forEach(function(production) {
                if (merge(firsts[nonterminal], getFirsts(production[0])))
                  done = false;
              });
            });
          } while (!done);
          
          //firsts.forEach(function(n) { console.log('first', n, Object.keys(firsts[n])); });
          
          // adds any nonkernel productions to complete closure,
          // as well as all shifting transition symbols
          var close = function(state) {
            if (!state.transitions) state.transitions = {};
            state.reductions = {};
            do {
              done = true;
              state.items.forEach(function(item) {
                var lookaheads = {}, next = item[1][item[2]];
                if (next && !state.transitions[next]) state.transitions[next] = 0;
                if (!next || !grammar.hasOwnProperty(next)) return;
                if (Object.keys(item[3]).length && (lookaheads = getFirsts(item[1], item[2]+1)).hasOwnProperty('')) {
                  delete lookaheads[''];
                  merge(lookaheads, item[3]);
                }
                grammar[next].forEach(function(production) {
                  var last;
                  if (state.items.some(function(item) {
                    last = item;
                    return item[1] == production[0] && !item[2];
                  })) {
                    if (merge(last[3], lookaheads))
                      done = false;
                  } else {
                    state.items.push([next, production[0], 0, lookaheads, production[1] || identity]);
                    done = false;
                  }
                });
              });
            } while (!done);
            return state;
          };
          
          // generate LR(0) states
          states.push(close({items: [[start, grammar[start][0][0], 0, {}, grammar[start][0][1] || identity]]}));
          
          do {
            done = true;
            states.forEach(function(state) {
              Object.keys(state.transitions).forEach(function(symbol) {
                // find all productions in state with `symbol` as
                // their next symbol and advance index; these
                // become kernel of another state, which we add
                // to `states` if it doesn't already exist
                var candidate = {items: []};
                state.items.forEach(function(item) {
                  var next = item[1][item[2]];
                  if (next == symbol)
                    candidate.items.push([item[0], item[1], item[2]+1, {}, item[4]]);
                });
                
                //console.log('state candidate\n'+candidate.items.map(stringify).join('\n'));
                
                if (!states.some(function(state) {
                  var compared = 0;
                  return !state.items.some(function(item) {
                    if (!item[2] && item[0] != start) return;
                    compared++;
                    return !candidate.items.some(function(i) {
                      return item[1] == i[1] && item[2] == i[2];
                    });// && !console.log(stringify(item)+' not in new state') || console.log(stringify(item)+' found in new state');
                  }) && compared == candidate.items.length && (candidate = state);
                })) {
                  states.push(close(candidate));
                  done = false;
                }
                state.transitions[symbol] = candidate;
              });
            });
          } while (!done);
          
          // generate lookaheads for LR(0) states
          var lookaheads = [], foo = unique('#', symbols, {});
          states[0].items[0][3] = {'': 1};
          
          states.forEach(function(state) {
            state.items.forEach(function(item) {
              if (!item[2] && item[0] != start) return;
              close({items: [item.slice(0, 3).concat([foo])]}).items.forEach(function(i) {
                var next = i[1][i[2]];
                if (next) {
                  state.transitions[next].items.some(function(j) {
                    return i[1] == j[1] && i[2]+1 == j[2] && (next = j);
                  });
                  Object.keys(i[3]).forEach(function(symbol) {
                    if (!foo.hasOwnProperty(symbol)) {
                      next[3][symbol] = 1;
                    } else if (item != next) {
                      lookaheads.push([item[3], next[3]]);
                    }
                  });
                }
              });
            });
          });
          
          do {
            done = true;
            lookaheads.forEach(function(pair) {
              if (merge(pair[1], pair[0]))
                done = false;
            });
          } while (!done);
          
          states.forEach(close);
          
          /*console.log(states.length+' states:\n\n'+states.map(function(state) {
            return state.items.map(stringify).join('\n');
          }).join('\n\n'));*/
          
          // detect shift-reduce, reduce-reduce conflicts
          states.forEach(function(state) {
            state.items.forEach(function(item) {
              var next = item[1][item[2]];
              if (!next) {
                Object.keys(item[3]).forEach(function(next) {
                  if (state.transitions.hasOwnProperty(next)) throw 'Shift-reduce conflict on input "'+next+'"\n  '+stringify(state.transitions[next].items[0])+' (shift)\n  '+stringify(item)+' (reduce)';
                  if (state.reductions.hasOwnProperty(next)) throw 'Reduce-reduce conflict on input "'+next+'"\n  '+stringify(state.reductions[next])+'\n  '+stringify(item);
                  state.reductions[next] = item;
                });
              } else if (state.reductions.hasOwnProperty(next)) {
                throw 'Shift-reduce conflict on input "'+next+'"\n  '+stringify(item)+' (shift)\n  '+stringify(state.reductions[next])+' (reduce)';
              }
            });
          });
        }
        
        return function(string) {
        
          if (string == null) {
            var s = Object.keys(symbols);
            return [s].concat(states.map(function(state) {
              var transitions = {},
                  reductions = {};
              Object.keys(state.transitions).forEach(function(symbol) {
                transitions[s.indexOf(symbol)+1] = states.indexOf(state.transitions[symbol]);
              });
              Object.keys(state.reductions).forEach(function(symbol) {
                var item = state.reductions[symbol],
                    nonterminal = s.indexOf(item[0])+1,
                    production;
                if (nonterminal) grammar[s[nonterminal-1]].some(function(rule, i) {
                  return rule[0] == item[1] && (production = i);
                });
                reductions[s.indexOf(symbol)+1] = production ? [nonterminal, production] : nonterminal;
              });
              return Object.keys(reductions).length ? [transitions, reductions] : transitions;
            }));
          }
        
          var token, match, ignore = tokens[''], substring = string, values = [], stack = [], state = states[0], i = 0;
          
          while (state) {
            //console.log('now at:\n'+state.items.map(stringify).join('\n'));
            
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
                //console.log('checking symbol '+symbol);
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
              //console.log('reducing '+stringify(reduction));
              for (var j = reduction[1].length; j; j--) {
                state = stack.pop();
                args.unshift(values.pop());
              }
              stack.push(state);
              state = state.transitions[reduction[0]];
              values.push(reduction[4](args));
            } else {
              //console.log('shifting '+token.symbol);
              stack.push(state);
              values.push(token.value);
              state = state.transitions[token.symbol];
              substring = substring.substr(token.value.length);
              i += token.value.length;
            }
          }
          
          return values.pop().pop();
        };
      }
    };
  }();

  var tokens = {
    id: /[a-zA-Z_$][a-zA-Z0-9_$]*/,
    number: /[0-9]+/,
    string: /'[^']*'|"[^"]*"/,
    code: /`[^`]+`/,
    '': /\s+/
  };
  var self, parse = parser.generate({
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
  }, 'spec', tokens);
  
  /** doc: {
        generate: function(code:string) -> [Block, ...],
        stringify: function(code:string, breakLimit=1:number) -> string,
        stringifySpec: function(spec:Value|Type, breakLimit=1:number, depth=0:number, type=false:boolean) -> string
      }
      
      Documentation is parsed from comments in `code` beginning with `/**`, which are split into blocks separated by
      one or more empty lines. The first block is parsed using the doc spec grammar below. If the parse succeeds, the
      result is returned in `spec`. Otherwise, `spec` is null, `error` is set to the `parser` module's `ParseError`,
      and the block is parsed as `text` along with subsequent blocks.
      
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
      stop being separated by line breaks. */
      
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
