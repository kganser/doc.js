// Copyright 2014, Klaus Ganser <http://kganser.com>
// MIT Licensed, with this copyright and permission notice
// <http://opensource.org/licenses/MIT>

/** doc: function(path:string, element:DOMElement)
    
    Populates `element` with documentation generated by doc.js and rendered with jsml using code retrieved with an ajax
    request to the specified `path`. */

doc = function(doc) {
  var format = function(node, type) {
    if (type) {
      if (Array.isArray(node))
        return {span: {className: 'docjs-types', children: node.map(function(node) { return format(node, true); })}};
      type = typeof node == 'string' ? node : Object.keys(node)[0];
      return {span: {className: 'docjs-type docjs-type-'+type, children: {span: node == type ? node : {className: 'docjs-'+type, children: [
        type == 'function' ? [
          node.function.args && {span: {className: 'docjs-args', children: format(node.function.args)}},
          node.function.returns && {span: {className: 'docjs-returns', children: format(node.function.returns, true)}}
        ] : format(node[type])
      ]}}}};
    }
    if (Array.isArray(node))
      return {span: {className: 'docjs-values', children: node.map(function(node) { return format(node); })}};
    return {span: {className: 'docjs-value', children: {span: {className: 'docjs-'+(node.name ? '' : 'un')+'named-value', children: typeof node == 'string' ? node : [
      node.name && {span: {className: 'docjs-name', children: node.name}},
      node.default && {span: {className: 'docjs-default', children: node.default}},
      format(node.type, true)
    ]}}}};
  };
  return function(path, elem) {
    doc.parseFile(path, function(data) {
      elem.classList.add('docjs');
      jsml([
        {div: {className: 'docjs-source', children: [
          'generated from ', {a: {href: path, children: 'source'}},
          ' by ', {a: {href: 'http://docjs.kganser.com', children: 'doc.js'}}
        ]}},
        data.map(function(block) {
          if (!block.spec) console.error(block.error.toString());
          return [
            block.spec && {pre: {className: 'docjs-spec', children: format(block.spec)}},
            block.text.map(function(text) {
              return text.pre ? text : {p: text};
            })
          ];
        })
      ], elem, true);
    });
  }
}(doc);
