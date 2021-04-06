
/**
 * @externs
 * @fileoverview Definitions for module "express"
*/

function express() { };

express.listen = function(port, host, cb) { if(cb) cb(); };

express.get = function(path, cb) { if(cb) cb(); };

express.post = function(path, cb) { if(cb) cb(); };

express.put = function(path, cb) { if(cb) cb(); };

express.delete = function(path, cb) { if(cb) cb(); };

express.patch = function(path, cb) { if(cb) cb(); };

Object.defineProperty(Object.prototype, 'express', {
  get: function() { return express(this.valueOf() || this); },
  enumerable: false,
  configurable: true
});

module.exports = express;
