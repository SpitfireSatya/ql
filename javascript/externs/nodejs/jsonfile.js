
/**
 * @externs
 * @fileoverview Definitions for module "jsonfile"
*/

var jsonfile = { };

jsonfile.readFile = function(filepath, options, callback) { if(callback) callback(); }

jsonfile.readFileSync = function(filepath, options) { }

jsonfile.writeFile = function(data, filepath, options, callback) { if(callback) callback(); }

jsonfile.writeFileSync = function(data, filepath, options) { }

module.exports = jsonfile.readFile;

module.exports = jsonfile.readFileSync;

module.exports = jsonfile.writeFile;

module.exports = jsonfile.writeFileSync;
