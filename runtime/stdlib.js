// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2010 Jérôme Vouillon
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

//Provides: caml_call_gen (const, shallow)
//Weakdef
function caml_call_gen(f, args) {
  if (f.fun)
    return caml_call_gen(f.fun, args);
  //FIXME, can happen with too many arguments
  if (typeof f !== "function") return f;
  var n = f.length | 0;
  if (n === 0) return f.apply(null, args);
  var argsLen = args.length | 0;
  var d = n - argsLen | 0;
  if (d == 0) {
    return f.apply(null, args);
  } else if (d < 0) {
    var k = args[0];
    var kx = args[1];
    var kf = args[2];
    var rest = new Array(argsLen - n + 3);
    rest[0] = k;
    rest[1] = kx;
    rest[2] = kf;
    for(var i = n; i < argsLen; i++) rest[i-n+3] = args[i];
    var a = new Array(n);
    a[0] = function (x){ return caml_call_gen(x, rest); };
    for(var i = 1; i < n; i++) a[i] = args[i];
    return f.apply(null, a);
  } else {
    var k = args[0];
    return k(function (k2, kx2, kf2, x) {
        var a = new Array(argsLen+1);
        a[0] = k2;
        a[1] = kx2;
        a[2] = kf2;
        for(var i = 3; i < argsLen; i++) a[i] = args[i];
        a[argsLen] = x;
        return caml_call_gen(f, a);
    });
  }
}

//Provides: caml_named_values
var caml_named_values = {};

//Provides: caml_register_named_value (const,const)
//Requires: caml_named_values, caml_jsbytes_of_string
function caml_register_named_value(nm, v) {
  caml_named_values[caml_jsbytes_of_string(nm)] = v;
  return 0;
}

//Provides: caml_named_value
//Requires: caml_named_values
function caml_named_value(nm) {
  return caml_named_values[nm]
}

//Provides: caml_global_data
var caml_global_data = [0];

//Provides: caml_register_global (const, shallow, const)
//Requires: caml_global_data
function caml_register_global (n, v, name_opt) {
  if(name_opt && globalThis.toplevelReloc)
    n = globalThis.toplevelReloc(name_opt);
  caml_global_data[n + 1] = v;
  if (name_opt) caml_global_data[name_opt] = v;
}

//Provides: caml_get_global_data mutable
//Requires: caml_global_data
function caml_get_global_data() { return caml_global_data; }

//Provides: caml_is_printable const (const)
function caml_is_printable(c) { return +(c > 31 && c < 127); }

//Provides: caml_maybe_print_stats
function caml_maybe_print_stats(unit) { return 0 }
