//Provides: caml_atomic_load
function caml_atomic_load(f) {
  return f[1];
}

//Provides: caml_continuation_use_noexc
function caml_continuation_use_noexc(cont) {
  return cont;
}

//Provides: caml_atomic_cas
function caml_atomic_cas(r) { 
  // TODO
  return true; 
}