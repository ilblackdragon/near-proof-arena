/* E2E M3: the link-time wrapper of the Lean checker's compiled Wasm entry (see Tape.lean).
 *
 * `wasmbase-tape` is linked with
 *   -Wl,--wrap=lp_NearSpecV3_NearSpecV3_Wasm_runCallWithLimitsFast
 * so every call from another object file reaches `__wrap_…` below.  It calls the real function
 * (`__real_…`), returns its result unchanged, and hands copies of the arguments and the result to the
 * Lean hook `wb_tape_hook` (Tape.lean `hookE`), which records the call's host tape.
 *
 * ABI of the original (Wasm/Arcs.c, `runCallWithLimitsFast___boxed`): cfg, ctx, fuel, real owned;
 * code, method borrowed; blockLevel, full unboxed bytes.  The hook is a Lean `@[export]`, so all of
 * its object arguments are owned: the shim takes one extra reference to each before the real call.
 */
#include <lean/lean.h>

#define RCWL lp_NearSpecV3_NearSpecV3_Wasm_runCallWithLimitsFast

lean_object *__real_lp_NearSpecV3_NearSpecV3_Wasm_runCallWithLimitsFast(
    lean_object *cfg, lean_object *code, lean_object *method, lean_object *ctx, lean_object *fuel,
    uint8_t blockLevel, uint8_t full, lean_object *real);

lean_object *wb_tape_hook(lean_object *cfg, lean_object *code, lean_object *method,
                          lean_object *ctx, lean_object *fuel, uint8_t blockLevel,
                          lean_object *real, lean_object *r, lean_object *world);

lean_object *__wrap_lp_NearSpecV3_NearSpecV3_Wasm_runCallWithLimitsFast(
    lean_object *cfg, lean_object *code, lean_object *method, lean_object *ctx, lean_object *fuel,
    uint8_t blockLevel, uint8_t full, lean_object *real) {
  /* the hook's references (the real call consumes cfg, ctx, fuel, real; borrows code, method) */
  lean_inc(cfg);
  lean_inc(code);
  lean_inc(method);
  lean_inc(ctx);
  lean_inc(fuel);
  lean_inc(real);
  lean_object *r = __real_lp_NearSpecV3_NearSpecV3_Wasm_runCallWithLimitsFast(
      cfg, code, method, ctx, fuel, blockLevel, full, real);
  lean_inc(r);
  lean_object *io = wb_tape_hook(cfg, code, method, ctx, fuel, blockLevel, real, r, lean_io_mk_world());
  lean_dec(io);
  return r;
}
