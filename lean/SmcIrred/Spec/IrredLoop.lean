module

public section

namespace SmcIrred.Struct

/-! The three C++ functions of `native/IrredLoop.cpp` (Figure 4), as flat programs at statement granularity, and the
CFG of Figure 4 as a semantics with condition oracles.

The observable behaviour is the sequence of calls: `u`, `v`, `w`, `x` and the two condition calls `w_cond` (`wc`) and
`x_cond` (`xc`). The `k`-th condition call (of either kind) returns `o k`: `0` is `EXIT`, `1` is `LOOP`, anything else
leaves the `switch` without a match (the code's `FORWARD`). `uStart` is the parameter `u_start`. -/

inductive Evt
  | u | v | w | x | wc | xc
  deriving DecidableEq

inductive Node
  | u | w | x | v

/-- The CFG of Figure 4 with oracles, as the set of complete call traces from a node: `u → w`; `w` then `w_cond`
(`EXIT`: end, `LOOP`: `u`, otherwise `x`); `x` then `x_cond` (`EXIT`: end, `LOOP`: `w`, otherwise `v`); `v → x`.
`G n i t`: started at node `n` after `i` condition calls, the program halts with the remaining trace `t`. -/
inductive G (o : Nat → Nat) : Node → Nat → List Evt → Prop
  | u {i : Nat} {t : List Evt} : G o .w i t → G o .u i (.u :: t)
  | wExit {i : Nat} : o i = 0 → G o .w i [.w, .wc]
  | wLoop {i : Nat} {t : List Evt} : o i = 1 → G o .u (i + 1) t → G o .w i (.w :: .wc :: t)
  | wFwd {i : Nat} {t : List Evt} : o i ≠ 0 → o i ≠ 1 → G o .x (i + 1) t → G o .w i (.w :: .wc :: t)
  | xExit {i : Nat} : o i = 0 → G o .x i [.x, .xc]
  | xLoop {i : Nat} {t : List Evt} : o i = 1 → G o .w (i + 1) t → G o .x i (.x :: .xc :: t)
  | xFwd {i : Nat} {t : List Evt} : o i ≠ 0 → o i ≠ 1 → G o .v (i + 1) t → G o .x i (.x :: .xc :: t)
  | v {i : Nat} {t : List Evt} : G o .x i t → G o .v i (.v :: t)

/-- The call trace of the program of Figure 4 from its start: `u` first if `u_start`, else `v` first. -/
@[expose] def Cfg (o : Nat → Nat) (uStart : Bool) (t : List Evt) : Prop :=
  if uStart then G o .u 0 t else G o .v 0 t

/-! ### A flat machine -/

inductive Var
  | loop | isEnd | vFirst

inductive Test
  | uStart | loop | isEnd | vFirst
  | not (t : Test)

structure Regs where
  i : Nat
  loop : Bool
  isEnd : Bool
  vFirst : Bool
  tr : List Evt

inductive Ins
  /-- a call statement `f();` -/
  | call : Evt → Ins
  /-- `switch (cond()) { case EXIT: goto a; case LOOP: goto b; }` (no match: fall through) -/
  | sw3 : Evt → Nat → Nat → Ins
  /-- `switch (cond()) { case EXIT: goto a; case LOOP: loop = true; }` -/
  | swSet : Evt → Nat → Ins
  /-- `switch (cond()) { case EXIT: is_end = true; case LOOP: loop = true; }` (the intentional fall-through) -/
  | swFall : Evt → Ins
  | jmp : Nat → Ins
  | jmpIf : Test → Nat → Ins
  | set : Var → Bool → Ins
  | setIf : Test → Var → Bool → Ins
  | halt : Ins

@[expose] def Test.eval (us : Bool) (g : Regs) : Test → Bool
  | .uStart => us
  | .loop => g.loop
  | .isEnd => g.isEnd
  | .vFirst => g.vFirst
  | .not t => !(t.eval us g)

@[expose] def Regs.setVar (g : Regs) : Var → Bool → Regs
  | .loop, b => { g with loop := b }
  | .isEnd, b => { g with isEnd := b }
  | .vFirst, b => { g with vFirst := b }

/-- One instruction; `none` at `halt` (and past the end of the code). -/
@[expose] def step (o : Nat → Nat) (us : Bool) (code : List Ins) : Nat × Regs → Option (Nat × Regs)
  | (pc, g) =>
    match code.getD pc .halt with
    | .call e => some (pc + 1, { g with tr := g.tr ++ [e] })
    | .sw3 e a b =>
      let g' := { g with i := g.i + 1, tr := g.tr ++ [e] }
      some (if o g.i = 0 then a else if o g.i = 1 then b else pc + 1, g')
    | .swSet e a =>
      let g' := { g with i := g.i + 1, tr := g.tr ++ [e] }
      if o g.i = 0 then some (a, g') else some (pc + 1, if o g.i = 1 then { g' with loop := true } else g')
    | .swFall e =>
      let g' := { g with i := g.i + 1, tr := g.tr ++ [e] }
      some (pc + 1, if o g.i = 0 then { g' with isEnd := true, loop := true }
        else if o g.i = 1 then { g' with loop := true } else g')
    | .jmp t => some (t, g)
    | .jmpIf c t => some (if c.eval us g then t else pc + 1, g)
    | .set v b => some (pc + 1, g.setVar v b)
    | .setIf c v b => some (pc + 1, if c.eval us g then g.setVar v b else g)
    | .halt => none

inductive Star (o : Nat → Nat) (us : Bool) (code : List Ins) : Nat × Regs → Nat × Regs → Prop
  | refl (c : Nat × Regs) : Star o us code c c
  | cons {c c' c'' : Nat × Regs} : step o us code c = some c' → Star o us code c' c'' → Star o us code c c''

/-- The program started at its first instruction halts with the call trace `t`. -/
@[expose] def Halts (o : Nat → Nat) (us : Bool) (code : List Ins) (t : List Evt) : Prop :=
  ∃ c, Star o us code (0, ⟨0, false, false, false, []⟩) c ∧ code.getD c.1 .halt = .halt ∧ c.2.tr = t

/-! ### The three functions -/

/-- `irreducible_loops_only_goto`: labels `do_u` = 1, `do_w` = 2, `do_x` = 4, `do_v` = 6, `end` = 8. -/
@[expose] def codeGoto : List Ins :=
  [.jmpIf (.not .uStart) 6,   -- 0: if (!u_start) goto do_v;
   .call .u,                  -- 1: do_u: u();
   .call .w,                  -- 2: do_w: w();
   .sw3 .wc 8 1,              -- 3: switch (w_cond()) { EXIT: goto end; LOOP: goto do_u; }
   .call .x,                  -- 4: do_x: x();
   .sw3 .xc 8 2,              -- 5: switch (x_cond()) { EXIT: goto end; LOOP: goto do_w; }
   .call .v,                  -- 6: do_v: v();
   .jmp 4,                    -- 7: goto do_x;
   .halt]                     -- 8: end: return;

/-- `irreducible_loops`: the nested `do { } while (true)` loops with `break`, and `goto do_v` into the inner loop;
`end` = 14. The end of the middle body (12) and of the outer body (13) jump back (`while (true)`). -/
@[expose] def codeLoops : List Ins :=
  [.jmpIf (.not .uStart) 10,  -- 0: if (!u_start) goto do_v;
   .call .u,                  -- 1: outer: do { u();
   .call .w,                  -- 2: middle: do { w();
   .set .loop false,          -- 3: loop = false;
   .swSet .wc 14,             -- 4: switch (w_cond()) { case EXIT: goto end; case LOOP: loop = true; }
   .jmpIf .loop 13,           -- 5: if (loop) break;     (leaves the middle loop)
   .call .x,                  -- 6: inner: do { x();
   .set .loop false,          -- 7: loop = false;
   .swSet .xc 14,             -- 8: switch (x_cond()) { case EXIT: goto end; case LOOP: loop = true; }
   .jmpIf .loop 12,           -- 9: if (loop) break;     (leaves the inner loop)
   .call .v,                  -- 10: do_v: v();
   .jmp 6,                    -- 11: } while (true);     (inner)
   .jmp 2,                    -- 12: } while (true);     (middle)
   .jmp 1,                    -- 13: } while (true);     (outer)
   .halt]                     -- 14: end: return;

/-- `irreducible_loops_no_goto`: `is_end` and `v_first` variables, `do { } while (!is_end)` loops, and the intentional
fall-through of `case EXIT` into `case LOOP`. -/
@[expose] def codeNoGoto : List Ins :=
  [.set .isEnd false,         -- 0: bool is_end = false,
   .set .vFirst true,         -- 1:      v_first = !u_start;
   .setIf .uStart .vFirst false, -- 2
   .jmpIf .vFirst 5,          -- 3: outer: do { if (!v_first) u();
   .call .u,                  -- 4
   .jmpIf .vFirst 10,         -- 5: middle: do { if (!v_first) {
   .call .w,                  -- 6:   w();
   .set .loop false,          -- 7:   bool loop = false;
   .swFall .wc,               -- 8:   switch (w_cond()) { case EXIT: is_end = true; case LOOP: loop = true; }
   .jmpIf .loop 19,           -- 9:   if (loop) break; }   (leaves the middle loop)
   .jmpIf .vFirst 15,         -- 10: inner: do { if (!v_first) {
   .call .x,                  -- 11:   x();
   .set .loop false,          -- 12:   bool loop = false;
   .swFall .xc,               -- 13:   switch (x_cond()) { ... }
   .jmpIf .loop 18,           -- 14:   if (loop) break; }  (leaves the inner loop)
   .call .v,                  -- 15: v();
   .set .vFirst false,        -- 16: v_first = false;
   .jmp 10,                   -- 17: } while (true);
   .jmpIf (.not .isEnd) 5,    -- 18: } while (!is_end);    (middle)
   .jmpIf (.not .isEnd) 3,    -- 19: } while (!is_end);    (outer)
   .halt]                     -- 20: return;

end SmcIrred.Struct
