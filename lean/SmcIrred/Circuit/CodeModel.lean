module

public import SmcIrred.Spec.Circuit

public section

namespace SmcIrred

/-- Literal transcription of the single pass of `do_run_virtual` (`BITSZ = 1`): the accepting set starts as the start token
(vertex `c.n`); for every vertex in the dependency order the `elif` chain adds or removes it, and a call adds the output
vertices of its subgraph. `V` evaluates the subgraphs. -/
@[expose] def stepCode (lib : Lib) (V : Circ → (Nat → Bool) → Nat → Nat → Bool) (c : Circ) (inp : Nat → Bool) (x : Nat)
    (acc : Nat → Bool) : Nat → Bool :=
  let ps := c.pred x ++ (if inp x then [c.n] else [])
  let a := cnt acc ps
  let l := ps.length
  let add : Nat → Bool := fun u => if u = x then true else acc u
  let rem : Nat → Bool := fun u => if u = x then false else acc u
  match c.kind x with
  | .flow => if l ≠ 0 ∧ a = l then add else acc
  | .any => if l ≠ 0 ∧ a ≠ 0 then add else if l ≠ 0 ∧ acc x = true ∧ a = 0 then rem else acc
  | .add => if a % 2 = 1 then add else if acc x = true ∧ a % 2 = 0 then rem else acc
  | .addneg => if a % 2 = 0 then add else if acc x = true ∧ a % 2 = 1 then rem else acc
  | .call sid ins outs reps =>
    if a = 1 then
      fun u => acc u || ((outs.zip (lib sid).outs).any fun p => p.1 == u && finalZ (callOf lib V acc sid ins reps) p.2)
    else acc
  | .tbl sel tab => if a = l then (if (sel.zip tab).any (fun p => acc p.1 && p.2) then add else acc) else acc

@[expose] def runPass (lib : Lib) (V : Circ → (Nat → Bool) → Nat → Nat → Bool) (c : Circ) (inp : Nat → Bool)
    (ord : List Nat) : Nat → Bool :=
  ord.foldl (fun acc x => stepCode lib V c inp x acc) (fun u => decide (u = c.n))

/-- A dependency order for the pass: a permutation of the vertices in which every vertex comes after everything it reads;
the circuit is well formed: predecessor lists are duplicate free, active inputs are predecessor-free `flow` vertices, the
output vertices of a call are `flow` vertices whose only predecessor is the call. -/
structure PassWF (c : Circ) (inp : Nat → Bool) (ord : List Nat) : Prop where
  perm : ord.Perm (List.range c.n)
  topo : ∀ L x R, ord = L ++ x :: R → ∀ y ∈ c.reads x, y ∈ L
  pred_nodup : ∀ x, (c.pred x).Nodup
  inp_wf : ∀ x, inp x = true → c.kind x = .flow ∧ c.pred x = []
  port : ∀ u sid ins outs reps, c.kind u = .call sid ins outs reps →
    ∀ y ∈ outs, y < c.n ∧ c.kind y = .flow ∧ c.pred y = [u] ∧ inp y = false

end SmcIrred
