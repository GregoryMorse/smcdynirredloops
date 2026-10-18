module

public import SmcIrred.Circuit.Order

public section

namespace SmcIrred

/-- `k` repetitions of a run with feedback, starting from the accepting set `z` of the previous run. -/
@[expose] def zIter (run : (Nat → Bool) → (Nat → Bool)) (fbIn : (Nat → Bool) → (Nat → Bool)) :
    Nat → (Nat → Bool) → (Nat → Bool)
  | 0, z => z
  | k + 1, z => zIter run fbIn k (run (fbIn z))

theorem callRunsAux_ungated (run : (Nat → Bool) → (Nat → Bool)) (fbIn : (Nat → Bool) → (Nat → Bool)) :
    ∀ k z, (callRunsAux run (fun _ => false) fbIn k z).length = k ∧
      ((callRunsAux run (fun _ => false) fbIn k z).getLast?.map Prod.snd).getD z = zIter run fbIn k z := by
  intro k
  induction k with
  | zero => intro z; simp [callRunsAux, zIter]
  | succ k ih =>
    intro z
    obtain ⟨h1, h2⟩ := ih (run (fbIn z))
    have e : callRunsAux run (fun _ => false) fbIn (k + 1) z =
        (fbIn z, run (fbIn z)) :: callRunsAux run (fun _ => false) fbIn k (run (fbIn z)) := rfl
    rw [e, zIter]
    refine ⟨by simp [h1], ?_⟩
    rw [List.getLast?_cons]
    cases hl : (callRunsAux run (fun _ => false) fbIn k (run (fbIn z))).getLast? with
    | none => rw [hl] at h2; simpa using h2
    | some q => rw [hl] at h2; simpa using h2

/-- Without a gate, a call with repetition `r` runs `r + 1` times and its final accepting set is the `r`-fold iteration of
the subgraph with feedback (the inlined graph iterated `r + 1` times). -/
theorem callRuns_ungated (run : (Nat → Bool) → (Nat → Bool)) (fbIn : (Nat → Bool) → (Nat → Bool)) (reps : Nat)
    (inb0 : Nat → Bool) :
    (callRuns run (fun _ => false) fbIn reps inb0).length = reps + 1 ∧
      finalZ (callRuns run (fun _ => false) fbIn reps inb0) = zIter run fbIn reps (run inb0) := by
  obtain ⟨h1, h2⟩ := callRunsAux_ungated run fbIn reps (run inb0)
  unfold callRuns finalZ
  refine ⟨by simp [h1], ?_⟩
  rw [List.getLast?_cons]
  cases hl : (callRunsAux run (fun _ => false) fbIn reps (run inb0)).getLast? with
  | none => rw [hl] at h2; simpa using h2
  | some q => rw [hl] at h2; simpa using h2

theorem callOf_ungated (lib : Lib) (V : Circ → (Nat → Bool) → Nat → Nat → Bool) (acc : Nat → Bool) (sid : Nat)
    (ins : List Nat) (reps : Nat) (hg : (lib sid).gated = false) :
    (callOf lib V acc sid ins reps).length = reps + 1 := by
  unfold callOf
  simp only [hg, Bool.false_and]
  exact (callRuns_ungated _ _ reps _).1

theorem sum_map_const_eq {α : Type} (f : α → Nat) (k : Nat) :
    ∀ l : List α, (∀ x ∈ l, f x = k) → (l.map f).sum = l.length * k := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h
    rw [List.map_cons, List.sum_cons, h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp [Nat.add_mul, Nat.add_comm]

/-- A subgraph cost that does not depend on the input makes the cost of an activated, ungated call independent of the
data: `reps + 1` runs of the subgraph. -/
theorem callCost_ungated (lib : Lib) (V : Circ → (Nat → Bool) → Nat → Nat → Bool)
    (K : Circ → (Nat → Bool) → Nat × Nat) (c : Circ) (acc : Nat → Bool) (u sid : Nat) (ins outs : List Nat) (reps : Nat)
    (hk : c.kind u = .call sid ins outs reps) (hg : (lib sid).gated = false) (hact : cnt acc (c.pred u) = 1)
    (κ : Nat × Nat) (hK : ∀ inp, K (lib sid).c inp = κ) :
    callCost lib V K c acc u = ((reps + 1) * κ.1, (reps + 1) * κ.2) := by
  unfold callCost
  rw [hk]
  simp only [hact, beq_self_eq_true, ↓reduceIte]
  have hl := callOf_ungated lib V acc sid ins reps hg
  have h1 := sum_map_const_eq (fun p : (Nat → Bool) × (Nat → Bool) => (K (lib sid).c p.1).1) κ.1
    (callOf lib V acc sid ins reps) (fun p _ => by simp [hK])
  have h2 := sum_map_const_eq (fun p : (Nat → Bool) × (Nat → Bool) => (K (lib sid).c p.1).2) κ.2
    (callOf lib V acc sid ins reps) (fun p _ => by simp [hK])
  rw [h1, h2, hl]

/-- A circuit without calls costs its number of vertices and examined edges, whatever the input. -/
theorem costAt_flat (lib : Lib) (V : Circ → (Nat → Bool) → Nat → Nat → Bool) (K : Circ → (Nat → Bool) → Nat × Nat)
    (c : Circ) (inp : Nat → Bool) (h : ∀ u, u < c.n → ∀ sid ins outs reps, c.kind u ≠ .call sid ins outs reps) :
    costAt lib V K c inp = (c.n, ((List.range c.n).map (edgesOf c)).sum) := by
  have hz : ∀ u, u < c.n → callCost lib V K c (valAt lib V c inp c.n) u = (0, 0) := by
    intro u hu
    unfold callCost
    cases hk : c.kind u with
    | call sid ins outs reps => exact absurd hk (h u hu sid ins outs reps)
    | _ => rfl
  have e1 : ((List.range c.n).map fun u => (callCost lib V K c (valAt lib V c inp c.n) u).1).sum = 0 := by
    rw [sum_map_const_eq _ 0 _ (fun x hx => by rw [hz x (List.mem_range.1 hx)])]; simp
  have e2 : ((List.range c.n).map fun u => (callCost lib V K c (valAt lib V c inp c.n) u).2).sum = 0 := by
    rw [sum_map_const_eq _ 0 _ (fun x hx => by rw [hz x (List.mem_range.1 hx)])]; simp
  unfold costAt
  simp only [e1, e2, Nat.add_zero]

/-- With every call activated and ungated and subgraph costs `κ` independent of the input, the cost of the caller is the
same for all inputs: own vertices and edges plus `reps + 1` subgraph costs per call. -/
theorem costAt_uniform (lib : Lib) (V : Circ → (Nat → Bool) → Nat → Nat → Bool) (K : Circ → (Nat → Bool) → Nat × Nat)
    (κ : Circ → Nat × Nat) (hK : ∀ c' inp, K c' inp = κ c') (c : Circ)
    (hc : ∀ inp u, u < c.n → ∀ sid ins outs reps, c.kind u = .call sid ins outs reps →
      (lib sid).gated = false ∧ cnt (valAt lib V c inp c.n) (c.pred u) = 1) (inp inp' : Nat → Bool) :
    costAt lib V K c inp = costAt lib V K c inp' := by
  have key : ∀ i, ∀ u, u < c.n → callCost lib V K c (valAt lib V c i c.n) u =
      match c.kind u with
      | .call sid _ _ reps => ((reps + 1) * (κ (lib sid).c).1, (reps + 1) * (κ (lib sid).c).2)
      | _ => (0, 0) := by
    intro i u hu
    cases hk : c.kind u with
    | call sid ins outs reps =>
      obtain ⟨hg, ha⟩ := hc i u hu sid ins outs reps hk
      exact callCost_ungated lib V K c _ u sid ins outs reps hk hg ha (κ (lib sid).c) (fun inp => hK _ _)
    | _ => unfold callCost; rw [hk]
  unfold costAt
  simp only []
  have m : ∀ i (g : Nat × Nat → Nat), ((List.range c.n).map fun u => g (callCost lib V K c (valAt lib V c i c.n) u)).sum =
      ((List.range c.n).map fun u => g (match c.kind u with
        | .call sid _ _ reps => ((reps + 1) * (κ (lib sid).c).1, (reps + 1) * (κ (lib sid).c).2)
        | _ => (0, 0))).sum := by
    intro i g
    congr 1
    apply List.map_congr_left
    intro u hu
    rw [key i u (List.mem_range.1 hu)]
  have a1 := m inp Prod.fst
  have a2 := m inp Prod.snd
  have b1 := m inp' Prod.fst
  have b2 := m inp' Prod.snd
  rw [a1, a2, b1, b2]

/-! ### The gate makes the cost data dependent (necessity witness for the ungated hypothesis) -/

namespace CostWitness

/-- The caller: input `A` (vertex 0), `t = A xor ..`, `nt`, the activation `any` (always accepting), the call and two ports. -/
@[expose] def caller : Circ where
  n := 7
  kind := fun v => match v with
    | 0 => .flow | 1 => .add | 2 => .addneg | 3 => .any
    | 4 => .call 0 [0] [5, 6] 1
    | _ => .flow
  pred := fun v => match v with
    | 1 => [0] | 2 => [1] | 3 => [1, 2] | 4 => [3] | 5 => [4] | 6 => [4] | _ => []

/-- The subgraph: input, two flow vertices; the last output is the gate bit. -/
@[expose] def sub (gated : Bool) : Sub where
  c := { n := 3, kind := fun _ => .flow, pred := fun v => match v with | 1 => [0] | 2 => [0] | _ => [] }
  ins := [0]
  outs := [1, 2]
  fb := [0]
  gated := gated

@[expose] def lib (gated : Bool) : Lib := fun _ => sub gated

@[expose] def inpOf (a : Bool) : Nat → Bool := fun v => v == 0 && a

/-- The call is activated for both inputs (the activation hypothesis is satisfiable). -/
theorem activated (g : Bool) (a : Bool) : cnt (valAt (lib g) (level (lib g) 0).val caller (inpOf a) caller.n) (caller.pred 4) = 1 := by
  cases a <;> cases g <;> decide

theorem gated_true : Circ.cost (lib true) 1 caller (inpOf true) = (13, 11) := by decide
theorem gated_false : Circ.cost (lib true) 1 caller (inpOf false) = (10, 9) := by decide
theorem ungated_true : Circ.cost (lib false) 1 caller (inpOf true) = (13, 11) := by decide
theorem ungated_false : Circ.cost (lib false) 1 caller (inpOf false) = (13, 11) := by decide

/-- With a gated subgraph the cost depends on the data. -/
theorem gate_data_dependent :
    Circ.cost (lib true) 1 caller (inpOf true) ≠ Circ.cost (lib true) 1 caller (inpOf false) := by
  rw [gated_true, gated_false]; decide

end CostWitness

end SmcIrred
