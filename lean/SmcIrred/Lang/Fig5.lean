module

public import SmcIrred.Spec.LangFigs
public import SmcIrred.Lang.Common

public section

namespace SmcIrred.Lang

/-! Figure 5 (C14, C74): the transformed programs execute the same blocks as the original, and the
CFGs of (b) and (c) contain an irreducible loop. -/

/-- All three programs run `A` then `B` once and halt, from the state "variable true" (the state the
simulated loop of (c) needs). -/
theorem fig5_traces :
    trace fig5a true true = some ([0, 1], true) ∧ trace fig5b true true = some ([0, 1], true) ∧
    trace fig5c true true = some ([0, 1], true) := by decide

/-- (a) and (b) do not read the state; (c) leaves the variable as it found it (two evaluations toggle it
twice), so repeated execution gives the same trace. -/
theorem fig5_traces_any (v : Bool) :
    trace fig5a true v = some ([0, 1], v) ∧ trace fig5b true v = some ([0, 1], v) := by
  cases v <;> decide

/-- Started with the variable false the loop of (c) is skipped (it must start true). -/
theorem fig5c_needs_state : trace fig5c true false = some ([], true) := by decide

/-! ### The graphs -/

/-- The CFG of (b): entry `0`, `A` `1`, `B` `2`, exit `3`; the edges `0→2`, `0→1`, `1→2`, `2→1`, `2→3`. -/
theorem fig5b_cfg : (cfgOf (compile fig5b)).n = 4 ∧
    ∀ k, k < 4 → (cfgOf (compile fig5b)).succ k = [[2, 1], [2], [1, 3], []].getD k [] := by decide

/-- The CFG of (c): entry `0`, condition node `H` `1`, `A` `2`, `B` `3`, exit `4`; the edges `0→B`, `0→H`, `H→exit`,
`H→A`, `A→B`, `B→H`. -/
theorem fig5c_cfg : (cfgOf (compile fig5c)).n = 5 ∧
    ∀ k, k < 5 → (cfgOf (compile fig5c)).succ k = [[3, 1], [4, 2], [3], [1], []].getD k [] := by decide

theorem fig5b_isCFG : (cfgOf (compile fig5b)).IsCFG 0 :=
  isCFG_of_reachB _ 0 (by decide) (by decide)

theorem fig5c_isCFG : (cfgOf (compile fig5c)).IsCFG 0 :=
  isCFG_of_reachB _ 0 (by decide) (by decide)

/-- The CFG of (b) has an irreducible loop (with respect to the depth-first jungle of the code order). The loop
`{A, B}` has two entries, from the first node into `A` and into `B`. -/
theorem fig5b_irreducible :
    ∃ w, w < 4 ∧ (cfgOf (compile fig5b)).Irreducible (dfsRun (cfgOf (compile fig5b)) 0 2) w := by decide

theorem fig5c_irreducible :
    ∃ w, w < 5 ∧ (cfgOf (compile fig5c)).Irreducible (dfsRun (cfgOf (compile fig5c)) 0 2) w := by decide

/-! ### P18: the drawn graph of (c) -/

/-- Invariant of the walks of the drawn graph. -/
@[expose] def drawn5cInv : Nat → List Nat → Prop
  | 0, t => t = [0] ∨ (∃ s, t = 0 :: 1 :: 0 :: s) ∨ ∃ s, t = 1 :: 0 :: s
  | 1, t => t = [0] ∨ ∃ s, t = 0 :: 1 :: 0 :: s
  | 2, t => ∃ s, t = 1 :: 0 :: s
  | _, t => t = []

theorem drawn5c_inv {a : Nat} {t : List Nat} (h : WalkTr fig5cDrawn fig5cLabel 3 a t) : drawn5cInv a t := by
  induction h with
  | exit hx => rfl
  | @step a b t hab _ ih =>
    have ha : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by have := hab.1; change a < 4 at this; omega
    have hb : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by have := hab.2.1; change b < 4 at this; omega
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd hab (by decide)
      | skip
    all_goals ((revert ih; simp [drawn5cInv, fig5cLabel]) <;>
      first
      | (rintro (h | ⟨s, h⟩) <;> subst h <;> simp)
      | (rintro x h; subst h; simp)
      | (intro h; subst h; simp))

/-- P18: in the graph as drawn, no walk from the entry to the exit executes `A` then `B` once. -/
theorem drawn5c_no_AB : ¬ WalkTr fig5cDrawn fig5cLabel 3 0 [0, 1] := by
  intro h
  have := drawn5c_inv h
  simp only [drawn5cInv] at this
  rcases this with h | ⟨s, h⟩ | ⟨s, h⟩ <;> simp at h

/-- The corrected graph (the CFG of the listing, with the injected condition node `H` = vertex `1`) has such a walk. -/
theorem fig5c_cfg_AB : WalkTr (cfgOf (compile fig5c)) (fun k => blockLabels (compile fig5c) k) 4 0 [0, 1] :=
  .step (a := 0) (b := 1) (by decide) (.step (a := 1) (b := 2) (by decide) (.step (a := 2) (b := 3) (by decide)
    (.step (a := 3) (b := 1) (by decide) (.step (a := 1) (b := 4) (by decide) (.exit (by decide))))))

end SmcIrred.Lang
