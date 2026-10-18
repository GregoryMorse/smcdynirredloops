module

public import SmcIrred.Lang.Common
public import SmcIrred.Spec.LangFigs

public section

namespace SmcIrred.Lang

/-! Figure 6 (C14, C74, P19): the one-sided conditional. -/

/-- For both values of `c` the three programs execute `A` only when `c` holds, then `B`; (c) starts with the
variable true and returns it to true (it is read twice or not at all). -/
theorem fig6_traces (c : Bool) :
    trace fig6a c true = some (if c then [0, 1] else [1], true) ∧
    trace fig6b c true = some (if c then [0, 1] else [1], true) ∧
    trace fig6c c true = some (if c then [0, 1] else [1], true) := by
  cases c <;> decide

/-- (a) and (b) do not read the variable. -/
theorem fig6_traces_any (c v : Bool) :
    trace fig6a c v = some (if c then [0, 1] else [1], v) ∧
    trace fig6b c v = some (if c then [0, 1] else [1], v) := by
  cases c <;> cases v <;> decide

/-- CFG of (b): `c` (with the goto), `A`, `B`, exit; the edges `c→B`, `c→A`, `A→B`, `B→A`, `B→exit`. -/
theorem fig6b_cfg : (cfgOf (compile fig6b)).n = 4 ∧
    ∀ k, k < 4 → (cfgOf (compile fig6b)).succ k = [[2, 1], [2], [1, 3], []].getD k [] := by decide

/-- CFG of (c): `c` with the dummy goto, the condition node, `A`, `B`; the edges `0→A`, `0→cond`, `cond→B`,
`cond→A`, `A→cond`. -/
theorem fig6c_cfg : (cfgOf (compile fig6c)).n = 4 ∧
    ∀ k, k < 4 → (cfgOf (compile fig6c)).succ k = [[2, 1], [3, 2], [1], []].getD k [] := by decide

theorem fig6b_isCFG : (cfgOf (compile fig6b)).IsCFG 0 :=
  isCFG_of_reachB _ 0 (by decide) (by decide)

theorem fig6c_isCFG : (cfgOf (compile fig6c)).IsCFG 0 :=
  isCFG_of_reachB _ 0 (by decide) (by decide)

theorem fig6b_irreducible :
    ∃ w, w < 4 ∧ (cfgOf (compile fig6b)).Irreducible (dfsRun (cfgOf (compile fig6b)) 0 2) w := by decide

theorem fig6c_irreducible :
    ∃ w, w < 4 ∧ (cfgOf (compile fig6c)).Irreducible (dfsRun (cfgOf (compile fig6c)) 0 2) w := by decide

/-- (a) is reducible. -/
theorem fig6a_no_irreducible :
    ∀ w, w < 3 → ¬ (cfgOf (compile fig6a)).Irreducible (dfsRun (cfgOf (compile fig6a)) 0 2) w := by decide

/-! ### P19: the drawn graph of (c) -/

/-- The drawn graph of (c) has the edge `A → B`; the CFG of the listing (vertices: `0` entry, `1` condition, `2` `A`,
`3` `B`, the same numbering) has all the other drawn edges and not that one. -/
theorem fig6c_drawn_extra : ∀ a, a < 4 → ∀ b, b < 4 →
    (fig6cDrawn.edge a b ↔ (cfgOf (compile fig6c)).edge a b ∨ (a = 2 ∧ b = 3)) := by decide

theorem fig6c_no_AB_edge : ¬ (cfgOf (compile fig6c)).edge 2 3 := by decide

theorem fig6c_drawn_has_AB_edge : fig6cDrawn.edge 2 3 := by decide

/-- Figures 5(b) and 6(b) as drawn are the CFGs of the listings without their exit vertex. -/
theorem fig5b_drawn : ∀ a, a < 3 → ∀ b, b < 3 →
    (fig5bDrawn.edge a b ↔ (cfgOf (compile fig5b)).edge a b) := by decide

theorem fig6b_drawn : ∀ a, a < 3 → ∀ b, b < 3 →
    (fig6bDrawn.edge a b ↔ (cfgOf (compile fig6b)).edge a b) := by decide

end SmcIrred.Lang
