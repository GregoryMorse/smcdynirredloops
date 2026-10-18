module

public import SmcIrred.Struct.IrredGoto
public import SmcIrred.Struct.IrredLoops
public import SmcIrred.Struct.IrredNoGoto
public import SmcIrred.Graph.Fig4

public section

namespace SmcIrred.Struct

/-- The vertex of `fig4` of a node (`u` = 1, `v` = 2, `w` = 3, `x` = 4). -/
@[expose] def Node.vertex : Node → Nat
  | .u => 1 | .v => 2 | .w => 3 | .x => 4

/-- The moves of the semantics `G` are the edges of the CFG of Figure 4 (and its exits are the edges into the exit
vertex `5`). -/
theorem G_moves_are_fig4_edges :
    fig4.edge Node.u.vertex Node.w.vertex ∧ fig4.edge Node.w.vertex Node.u.vertex ∧
    fig4.edge Node.w.vertex Node.x.vertex ∧ fig4.edge Node.w.vertex 5 ∧
    fig4.edge Node.x.vertex Node.v.vertex ∧ fig4.edge Node.x.vertex Node.w.vertex ∧ fig4.edge Node.x.vertex 5 ∧
    fig4.edge Node.v.vertex Node.x.vertex := by decide

/-- C65: the three C++ functions of `native/IrredLoop.cpp` (transcribed statement by statement, with the intentional
fall-through of `irreducible_loops_no_goto`) produce the same call trace as each other and as the CFG of Figure 4, for every
oracle of the two conditions and both values of `u_start`: one halts with a trace exactly when the others do. -/
theorem three_versions_agree (o : Nat → Nat) (us : Bool) (t : List Evt) :
    (Halts o us codeNoGoto t ↔ Halts o us codeLoops t) ∧ (Halts o us codeLoops t ↔ Halts o us codeGoto t) ∧
    (Halts o us codeGoto t ↔ Cfg o us t) := by
  refine ⟨?_, ?_, goto_iff o us t⟩
  · rw [ng_iff, loops_iff]
  · rw [loops_iff, goto_iff]

end SmcIrred.Struct
