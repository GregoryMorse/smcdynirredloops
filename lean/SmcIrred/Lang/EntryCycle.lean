module

public import SmcIrred.Lang.ProtIrred

public section

namespace SmcIrred.Lang

/-! # The cycle of a protected region (G33 b, R19b)

The abstract form of the argument for `prot_not_reducible`, for an entry jump at any address `e0`: the loop head `e0 + 1`
starts a forward path to the closing jump at `c`, which jumps back to the head; the entry jump at `e0` reaches the second
half of the region `L`, which also reaches `c`, without passing the head. Then the back edge is not an edge into a dominator
of its source and the block graph is not reducible. -/

/-- A step out of the last instruction of a block is an edge of the block graph. -/
theorem step_edge (code : List Instr) {e c : Nat} (he : e + 1 < code.length) (hc : c < code.length)
    (hl : ldr code (e + 1) = true) (hs : StepI code e c) :
    (cfgOf code).edge (blockOf code e) (blockOf code c) := by
  have hend := end_of_block code he hl
  refine ⟨blockOf_lt code (by omega), blockOf_lt code hc, ?_⟩
  show blockOf code c ∈ blockSucc code (blockOf code e)
  unfold blockSucc
  rw [hend]
  unfold StepI at hs
  cases hi : code.getD e .halt <;> simp only [hi] at hs ⊢
  · subst hs; simp [he]
  · subst hs; simp
  · rcases hs with h | h <;> subst h <;> simp

theorem entry_cycle_not_reducible (Q : List Instr) {e0 L c : Nat} {h : Cond} (hn : c + 1 < Q.length)
    (hentry : Q.getD e0 .halt = .jmpIf h L) (hroot : ∀ x, x < Q.length → Fwd (StepI Q) 0 x)
    (hLc : L ≤ c) (hl : e0 + 1 < L) (hf1 : Fwd (StepI Q) (e0 + 1) c) (hfL : Fwd (StepI Q) L c)
    (hback : StepI Q c (e0 + 1)) : ¬ (cfgOf Q).Reducible 0 := by
  have hroot' := fwd_root Q hroot
  have hl1 : ldr Q (e0 + 1) = true := ldr_next Q (e := e0) (by omega) (by rw [hentry]; rfl)
  have hlL : ldr Q L = true := ldr_target Q (e := e0) (by omega) (by rw [hentry]; rfl)
  have hlc : ldr Q (c + 1) = true := (back_leaders Q (e := c) (by omega) hback (by omega)).2
  have hlt1 : blockOf Q (e0 + 1) < blockOf Q L := blockOf_strict Q (by omega) (by omega) hlL
  have hlt0 : blockOf Q e0 < blockOf Q (e0 + 1) := blockOf_strict Q (by omega) (by omega) hl1
  have hmc : blockOf Q L ≤ blockOf Q c := blockOf_mono Q hLc (by omega)
  have hf1b : BFwd (cfgOf Q) (blockOf Q (e0 + 1)) (blockOf Q c) := fwd_blocks Q (by omega) hf1
  have hfLb : BFwd (cfgOf Q) (blockOf Q L) (blockOf Q c) := fwd_blocks Q (by omega) hfL
  have hnd := BFwd.nondom hroot' hf1b (by omega)
  have hcB : blockOf Q c < (cfgOf Q).n := blockOf_lt Q (by omega)
  have heb : (cfgOf Q).edge (blockOf Q c) (blockOf Q (e0 + 1)) := step_edge Q (by omega) (by omega) hlc hback
  have hstep0 : StepI Q e0 L := by unfold StepI; rw [hentry]; exact Or.inl rfl
  have he0 : (cfgOf Q).edge (blockOf Q e0) (blockOf Q L) := step_edge Q (by omega) (by omega) hl1 hstep0
  have heB : blockOf Q e0 < (cfgOf Q).n := blockOf_lt Q (by omega)
  have hnotdom : ¬ (cfgOf Q).Dom 0 (blockOf Q (e0 + 1)) (blockOf Q c) := by
    intro hd
    apply hd.2
    have p1 : PathIn (cfgOf Q) (fun z => z ≠ blockOf Q (e0 + 1)) 0 (blockOf Q e0) :=
      (hroot' _ heB).path.mono (fun z hz => by omega)
    have p2 : PathIn (cfgOf Q) (fun z => z ≠ blockOf Q (e0 + 1)) (blockOf Q L) (blockOf Q c) :=
      hfLb.path.mono (fun z hz => by omega)
    have p3 : PathIn (cfgOf Q) (fun z => z ≠ blockOf Q (e0 + 1)) (blockOf Q e0) (blockOf Q c) :=
      .step (by omega) he0 p2
    exact p1.trans p3
  have hPc : PathIn (cfgOf Q) (fun _ => True) 0 (blockOf Q c) := (hroot' _ hcB).path.mono (fun _ _ => trivial)
  intro hred
  exact hred (blockOf Q (e0 + 1)) (hnd.snoc heb hPc hnotdom)

end SmcIrred.Lang
