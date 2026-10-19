module

public import SmcIrred.Lang.StructRed

public section

namespace SmcIrred.Lang

/-! # Forward paths through structured code and its blocks

Every address of a structured statement is reached from its first address by steps that increase the address (`Fwd`). On
the basic blocks of flat code a forward address path becomes a path of block edges that increase the block number
(`BFwd`); such paths are non-dominated, which gives a cycle of non-dominating edges as soon as one back edge closes
a forward path whose start is not on the dominating route (used for the protected programs). -/

/-- A path of steps that strictly increase the address. -/
inductive Fwd (R : Nat → Nat → Prop) : Nat → Nat → Prop
  | refl (a : Nat) : Fwd R a a
  | step {a c b : Nat} : R a c → a < c → Fwd R c b → Fwd R a b

theorem Fwd.le {R : Nat → Nat → Prop} {a b : Nat} (h : Fwd R a b) : a ≤ b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ hlt _ ih => omega

theorem Fwd.trans {R : Nat → Nat → Prop} {a b c : Nat} (h1 : Fwd R a b) (h2 : Fwd R b c) : Fwd R a c := by
  induction h1 with
  | refl => exact h2
  | step hr hlt _ ih => exact .step hr hlt (ih h2)

theorem Fwd.mono {R R' : Nat → Nat → Prop} (hm : ∀ a c, R a c → R' a c) {a b : Nat} (h : Fwd R a b) : Fwd R' a b := by
  induction h with
  | refl => exact .refl _
  | step hr hlt _ ih => exact .step (hm _ _ hr) hlt ih

theorem Sub.sstep {u s : Stmt} {q p : Nat} (h : Sub u q s p) : ∀ {a c : Nat}, SStep u q a c → SStep s p a c := by
  induction h with
  | refl => exact id
  | seqL _ ih => intro a c h; exact .seqL (ih h)
  | seqR _ ih => intro a c h; exact .seqR (ih h)
  | ite1 _ ih => intro a c h; exact .ite1_body (ih h)
  | iteS _ ih => intro a c h; exact .ite_s (ih h)
  | iteT _ ih => intro a c h; exact .ite_t (ih h)
  | whl _ ih => intro a c h; exact .while_body (ih h)
  | dow _ ih => intro a c h; exact .do_body (ih h)

/-- Every address of a structured statement (and the address after it) is reached by increasing steps from its start. -/
theorem sstep_fwd : ∀ (s : Stmt), Structured s → ∀ p x, p ≤ x → x ≤ p + s.size → Fwd (SStep s p) p x := by
  intro s
  induction s with
  | skip => intro _ p x h1 h2; simp only [Stmt.size] at h2; have : x = p := by omega
            subst this; exact .refl _
  | blk b =>
    intro _ p x h1 h2
    simp only [Stmt.size] at h2
    by_cases h : x = p
    · subst h; exact .refl _
    · have : x = p + 1 := by omega
      subst this; exact .step .blk (by omega) (.refl _)
  | seq s t ihs iht =>
    intro hst p x h1 h2
    simp only [Stmt.size] at h2
    by_cases h : x ≤ p + s.size
    · exact (ihs hst.1 p x h1 h).mono (fun _ _ h => .seqL h)
    · exact ((ihs hst.1 p (p + s.size) (by omega) (by omega)).mono (fun _ _ h => .seqL h)).trans
        ((iht hst.2 (p + s.size) x (by omega) (by omega)).mono (fun _ _ h => .seqR h))
  | ite1 k s ih =>
    intro hs p x h1 h2
    simp only [Stmt.size] at h2
    by_cases h : x = p
    · subst h; exact .refl _
    · exact .step .ite1_in (by omega) ((ih hs (p + 1) x (by omega) (by omega)).mono (fun _ _ h => .ite1_body h))
  | ite k s t ihs iht =>
    intro hst p x h1 h2
    simp only [Stmt.size] at h2
    by_cases h : x = p
    · subst h; exact .refl _
    · by_cases h' : x ≤ p + 1 + s.size
      · exact .step .ite_then (by omega) ((ihs hst.1 (p + 1) x (by omega) h').mono (fun _ _ h => .ite_s h))
      · exact .step .ite_else (by omega) ((iht hst.2 (p + 2 + s.size) x (by omega) (by omega)).mono (fun _ _ h => .ite_t h))
  | «while» k s ih =>
    intro hs p x h1 h2
    simp only [Stmt.size] at h2
    by_cases h : x = p
    · subst h; exact .refl _
    · by_cases h' : x ≤ p + 1 + s.size
      · exact .step .while_in (by omega) ((ih hs (p + 1) x (by omega) h').mono (fun _ _ h => .while_body h))
      · have : x = p + 2 + s.size := by omega
        subst this; exact .step .while_exit (by omega) (.refl _)
  | doWhile s k ih =>
    intro hs p x h1 h2
    simp only [Stmt.size] at h2
    by_cases h : x ≤ p + s.size
    · exact (ih hs p x h1 h).mono (fun _ _ h => .do_body h)
    · have : x = p + s.size + 1 := by omega
      subst this
      exact ((ih hs p (p + s.size) (by omega) (Nat.le_refl _)).mono (fun _ _ h => .do_body h)).trans
        (.step .do_exit (by omega) (.refl _))
  | goto _ => intro h; exact h.elim
  | ifGoto _ _ => intro h; exact h.elim
  | lab _ s _ => intro h; exact h.elim

/-! ### Blocks -/

/-- A path of block edges that increase the block number. -/
inductive BFwd (g : Digraph) : Nat → Nat → Prop
  | refl {a : Nat} : a < g.n → BFwd g a a
  | step {a c b : Nat} : g.edge a c → a < c → BFwd g c b → BFwd g a b

theorem BFwd.le {g : Digraph} {a b : Nat} (h : BFwd g a b) : a ≤ b := by
  induction h with
  | refl _ => exact Nat.le_refl _
  | step _ hlt _ ih => omega

theorem BFwd.path {g : Digraph} {a b : Nat} (h : BFwd g a b) : PathIn g (fun z => a ≤ z ∧ z ≤ b) a b := by
  induction h with
  | refl h => exact .refl h ⟨Nat.le_refl _, Nat.le_refl _⟩
  | @step a c b he hlt hb ih => exact .step ⟨Nat.le_refl _, by have := hb.le; omega⟩ he (ih.mono (fun z hz => ⟨by omega, hz.2⟩))

theorem BFwd.target {g : Digraph} {a b : Nat} (h : BFwd g a b) : b < g.n := h.path.target.1

/-- A forward edge `a → c` is not an edge into a dominator of `a`, when `a` is reached from the root by a forward path. -/
theorem fwd_not_dom {g : Digraph} {a c : Nat} (hr : BFwd g 0 a) (hlt : a < c) : ¬ g.Dom 0 c a := by
  intro hd
  apply hd.2
  have h0 := hr.path
  exact h0.mono (fun z hz => by omega)

/-- A forward path between two vertices reached from the root by forward paths is a path of non-dominating edges. -/
theorem BFwd.nondom {g : Digraph} (hroot : ∀ v, v < g.n → BFwd g 0 v) {a b : Nat} (h : BFwd g a b) (hab : a < b) :
    g.NonDomPath 0 a b := by
  induction h with
  | refl _ => omega
  | @step a c b he hlt hb ih =>
    have hr := hroot a he.1
    have hP : PathIn g (fun _ => True) 0 a := hr.path.mono (fun _ _ => trivial)
    by_cases hcb : c = b
    · subst hcb
      exact .single he hP (fwd_not_dom hr hlt)
    · exact .step he hP (fwd_not_dom hr hlt) (ih (by have := hb.le; omega))

theorem blockOf_lt (code : List Instr) {x : Nat} (hx : x < code.length) : blockOf code x < (leaders code).length := by
  rw [blockOf_eq code hx]
  have h1 := pos_mono (ldr code) (x + 1) code.length (by omega)
  have h2 := @pos_pos code x
  have h3 : (leaders code).length = pos (ldr code) code.length := rfl
  omega

/-- An address followed by a leader is the last address of its block. -/
theorem end_of_block (code : List Instr) {e : Nat} (he : e + 1 < code.length) (hl : ldr code (e + 1) = true) :
    blockEnd code (blockOf code e) = e := by
  obtain ⟨hlt, hbe, hnext⟩ := blockEnd_spec (code := code) (B := blockOf code e) (blockOf_lt code (by omega))
  generalize blockEnd code (blockOf code e) = b at hlt hbe hnext
  have h1 : e ≤ b := by
    by_cases h : e ≤ b
    · exact h
    · exfalso
      have := blockOf_strict code (x := b) (y := b + 1) (by omega) (by omega) (hnext (by omega))
      have h2 := blockOf_mono code (x := b + 1) (y := e) (by omega) (by omega)
      omega
  have h2 : b ≤ e := by
    by_cases h : b ≤ e
    · exact h
    · exfalso
      have := blockOf_strict code (x := e) (y := e + 1) (by omega) (by omega) hl
      have h3 := blockOf_mono code (x := e + 1) (y := b) (by omega) (by omega)
      omega
  omega

/-- A forward step of flat code stays in its block or is a block edge to a later block. -/
theorem step_block (code : List Instr) {e c : Nat} (he : e + 1 < code.length) (hc : c < code.length) (hlt : e < c)
    (hs : StepI code e c) :
    blockOf code c = blockOf code e ∨ ((cfgOf code).edge (blockOf code e) (blockOf code c) ∧ blockOf code e < blockOf code c) := by
  have hn : ∀ i : Instr, code.getD e .halt = i → (i = .halt ∨ i.isTerm = true ∨ ∃ a, i = .blk a) := by
    intro i _; cases i <;> simp [Instr.isTerm]
  by_cases hl : ldr code (e + 1) = true
  · right
    have hend := end_of_block code he hl
    have hlt' : blockOf code e < blockOf code c := by
      have := blockOf_strict code (x := e) (y := e + 1) (by omega) he hl
      have h2 := blockOf_mono code (x := e + 1) (y := c) (by omega) hc
      omega
    refine ⟨⟨blockOf_lt code (by omega), blockOf_lt code hc, ?_⟩, hlt'⟩
    show blockOf code c ∈ blockSucc code (blockOf code e)
    unfold blockSucc
    rw [hend]
    unfold StepI at hs
    cases hi : code.getD e .halt <;> simp only [hi] at hs ⊢
    · subst hs; simp [he]
    · subst hs; simp
    · rcases hs with h | h <;> subst h <;> simp
  · left
    have hnb : ∃ a, code.getD e .halt = .blk a := by
      cases hi : code.getD e .halt with
      | blk a => exact ⟨a, rfl⟩
      | jmp t => exact absurd (ldr_next code (by omega) (by rw [hi]; rfl)) hl
      | jmpIf k t => exact absurd (ldr_next code (by omega) (by rw [hi]; rfl)) hl
      | halt => unfold StepI at hs; rw [hi] at hs; exact hs.elim
    obtain ⟨a, ha⟩ := hnb
    unfold StepI at hs
    rw [ha] at hs
    subst hs
    rw [blockOf_eq code hc, blockOf_eq code (by omega), pos_succ]
    simp [hl]

/-- An increasing address path of flat code is an increasing path of blocks. -/
theorem fwd_blocks (code : List Instr) {a b : Nat} (hb : b < code.length) (h : Fwd (StepI code) a b) :
    BFwd (cfgOf code) (blockOf code a) (blockOf code b) := by
  induction h with
  | refl a => exact .refl (blockOf_lt code hb)
  | @step a c b hs hlt hf ih =>
    have hcb := hf.le
    rcases step_block code (by omega) (by omega) hlt hs with h | ⟨he, hl⟩
    · rw [← h]; exact ih hb
    · exact .step he hl (ih hb)

end SmcIrred.Lang
