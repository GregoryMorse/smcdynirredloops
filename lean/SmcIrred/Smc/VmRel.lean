module

public import SmcIrred.Spec.SmcVm
public import SmcIrred.Smc.Solve
public import SmcIrred.Smc.VmStep

public section

namespace SmcIrred.Vm

/-! # The image of a Level 2 state in the instruction memory (G28)

`img g s` is the instruction memory that the machine `SmcVm` holds when the Level 2 state is `s`: the data cells carry the
index, the entry marker, the lowlink, the component, the topological chain; the patched instructions are the original or the
patched variant according to `ent`, `pk`, `chk`, `dep`. Two cells of every visited node are *free*: the counter (offset 10)
and the return jump (offset 30) are loop state of the node's run that Level 2 does not model. -/

/-- The return address encoded for a stack cell: the address after the call inside the caller, or after the outer call `oc`. -/
@[expose] def enc (n oc : Nat) : Option Nat → Nat
  | some x => base n x + 16
  | none => oc + 1

/-- The jump from the cell of a chain element to the next one. -/
@[expose] def lnk (n : Nat) : List Nat → Nat → Tgt
  | [], _ => .sat
  | [_], _ => .sat
  | a :: b :: t, x => if x = a then .at (base n b + 31) else lnk n (b :: t) x

@[expose] def headT (n : Nat) : List Nat → Tgt
  | [] => .sat
  | c :: _ => .at (base n c + 31)

/-- The jump slot the next chain element is patched into. -/
@[expose] def tailSlot (n : Nat) (ch : List Nat) : Nat :=
  match ch.getLast? with
  | none => n + 2
  | some u => base n u + 35

/-- The instruction at offset `i` of the block of `x` for the Level 2 state `s`. -/
@[expose] def blk (g : Digraph) (s : SState) (x i : Nat) : Ins :=
  if i = 0 then .data (match s.ent x with | none => -1 | some k => (k : Int))
  else if i = 1 then (if s.ent x = none then .load 0 else .ret)
  else if i = 5 then (if s.pk x then .peek else .pop)
  else if i = 13 ∨ i = 20 then (match s.ent x with | none => .jc .tru 2 | some _ => .jc (.stkNe (s.dep x)) 2)
  else if i = 22 then (if s.ent x ≠ none ∧ s.chk x = true then .jc .tru 7 else .jc .fls 7)
  else if i = 29 then (match s.ent x with | none => .data (-1) | some _ => .data (s.low x))
  else if i = 31 then (if s.set x = g.n then .data (-1) else .data (base g.n (s.set x)))
  else if i = 35 then .jmp (lnk g.n s.chain x)
  else blueprint g x i

@[expose] def img (g : Digraph) (s : SState) : Nat → Ins := fun a =>
  if a = 0 then .data s.idx
  else if a ≤ g.n then .call (base g.n (a - 1))
  else if a = g.n + 1 then .data (tailSlot g.n s.chain)
  else if a = g.n + 2 then .jmp (headT g.n s.chain)
  else if (a - (g.n + 3)) / 36 < g.n then blk g s ((a - (g.n + 3)) / 36) ((a - (g.n + 3)) % 36)
  else blueprint g ((a - (g.n + 3)) / 36) ((a - (g.n + 3)) % 36)

/-- The free cells: counter and return jump of a visited node. -/
@[expose] def FreeC (g : Digraph) (s : SState) (a : Nat) : Prop :=
  ∃ x i, x < g.n ∧ a = base g.n x + i ∧ (i = 10 ∨ i = 30) ∧ s.ent x ≠ none

/-- The machine state realises the Level 2 state `s` (the outer call being the `oc`-th). -/
structure VR (g : Digraph) (s : SState) (oc : Nat) (m : VM) : Prop where
  st : m.st = .run
  sol : m.sol = []
  stk : m.stk = s.stk.map (enc g.n oc)
  mem : ∀ a, m.mem a = img g s a ∨ FreeC g s a
  nodup : s.chain.Nodup

theorem img_blk (g : Digraph) (s : SState) {x i : Nat} (hx : x < g.n) (hi : i < 36) :
    img g s (base g.n x + i) = blk g s x i := by
  have h1 : (base g.n x + i - (g.n + 3)) / 36 = x := by unfold base; omega
  have h2 : (base g.n x + i - (g.n + 3)) % 36 = i := by unfold base; omega
  unfold img
  have e0 : ¬ base g.n x + i = 0 := by unfold base; omega
  have e1 : ¬ base g.n x + i ≤ g.n := by unfold base; omega
  have e2 : ¬ base g.n x + i = g.n + 1 := by unfold base; omega
  have e3 : ¬ base g.n x + i = g.n + 2 := by unfold base; omega
  simp only [e0, e1, e2, e3, if_false, h1, h2, hx, if_true]

theorem img_zero (g : Digraph) (s : SState) : img g s 0 = .data s.idx := by simp [img]

theorem img_call (g : Digraph) (s : SState) {a : Nat} (h1 : 1 ≤ a) (h2 : a ≤ g.n) :
    img g s a = .call (base g.n (a - 1)) := by
  unfold img
  simp only [show a ≠ 0 by omega, h2, if_false, if_true]

theorem img_n1 (g : Digraph) (s : SState) : img g s (g.n + 1) = .data (tailSlot g.n s.chain) := by
  unfold img
  simp only [show g.n + 1 ≠ 0 by omega, show ¬ g.n + 1 ≤ g.n by omega, if_false, if_true]

theorem img_n2 (g : Digraph) (s : SState) : img g s (g.n + 2) = .jmp (headT g.n s.chain) := by
  unfold img
  simp only [show g.n + 2 ≠ 0 by omega, show ¬ g.n + 2 ≤ g.n by omega, show g.n + 2 ≠ g.n + 1 by omega, if_false,
    if_true]

theorem blk_init (g : Digraph) (x i : Nat) : blk g (SState.init g.n) x i = blueprint g x i := by
  unfold blk
  by_cases h0 : i = 0
  · subst h0; simp [SState.init, blueprint]
  by_cases h1 : i = 1
  · subst h1; simp [SState.init, blueprint]
  by_cases h5 : i = 5
  · subst h5; simp [SState.init, blueprint]
  by_cases h13 : i = 13 ∨ i = 20
  · rcases h13 with rfl | rfl <;> simp [SState.init, blueprint]
  by_cases h22 : i = 22
  · subst h22; simp [SState.init, blueprint]
  by_cases h29 : i = 29
  · subst h29; simp [SState.init, blueprint]
  by_cases h31 : i = 31
  · subst h31; simp [SState.init, blueprint]
  by_cases h35 : i = 35
  · subst h35; simp [SState.init, blueprint, lnk]
  simp [h0, h1, h5, h13, h22, h29, h31, h35]

/-- The initial image is the image of the initial Level 2 state. -/
theorem image_eq_img (g : Digraph) : image g = img g (SState.init g.n) := by
  funext a
  unfold image
  by_cases h0 : a = 0
  · subst h0; simp [img_zero, SState.init]
  by_cases h1 : a ≤ g.n
  · rw [img_call g _ (by omega) h1]; simp [h0, h1]
  by_cases h2 : a = g.n + 1
  · subst h2; rw [img_n1]; simp [tailSlot, SState.init]
  by_cases h3 : a = g.n + 2
  · subst h3; rw [img_n2]; simp [headT, SState.init]
  simp only [h0, h1, h2, h3, if_false]
  unfold img
  simp only [h0, h1, h2, h3, if_false]
  by_cases hx : (a - (g.n + 3)) / 36 < g.n
  · rw [if_pos hx, blk_init]
  · rw [if_neg hx]

theorem FreeC.mono {g : Digraph} {s s' : SState} (h : ∀ x, s.ent x ≠ none → s'.ent x ≠ none) {a : Nat}
    (ha : FreeC g s a) : FreeC g s' a := by
  obtain ⟨x, i, hx, e, hi, hne⟩ := ha
  exact ⟨x, i, hx, e, hi, h x hne⟩

theorem VR.fetch {g : Digraph} {s : SState} {oc : Nat} {m : VM} (h : VR g s oc m) {x i : Nat} (hx : x < g.n)
    (hi : i < 36) (hf : (i ≠ 10 ∧ i ≠ 30) ∨ s.ent x = none) : m.mem (base g.n x + i) = blk g s x i := by
  rcases h.mem (base g.n x + i) with h1 | ⟨x', i', hx', e, hi', hne⟩
  · rw [h1, img_blk g s hx hi]
  · exfalso
    have hxi : x' = x ∧ i' = i := by unfold base at e; omega
    obtain ⟨rfl, rfl⟩ := hxi
    rcases hf with ⟨a1, a2⟩ | hn
    · omega
    · exact hne hn

theorem blk_other {g : Digraph} (s : SState) {x i : Nat} (hs : i ∉ [0, 1, 5, 13, 20, 22, 29, 31, 35]) :
    blk g s x i = blueprint g x i := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
  obtain ⟨h0, h1, h5, h13, h20, h22, h29, h31, h35⟩ := hs
  unfold blk
  simp [h0, h1, h5, h13, h20, h22, h29, h31, h35]

theorem VR.fetch_bp {g : Digraph} {s : SState} {oc : Nat} {m : VM} (h : VR g s oc m) {x i : Nat} (hx : x < g.n)
    (hi : i < 36) (hf : (i ≠ 10 ∧ i ≠ 30) ∨ s.ent x = none) (hs : i ∉ [0, 1, 5, 13, 20, 22, 29, 31, 35]) :
    m.mem (base g.n x + i) = blueprint g x i := by
  rw [h.fetch hx hi hf, blk_other s hs]

theorem VR.mem_zero {g : Digraph} {s : SState} {oc : Nat} {m : VM} (h : VR g s oc m) : m.mem 0 = .data s.idx := by
  rcases h.mem 0 with h1 | ⟨x, i, hx, e, hi, hne⟩
  · rw [h1, img_zero]
  · exfalso; unfold base at e; omega

theorem blk_congr_fields {g : Digraph} {s s' : SState} {x : Nat} (i : Nat) (he : s.ent x = s'.ent x)
    (hp : s.pk x = s'.pk x) (hd : s.dep x = s'.dep x) (hc : s.chk x = s'.chk x) (hl : s.low x = s'.low x)
    (hset : s.set x = s'.set x) (hch : i = 35 → lnk g.n s.chain x = lnk g.n s'.chain x) :
    blk g s x i = blk g s' x i := by
  unfold blk
  rw [he, hp, hd, hc, hl, hset]
  by_cases h35 : i = 35
  · subst h35; simp [hch rfl]
  · simp [h35]

theorem img_congr {g : Digraph} {s s' : SState} (a : Nat) (h0 : a = 0 → s.idx = s'.idx)
    (hc1 : a = g.n + 1 → tailSlot g.n s.chain = tailSlot g.n s'.chain)
    (hc2 : a = g.n + 2 → headT g.n s.chain = headT g.n s'.chain)
    (hb : ∀ x i, x < g.n → i < 36 → a = base g.n x + i → blk g s x i = blk g s' x i) : img g s a = img g s' a := by
  unfold img
  by_cases e0 : a = 0
  · subst e0; simp [h0 rfl]
  by_cases e1 : a ≤ g.n
  · simp [e0, e1]
  by_cases e2 : a = g.n + 1
  · subst e2; simp [hc1 rfl]
  by_cases e3 : a = g.n + 2
  · subst e3; simp [hc2 rfl]
  simp only [e0, e1, e2, e3, if_false]
  by_cases hx : (a - (g.n + 3)) / 36 < g.n
  · rw [if_pos hx, if_pos hx]
    exact hb _ _ hx (Nat.mod_lt _ (by omega)) (by unfold base; omega)
  · rw [if_neg hx, if_neg hx]

theorem VR.mem_n1 {g : Digraph} {s : SState} {oc : Nat} {m : VM} (h : VR g s oc m) :
    m.mem (g.n + 1) = .data (tailSlot g.n s.chain : Nat) := by
  rcases h.mem (g.n + 1) with h1 | ⟨x, i, hx, e, hi, hne⟩
  · rw [h1, img_n1]
  · exfalso; unfold base at e; omega

theorem VR.mem_n2 {g : Digraph} {s : SState} {oc : Nat} {m : VM} (h : VR g s oc m) :
    m.mem (g.n + 2) = .jmp (headT g.n s.chain) := by
  rcases h.mem (g.n + 2) with h1 | ⟨x, i, hx, e, hi, hne⟩
  · rw [h1, img_n2]
  · exfalso; unfold base at e; omega

end SmcIrred.Vm
