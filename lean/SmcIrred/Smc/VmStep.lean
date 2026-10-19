module

public import SmcIrred.Spec.SmcVm

public section

namespace SmcIrred.Vm

/-! # Running the VM: reachability and one lemma per instruction (G28) -/

/-- `m'` is reached from `m` in some number of steps. -/
@[expose] def Rn (g : Digraph) (m m' : VM) : Prop := ∃ k, run g k m = m'

theorem run_add (g : Digraph) : ∀ (k1 k2 : Nat) (m : VM), run g (k1 + k2) m = run g k2 (run g k1 m) := by
  intro k1
  induction k1 with
  | zero => intro k2 m; simp [run]
  | succ k ih =>
    intro k2 m
    rw [Nat.succ_add]
    show run g (k + k2) (step g m) = run g k2 (run g k (step g m))
    exact ih k2 (step g m)

theorem Rn.refl (g : Digraph) (m : VM) : Rn g m m := ⟨0, rfl⟩

theorem Rn.trans {g : Digraph} {a b c : VM} (h1 : Rn g a b) (h2 : Rn g b c) : Rn g a c := by
  obtain ⟨k1, e1⟩ := h1
  obtain ⟨k2, e2⟩ := h2
  exact ⟨k1 + k2, by rw [run_add, e1, e2]⟩

theorem Rn.one (g : Digraph) (m : VM) : Rn g m (step g m) := ⟨1, rfl⟩

theorem Rn.of_step {g : Digraph} {m m' : VM} (h : Vm.step g m = m') : Rn g m m' := by subst h; exact Rn.one g m

section
variable {g : Digraph} {m : VM}

theorem step_data {v : Int} (hst : m.st = .run) (hm : m.mem m.pc = .data v) :
    step g m = { m with reg := v, pc := m.pc + 1 } := by
  simp [step, hst, hm]

theorem step_call {a : Nat} (hst : m.st = .run) (hm : m.mem m.pc = .call a) :
    step g m = { m with stk := (m.pc + 1) :: m.stk, pc := a } := by
  simp [step, hst, hm]

theorem step_callS {x : Nat} (hst : m.st = .run) (hm : m.mem m.pc = .callS x) :
    step g m = { m with stk := (m.pc + 1) :: m.stk, pc := base g.n ((g.succ x).getD (m.reg - 1).toNat 0) } := by
  simp [step, hst, hm]

theorem step_jmp {a : Nat} (hst : m.st = .run) (hm : m.mem m.pc = .jmp (.at a)) :
    step g m = { m with pc := a } := by
  simp [step, hst, hm]

theorem step_sat (hst : m.st = .run) (hm : m.mem m.pc = .jmp .sat) :
    step g m = { m with st := .sat } := by
  simp [step, hst, hm]

theorem step_unsat (hst : m.st = .run) (hm : m.mem m.pc = .jmp .unsat) :
    step g m = { m with st := .unsat } := by
  simp [step, hst, hm]

theorem step_load {a : Nat} {v : Int} (hst : m.st = .run) (hm : m.mem m.pc = .load a) (hd : m.mem a = .data v) :
    step g m = { m with reg := v, pc := m.pc + 1 } := by
  simp [step, hst, hm, dataAt, hd]

theorem step_store {s : Src} {d : Dst} {v : Int} (hst : m.st = .run) (hm : m.mem m.pc = .store s d)
    (hd : m.mem (d.eval m.reg) = .data v) :
    step g m = { m with mem := memUpd m.mem (d.eval m.reg) (.data (s.eval m.reg)), pc := m.pc + 1 } := by
  simp [step, hst, hm, dataAt, hd]

theorem step_pop {a : Nat} {r : List Nat} (hst : m.st = .run) (hm : m.mem m.pc = .pop) (hs : m.stk = a :: r) :
    step g m = { m with reg := a, stk := r, pc := m.pc + 1 } := by
  simp [step, hst, hm, hs]

theorem step_peek {a : Nat} {r : List Nat} (hst : m.st = .run) (hm : m.mem m.pc = .peek) (hs : m.stk = a :: r) :
    step g m = { m with reg := a, pc := m.pc + 1 } := by
  simp [step, hst, hm, hs]

theorem step_ret {a : Nat} {r : List Nat} (hst : m.st = .run) (hm : m.mem m.pc = .ret) (hs : m.stk = a :: r) :
    step g m = { m with stk := r, pc := a } := by
  simp [step, hst, hm, hs]

theorem step_push {a : Nat} (hst : m.st = .run) (hm : m.mem m.pc = .push a) :
    step g m = { m with stk := a :: m.stk, pc := m.pc + 1 } := by
  simp [step, hst, hm]

theorem step_func {x : Nat} (hst : m.st = .run) (hm : m.mem m.pc = .func x) :
    step g m = { m with sol := if nneg x ∈ m.sol then m.sol else x :: m.sol, pc := m.pc + 1 } := by
  simp [step, hst, hm]

theorem step_modinst {mk : Mk} {ad : MAddr} {a : Nat} (hst : m.st = .run) (hm : m.mem m.pc = .modinst mk ad)
    (ha : ad.eval g m.mem m.reg = some a) :
    step g m = { m with mem := memUpd m.mem a (mk.build m), pc := m.pc + 1 } := by
  simp [step, hst, hm, ha]

theorem step_jc_true {c : Cnd} {off : Int} (hst : m.st = .run) (hm : m.mem m.pc = .jc c off)
    (hc : c.eval g m = some true) : step g m = { m with pc := (m.pc + off).toNat } := by
  simp [step, hst, hm, hc]

theorem step_jc_false {c : Cnd} {off : Int} (hst : m.st = .run) (hm : m.mem m.pc = .jc c off)
    (hc : c.eval g m = some false) : step g m = { m with pc := m.pc + 1 } := by
  simp [step, hst, hm, hc]

end

/-! Effects as field equations (so a proof can name the machine after each step and forget the update term). -/

section
variable {g : Digraph} {m : VM}

theorem eff_data {v : Int} (hst : m.st = .run) (hm : m.mem m.pc = .data v) :
    ∃ m1, Rn g m m1 ∧ m1.st = .run ∧ m1.mem = m.mem ∧ m1.pc = m.pc + 1 ∧ m1.reg = v ∧ m1.stk = m.stk ∧
      m1.sol = m.sol :=
  ⟨_, Rn.of_step (step_data hst hm), hst, rfl, rfl, rfl, rfl, rfl⟩

theorem eff_load {a : Nat} {v : Int} (hst : m.st = .run) (hm : m.mem m.pc = .load a) (hd : m.mem a = .data v) :
    ∃ m1, Rn g m m1 ∧ m1.st = .run ∧ m1.mem = m.mem ∧ m1.pc = m.pc + 1 ∧ m1.reg = v ∧ m1.stk = m.stk ∧
      m1.sol = m.sol :=
  ⟨_, Rn.of_step (step_load hst hm hd), hst, rfl, rfl, rfl, rfl, rfl⟩

theorem eff_store {s : Src} {d : Dst} {v : Int} (hst : m.st = .run) (hm : m.mem m.pc = .store s d)
    (hd : m.mem (d.eval m.reg) = .data v) :
    ∃ m1, Rn g m m1 ∧ m1.st = .run ∧ m1.mem = memUpd m.mem (d.eval m.reg) (.data (s.eval m.reg)) ∧
      m1.pc = m.pc + 1 ∧ m1.reg = m.reg ∧ m1.stk = m.stk ∧ m1.sol = m.sol :=
  ⟨_, Rn.of_step (step_store hst hm hd), hst, rfl, rfl, rfl, rfl, rfl⟩

theorem eff_pop {a : Nat} {r : List Nat} (hst : m.st = .run) (hm : m.mem m.pc = .pop) (hs : m.stk = a :: r) :
    ∃ m1, Rn g m m1 ∧ m1.st = .run ∧ m1.mem = m.mem ∧ m1.pc = m.pc + 1 ∧ m1.reg = a ∧ m1.stk = r ∧
      m1.sol = m.sol :=
  ⟨_, Rn.of_step (step_pop hst hm hs), hst, rfl, rfl, rfl, rfl, rfl⟩

theorem eff_peek {a : Nat} {r : List Nat} (hst : m.st = .run) (hm : m.mem m.pc = .peek) (hs : m.stk = a :: r) :
    ∃ m1, Rn g m m1 ∧ m1.st = .run ∧ m1.mem = m.mem ∧ m1.pc = m.pc + 1 ∧ m1.reg = a ∧ m1.stk = m.stk ∧
      m1.sol = m.sol :=
  ⟨_, Rn.of_step (step_peek hst hm hs), hst, rfl, rfl, rfl, rfl, rfl⟩

theorem eff_modinst {mk : Mk} {ad : MAddr} {a : Nat} (hst : m.st = .run) (hm : m.mem m.pc = .modinst mk ad)
    (ha : ad.eval g m.mem m.reg = some a) :
    ∃ m1, Rn g m m1 ∧ m1.st = .run ∧ m1.mem = memUpd m.mem a (mk.build m) ∧ m1.pc = m.pc + 1 ∧
      m1.reg = m.reg ∧ m1.stk = m.stk ∧ m1.sol = m.sol :=
  ⟨_, Rn.of_step (step_modinst hst hm ha), hst, rfl, rfl, rfl, rfl, rfl⟩

theorem eff_jc_true {c : Cnd} {off : Int} (hst : m.st = .run) (hm : m.mem m.pc = .jc c off)
    (hc : c.eval g m = some true) :
    ∃ m1, Rn g m m1 ∧ m1.st = .run ∧ m1.mem = m.mem ∧ m1.pc = (m.pc + off).toNat ∧ m1.reg = m.reg ∧
      m1.stk = m.stk ∧ m1.sol = m.sol :=
  ⟨_, Rn.of_step (step_jc_true hst hm hc), hst, rfl, rfl, rfl, rfl, rfl⟩

theorem eff_jc_false {c : Cnd} {off : Int} (hst : m.st = .run) (hm : m.mem m.pc = .jc c off)
    (hc : c.eval g m = some false) :
    ∃ m1, Rn g m m1 ∧ m1.st = .run ∧ m1.mem = m.mem ∧ m1.pc = m.pc + 1 ∧ m1.reg = m.reg ∧ m1.stk = m.stk ∧
      m1.sol = m.sol :=
  ⟨_, Rn.of_step (step_jc_false hst hm hc), hst, rfl, rfl, rfl, rfl, rfl⟩

theorem eff_ret {a : Nat} {r : List Nat} (hst : m.st = .run) (hm : m.mem m.pc = .ret) (hs : m.stk = a :: r) :
    ∃ m1, Rn g m m1 ∧ m1.st = .run ∧ m1.mem = m.mem ∧ m1.pc = a ∧ m1.reg = m.reg ∧ m1.stk = r ∧
      m1.sol = m.sol :=
  ⟨_, Rn.of_step (step_ret hst hm hs), hst, rfl, rfl, rfl, rfl, rfl⟩

theorem eff_push {a : Nat} (hst : m.st = .run) (hm : m.mem m.pc = .push a) :
    ∃ m1, Rn g m m1 ∧ m1.st = .run ∧ m1.mem = m.mem ∧ m1.pc = m.pc + 1 ∧ m1.reg = m.reg ∧
      m1.stk = a :: m.stk ∧ m1.sol = m.sol :=
  ⟨_, Rn.of_step (step_push hst hm), hst, rfl, rfl, rfl, rfl, rfl⟩

theorem eff_callS {x : Nat} (hst : m.st = .run) (hm : m.mem m.pc = .callS x) :
    ∃ m1, Rn g m m1 ∧ m1.st = .run ∧ m1.mem = m.mem ∧
      m1.pc = base g.n ((g.succ x).getD (m.reg - 1).toNat 0) ∧ m1.reg = m.reg ∧ m1.stk = (m.pc + 1) :: m.stk ∧
      m1.sol = m.sol :=
  ⟨_, Rn.of_step (step_callS hst hm), hst, rfl, rfl, rfl, rfl, rfl⟩

theorem eff_call {a : Nat} (hst : m.st = .run) (hm : m.mem m.pc = .call a) :
    ∃ m1, Rn g m m1 ∧ m1.st = .run ∧ m1.mem = m.mem ∧ m1.pc = a ∧ m1.reg = m.reg ∧
      m1.stk = (m.pc + 1) :: m.stk ∧ m1.sol = m.sol :=
  ⟨_, Rn.of_step (step_call hst hm), hst, rfl, rfl, rfl, rfl, rfl⟩

theorem eff_jmp {a : Nat} (hst : m.st = .run) (hm : m.mem m.pc = .jmp (.at a)) :
    ∃ m1, Rn g m m1 ∧ m1.st = .run ∧ m1.mem = m.mem ∧ m1.pc = a ∧ m1.reg = m.reg ∧ m1.stk = m.stk ∧
      m1.sol = m.sol :=
  ⟨_, Rn.of_step (step_jmp hst hm), hst, rfl, rfl, rfl, rfl, rfl⟩

theorem eff_func {x : Nat} (hst : m.st = .run) (hm : m.mem m.pc = .func x) :
    ∃ m1, Rn g m m1 ∧ m1.st = .run ∧ m1.mem = m.mem ∧ m1.pc = m.pc + 1 ∧ m1.reg = m.reg ∧ m1.stk = m.stk ∧
      m1.sol = (if nneg x ∈ m.sol then m.sol else x :: m.sol) :=
  ⟨_, Rn.of_step (step_func hst hm), hst, rfl, rfl, rfl, rfl, rfl⟩

end

theorem memUpd_same (mem : Nat → Ins) (a : Nat) (i : Ins) : memUpd mem a i a = i := by simp [memUpd]

theorem memUpd_ne (mem : Nat → Ins) {a b : Nat} (i : Ins) (h : b ≠ a) : memUpd mem a i b = mem b := by
  simp [memUpd, h]

end SmcIrred.Vm
