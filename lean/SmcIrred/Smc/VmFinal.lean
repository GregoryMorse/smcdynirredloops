module

public import SmcIrred.Smc.VmRun
public import SmcIrred.Smc.Solve

public section

namespace SmcIrred

open Vm

theorem srel_chain_facts {g : Digraph} {t : TState} {s : SState} {p : Option Nat} (h : SRel g t s p) :
    (∀ u ∈ s.chain, u < g.n) ∧ (∀ u ∈ s.chain, s.set u ≠ g.n) := by
  have hdone : ∀ u ∈ s.chain, s.ent u = some g.n := by
    intro u hu
    rw [h.chain] at hu
    obtain ⟨C, hC, huC⟩ := List.mem_flatten.1 hu
    exact h.done_ent u ⟨C, hC, huC⟩
  have hlt : ∀ u ∈ s.chain, u < g.n := fun u hu => h.lt (by rw [hdone u hu]; simp)
  refine ⟨hlt, ?_⟩
  intro u hu
  have hu' := hu
  rw [h.chain] at hu'
  obtain ⟨C, hC, huC⟩ := List.mem_flatten.1 hu'
  obtain ⟨r, hrC, hr⟩ := h.set C hC
  rw [hr u huC]
  have hrd : s.ent r = some g.n := h.done_ent r ⟨C, hC, hrC⟩
  have := h.lt (u := r) (by rw [hrd]; simp)
  omega

theorem graph_succ_lt (f : TwoSat) (hw : f.Wf) : ∀ x w, w ∈ f.graph.succ x → w < f.graph.n := by
  intro x w hm
  simp only [TwoSat.graph, List.mem_map, List.mem_filter] at hm
  obtain ⟨e, ⟨he, _⟩, rfl⟩ := hm
  exact Lit.node_lt (imps_var_lt hw he).2

theorem vmResult_unsat {g : Digraph} {K : Nat} {m' : VM} (h : run g K (VM.init g) = m') (hs : m'.st = .unsat) :
    vmResult g K = some none := by
  simp only [vmResult, h, hs]

theorem vmResult_sat {g : Digraph} {K : Nat} {m' : VM} (h : run g K (VM.init g) = m') (hs : m'.st = .sat) :
    vmResult g K = some (some m'.sol) := by
  simp only [vmResult, h, hs]

/-- The instruction-level machine computes the solution phase of the Level 2 machine on any digraph whose successor
lists stay in range and whose node set is closed under `nneg`. -/
theorem vm_correct_gen (g : Digraph) (hG : ∀ x w, w ∈ g.succ x → w < g.n) (hneg : ∀ x, x < g.n → nneg x < g.n) :
    ∃ fuel, vmResult g fuel = some (sSolFold (sRun g (g.n - 1) (List.range g.n) (SState.init g.n)).set
      (sRun g (g.n - 1) (List.range g.n) (SState.init g.n)).chain []) := by
  have hCS := callSpec_all hG (g.n - 1)
  have hv0 : VR g (SState.init g.n) 0 (VM.init g) :=
    ⟨rfl, rfl, rfl, fun a => Or.inl (congrFun (image_eq_img g) a), List.nodup_nil⟩
  have f0 : (VM.init g).mem (VM.init g).pc = .data 0 := by simp [VM.init, image]
  obtain ⟨m1, R1, st1, mem1, pc1, reg1, stk1, sol1⟩ := eff_data (g := g) (m := VM.init g) rfl f0
  have hv1 : VR g (SState.init g.n) 0 m1 := VR.congr hv0 st1 mem1 stk1 sol1
  have p1 : m1.pc = 0 + 1 := pc1
  obtain ⟨m2, R2, p2, hv2⟩ := vm_outer hCS hG rfl g.n 0 TState.init (SState.init g.n) 0 m1 (by omega) (SRel.init g) hv1 p1
  have hR := sRun_sim g (g.n - 1) rfl (List.range g.n) TState.init (SState.init g.n) (SRel.init g)
    (by intro v hv; simpa using hv)
  rw [← List.range_eq_range'] at hv2
  obtain ⟨hlt, hset⟩ := srel_chain_facts hR
  generalize sRun g (g.n - 1) (List.range g.n) (SState.init g.n) = S at hv2 hlt hset ⊢
  have p2' : m2.pc = g.n + 1 := by omega
  have c1 : m2.mem m2.pc = .data ((tailSlot g.n S.chain : Nat) : Int) := by rw [p2', hv2.mem_n1]
  obtain ⟨m3, R3, st3, mem3, pc3, reg3, stk3, sol3⟩ := eff_data (g := g) (m := m2) hv2.st c1
  have p3 : m3.pc = g.n + 2 := by omega
  have c2 : m3.mem m3.pc = .jmp (headT g.n S.chain) := by rw [p3, mem3, hv2.mem_n2]
  have hsol3 : m3.sol = [] := by rw [sol3, hv2.sol]
  cases hc : S.chain with
  | nil =>
    have c2' : m3.mem m3.pc = .jmp .sat := by rw [c2, hc]; rfl
    obtain ⟨K, hK⟩ : ∃ K, run g K (VM.init g) = { m3 with st := .sat } :=
      (R1.trans (R2.trans (R3.trans (Rn.of_step (step_sat st3 c2'))))
        : Rn g (VM.init g) { m3 with st := .sat })
    refine ⟨K, ?_⟩
    rw [vmResult_sat hK rfl]
    simp [sSolFold, hsol3]
  | cons c cs =>
    have c2' : m3.mem m3.pc = .jmp (.at (base g.n c + 31)) := by rw [c2, hc]; rfl
    obtain ⟨m4, R4, st4, mem4, pc4, reg4, stk4, sol4⟩ := eff_jmp (g := g) (m := m3) st3 c2'
    have hmem : ∀ a, m4.mem a = img g S a ∨ FreeC g S a := fun a => by rw [mem4, mem3]; exact hv2.mem a
    obtain ⟨m5, R5, hu, hs⟩ := vm_walk hneg hv2.nodup hlt hset cs [] c m4 [] (by rw [hc]; rfl) st4 hmem pc4
      (by rw [sol4, hsol3])
    obtain ⟨K, hK⟩ : ∃ K, run g K (VM.init g) = m5 := R1.trans (R2.trans (R3.trans (R4.trans R5)))
    refine ⟨K, ?_⟩
    cases hr : sSolFold S.set (c :: cs) [] with
    | none => rw [vmResult_unsat hK (hu hr)]
    | some r =>
      obtain ⟨hs1, hs2⟩ := hs r hr
      rw [vmResult_sat hK hs1, hs2]

/-- G28: the instruction-level virtual machine of the stamped image computes `smcSolve`. -/
theorem vm_correct (f : TwoSat) (hw : f.Wf) : ∃ fuel, vmResult f.graph fuel = some (smcSolve f) :=
  vm_correct_gen f.graph (graph_succ_lt f hw) (fun x hx => nneg_lt hx)

end SmcIrred
