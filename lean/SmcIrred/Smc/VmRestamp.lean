module

public import SmcIrred.Smc.VmFinal

public section

namespace SmcIrred

open Vm

theorem declared_iff (g : Digraph) (a : Nat) :
    declared g a = true ↔ a = 0 ∨ a = g.n + 1 ∨ a = g.n + 2 ∨
      (g.n + 3 ≤ a ∧ (a - (g.n + 3)) / 36 < g.n ∧ (a - (g.n + 3)) % 36 ∈ patchOffsets) := by
  simp [declared, Bool.or_eq_true, Bool.and_eq_true, or_assoc, and_assoc]

/-- Every cell a run can change is a declared patch cell: outside them the memory is the stamped image. -/
theorem restamp_cover {g : Digraph} {s : SState} {mem : Nat → Ins}
    (hmem : ∀ a, mem a = img g s a ∨ FreeC g s a) : restampMem g mem = image g := by
  funext a
  unfold restampMem
  by_cases hd : declared g a = true
  · simp only [hd, if_true]
  · simp only [hd, if_false]
    have hnd := mt (declared_iff g a).2 hd
    simp only [not_or, not_and] at hnd
    obtain ⟨h0, h1, h2, h3⟩ := hnd
    rcases hmem a with e | ⟨x, i, hx, e, hi, hne⟩
    · rw [e]
      unfold img image
      simp only [h0, h1, h2, if_false]
      by_cases hle : a ≤ g.n
      · simp [hle]
      · simp only [hle, if_false]
        by_cases hq : (a - (g.n + 3)) / 36 < g.n
        · simp only [hq, if_true]
          have hr : (a - (g.n + 3)) % 36 ∉ patchOffsets := h3 (by omega) hq
          have hr' : (a - (g.n + 3)) % 36 ∉ [0, 1, 5, 13, 20, 22, 29, 31, 35] := by
            intro hm
            apply hr
            simp only [patchOffsets, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
            omega
          exact blk_other s hr'
        · simp [hq]
    · exfalso
      apply hd
      rw [declared_iff]
      right; right; right
      have e1 : (a - (g.n + 3)) / 36 = x := by rw [e, base_eq]; omega
      have e2 : (a - (g.n + 3)) % 36 = i := by rw [e, base_eq]; omega
      refine ⟨by rw [e, base_eq]; omega, by rw [e1]; exact hx, ?_⟩
      rw [e2]
      simp only [patchOffsets, List.mem_cons, List.not_mem_nil, or_false]
      omega


theorem vmResult_eq_answer (g : Digraph) (fuel : Nat) : vmResult g fuel = vmAnswer (run g fuel (VM.init g)) := rfl

/-- G25 / C39 at the level of the instruction memory: after a run the restamped machine is the stamped machine again, so
`k` successive queries give `k` copies of the answer of `smcSolve`. -/
theorem vm_rounds_replicate (f : TwoSat) (hw : f.Wf) :
    ∃ fuel, ∀ k, vmRounds f.graph fuel k (VM.init f.graph) = List.replicate k (some (smcSolve f)) := by
  obtain ⟨fuel, h1, s0, hm⟩ := vm_correct f hw
  have hans : vmAnswer (run f.graph fuel (VM.init f.graph)) = some (smcSolve f) := by
    rw [← vmResult_eq_answer]; exact h1
  have hre : vmRestamp f.graph (run f.graph fuel (VM.init f.graph)) = VM.init f.graph := by
    have hc := restamp_cover hm
    show VM.mk (restampMem f.graph (run f.graph fuel (VM.init f.graph)).mem) 0 0 [] [] .run = VM.mk (image f.graph) 0 0 [] [] .run
    rw [hc]
  refine ⟨fuel, ?_⟩
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [vmRounds, hans, hre, ih, List.replicate_succ]

end SmcIrred
