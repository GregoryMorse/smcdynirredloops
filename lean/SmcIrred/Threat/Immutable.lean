module

public import SmcIrred.Threat.Recover
public import SmcIrred.Dynamic.Fault

public section

namespace SmcIrred.Threat

open Lang Dyn

/-- T2a. An analyzer that reads the predicate cells from the static code bytes fails the goal on every image in which some
cell the program reads differs between the code bytes and the run-time value. -/
theorem imm_fails {A : Analyzer} (hC : ImmCap A) (img : Image) {k : Nat} (hk : k ∈ img.cells)
    (hd : img.blueprint k ≠ rtVal img k) : ¬ Determines A img :=
  fun h => hd (by rw [← hC.static_read img k]; exact h k hk)

/-- T2b (characterization). For the class `Imm` the goal holds exactly when the code bytes of every cell the program reads
already equal its run-time value. -/
theorem imm_determines_iff {A : Analyzer} (hC : ImmCap A) (img : Image) :
    Determines A img ↔ ∀ k ∈ img.cells, img.blueprint k = rtVal img k :=
  ⟨fun h k hk => by rw [← hC.static_read img k]; exact h k hk,
   fun h k hk => by rw [hC.static_read img k]; exact h k hk⟩

/-- The witness design: three variables, intended assignment all false, variables 1 and 2 required with the planted forest
`x ⇒ ¬x`, no extra implications, and the circuit with its ordered schedule. -/
@[expose] def witness (orig prog : Stmt) : Design where
  img := ⟨prog, impFormula 3 [(⟨1, true⟩, ⟨1, false⟩), (⟨2, true⟩, ⟨2, false⟩)]⟩
  orig := orig
  n := 3
  σ := fun _ => false
  req := fun x => x = 1 ∨ x = 2
  forest := [(⟨1, true⟩, ⟨1, false⟩), (⟨2, true⟩, ⟨2, false⟩)]
  extra := []
  extra_wf := by intro e he; simp at he
  circ := wcirc
  acts := execs [0, 1]

theorem witness_planted : Planted 3 (fun _ => false) (fun x => x = 1 ∨ x = 2)
    [(⟨1, true⟩, ⟨1, false⟩), (⟨2, true⟩, ⟨2, false⟩)] where
  wf := by decide
  respect := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [Respecting, Lit.Holds]
  forcing := by
    intro x hx hr
    rcases hr with rfl | rfl
    · exact .step (by simp) (.refl _)
    · exact .step (by simp) (.refl _)

theorem witness_assumptions {orig prog : Stmt} (hc : ∀ k ∈ codeReads (compile prog), k = 1 ∨ k = 2) :
    Assumptions (witness orig prog) where
  planted := witness_planted
  extra_respects := by intro e he; simp [witness] at he
  stamped := by simp [witness]
  cells_planted := by
    intro k hk
    have := hc k hk
    refine ⟨?_, this, rfl⟩
    show k < 3
    omega
  schedule_topo := wcirc_topo
  schedule_ordered := wcirc_ordered_01

theorem reads_fig5bS : codeReads (compile fig5bS) = [1, 2] := by decide
theorem reads_fig5cS : codeReads (compile fig5cS) = [1] := by decide
theorem reads_fig6bS : codeReads (compile fig6bS) = [1] := by decide
theorem reads_fig6cS : codeReads (compile fig6cS) = [1] := by decide

/-- The forcing implications `x ⇒ ¬x` of the cells `cs`. -/
@[expose] def cellForest (cs : List Nat) : List (Lit × Lit) := cs.map fun k => (⟨k, true⟩, ⟨k, false⟩)

theorem lt_sum_succ : ∀ {cs : List Nat} {k : Nat}, k ∈ cs → k < cs.sum + 1
  | a :: cs, k, h => by
    simp only [List.mem_cons] at h
    simp only [List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := lt_sum_succ h
      omega

theorem cellForest_planted (cs : List Nat) : Planted (cs.sum + 1) (fun _ => false) (fun x => x ∈ cs) (cellForest cs) where
  wf := by
    intro e he
    simp only [cellForest, List.mem_map] at he
    obtain ⟨k, hk, rfl⟩ := he
    exact ⟨lt_sum_succ hk, lt_sum_succ hk⟩
  respect := by
    intro e he
    simp only [cellForest, List.mem_map] at he
    obtain ⟨k, hk, rfl⟩ := he
    simp [Respecting, Lit.Holds]
  forcing := by
    intro x _ hx
    exact .step (List.mem_map.2 ⟨x, hx, rfl⟩) (.refl _)

/-- The witness design for any program: the variables are numbered beyond every cell the program reads, and the cells are
the required variables with intended value false and the forest `x ⇒ ¬x`. -/
@[expose] def witnessG (orig prog : Stmt) : Design where
  img := ⟨prog, impFormula ((codeReads (compile prog)).sum + 1) (cellForest (codeReads (compile prog)))⟩
  orig := orig
  n := (codeReads (compile prog)).sum + 1
  σ := fun _ => false
  req := fun x => x ∈ codeReads (compile prog)
  forest := cellForest (codeReads (compile prog))
  extra := []
  extra_wf := by intro e he; simp at he
  circ := wcirc
  acts := execs [0, 1]

theorem witnessG_assumptions (orig prog : Stmt) : Assumptions (witnessG orig prog) where
  planted := cellForest_planted _
  extra_respects := by intro e he; simp [witnessG] at he
  stamped := by simp [witnessG]
  cells_planted := fun k hk => ⟨lt_sum_succ hk, hk, rfl⟩
  schedule_topo := wcirc_topo
  schedule_ordered := wcirc_ordered_01

/-- Every program of the static scheme reads the predicate cell `1`. -/
theorem obf_cell {orig prog : Stmt} (ho : Obfuscates orig prog) : 1 ∈ codeReads (compile prog) := by
  cases ho with
  | b5 hS hT =>
    show 1 ∈ codeReads (compile (prot (.out 1 true) _ _ (.out 2 true)))
    simp [codeReads, compile_prot hS hT, Instr.reads, Cond.reads]
  | c5 hS hT _ => simp [codeReads, compile_protC hS hT, Instr.reads, Cond.reads]
  | b6 hS hT _ =>
    show 1 ∈ codeReads (compile (prot (.neg _) _ _ (.out 1 true)))
    simp [codeReads, compile_prot hS hT, Instr.reads, Cond.reads]
  | c6 hS hT _ => simp [codeReads, compile_protC6 hS hT, Instr.reads, Cond.reads]

/-- The placeholder the generator writes for predicate cell `1` in every obfuscated program of the static scheme is
`true`: it sits in the first compiled instruction of `b5`, `c5`, `c6` (so whatever `S`, `T` compile to afterwards cannot
hide it), and in `b6` it sits last, after `S` and `T`, but `b6`'s side condition rules out any earlier instruction of the
original program testing cell `1` (`codeStatic_append_of_not_mem`). -/
theorem obf_cell_static {orig prog : Stmt} (ho : Obfuscates orig prog) : codeStatic (compile prog) 1 = true := by
  cases ho with
  | b5 hS hT =>
    rename_i S T
    show codeStatic (compile (prot (Cond.out 1 true) S T (Cond.out 2 true))) 1 = true
    rw [compile_prot hS hT]
    exact codeStatic_cons_eq (by simp [Cond.staticVal])
  | c5 hS hT hp =>
    rename_i S T
    show codeStatic (compile (protC (Cond.out 1 true) S T)) 1 = true
    rw [compile_protC hS hT]
    exact codeStatic_cons_eq (by simp [Cond.staticVal])
  | c6 hS hT hp =>
    rename_i cd S T
    show codeStatic (compile (protC6 cd (Cond.out 1 true) S T)) 1 = true
    rw [compile_protC6 hS hT]
    exact codeStatic_cons_eq (by simp [Cond.staticVal])
  | b6 hS hT hfresh =>
    rename_i cd S T
    show codeStatic (compile (prot (Cond.neg cd) S T (Cond.out 1 true))) 1 = true
    have hsh1 : comp [] 1 S = (comp [] 0 S).map (shiftI 1) := comp_shift [] 1 S hS 0
    have hsh2 : comp [] (1 + S.size) T = (comp [] 0 T).map (shiftI (1 + S.size)) := by
      have := comp_shift [] (1 + S.size) T hT 0; rwa [Nat.zero_add] at this
    rw [compile_ite1_seq hS hT, ← hsh1, ← hsh2] at hfresh
    have hpre : 1 ∉ codeReads
        (Instr.jmpIf (Cond.neg cd) (1 + S.size) :: (comp [] 1 S ++ comp [] (1 + S.size) T)) := by
      intro hmem
      apply hfresh
      simp only [codeReads, List.flatMap_cons, List.flatMap_append, List.flatMap_nil, List.mem_append,
        Instr.reads, List.not_mem_nil, or_false] at hmem ⊢
      exact hmem
    have hsplit : (Instr.jmpIf (Cond.neg cd) (1 + S.size) ::
        (comp [] 1 S ++ (comp [] (1 + S.size) T ++ [Instr.jmpIf (Cond.out 1 true) 1, Instr.halt]))) =
      (Instr.jmpIf (Cond.neg cd) (1 + S.size) :: (comp [] 1 S ++ comp [] (1 + S.size) T)) ++
        [Instr.jmpIf (Cond.out 1 true) 1, Instr.halt] := by simp [List.append_assoc]
    rw [compile_prot hS hT, hsplit, codeStatic_append_of_not_mem hpre]
    exact codeStatic_cons_eq (by simp [Cond.staticVal])

/-- T2 (the class `Imm` is unsound on the scheme). For every obfuscated program of the static scheme (arbitrary goto-free
blocks, Figures 5 and 6) there is a design satisfying S1–S3 (in which the generator's placeholder for the predicate cells is
true, the run-time value false) whose image the class `Imm` provably fails to determine, whatever the analyzer does beyond
reading the code bytes. -/
theorem imm_unsound {orig prog : Stmt} (ho : Obfuscates orig prog) {A : Analyzer} (hC : ImmCap A) :
    ∃ d : Design, Assumptions d ∧ d.orig = orig ∧ d.img.prog = prog ∧ ¬ Determines A d.img := by
  have hA := witnessG_assumptions orig prog
  obtain ⟨hn, hr, hs⟩ := hA.cells_planted 1 (obf_cell ho)
  refine ⟨witnessG orig prog, hA, rfl, rfl, imm_fails hC _ (obf_cell ho) ?_⟩
  show (witnessG orig prog).img.blueprint 1 ≠ rtVal (witnessG orig prog).img 1
  rw [rtVal_planted hA hn hr, hs]
  show codeStatic (compile prog) 1 ≠ false
  rw [obf_cell_static ho]
  decide

/-- At the level of behaviour: with placeholder bytes all true the static reading of the obfuscated programs is not the
behaviour of the original program (so a class that trusts the code bytes misreads the control flow). -/
theorem static_reading_wrong :
    (∃ c, traceS (fun _ => true) fig5bS c true ≠ trace fig5a c true) ∧
    (∃ c, traceS (fun _ => true) fig5cS c true ≠ trace fig5a c true) ∧
    (∃ c, traceS (fun _ => true) fig6bS c true ≠ trace fig6a c true) ∧
    (∃ c, traceS (fun _ => true) fig6cS c true ≠ trace fig6a c true) := by
  refine ⟨⟨true, by decide⟩, ⟨true, by decide⟩, ⟨true, by decide⟩, ⟨true, by decide⟩⟩

end SmcIrred.Threat
