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
`x ⇒ ¬x`, no extra implications, the blueprint (the placeholder bytes) all true, and the circuit with its ordered schedule. -/
@[expose] def witness (orig prog : Stmt) : Design where
  img := ⟨prog, impFormula 3 [(⟨1, true⟩, ⟨1, false⟩), (⟨2, true⟩, ⟨2, false⟩)], fun _ => true⟩
  orig := orig
  n := 3
  σ := fun _ => false
  req := fun x => x = 1 ∨ x = 2
  forest := [(⟨1, true⟩, ⟨1, false⟩), (⟨2, true⟩, ⟨2, false⟩)]
  extra := []
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
  extra_wf := by intro e he; simp [witness] at he
  stamped := by simp [witness]
  cells_planted := by
    intro k hk
    have := hc k hk
    refine ⟨?_, this, rfl⟩
    show k < 3
    omega
  schedule_topo := wcirc_topo
  schedule_ordered := wcirc_ordered_01

theorem witness_cells_diff {orig prog : Stmt} (hc : ∀ k ∈ codeReads (compile prog), k = 1 ∨ k = 2)
    {k : Nat} (hk : k ∈ codeReads (compile prog)) :
    (witness orig prog).img.blueprint k ≠ rtVal (witness orig prog).img k := by
  have hA := witness_assumptions (orig := orig) hc
  obtain ⟨hn, hr, hs⟩ := hA.cells_planted k hk
  rw [rtVal_planted hA hn hr]
  simp [witness]

theorem reads_fig5bS : codeReads (compile fig5bS) = [1, 2] := by decide
theorem reads_fig5cS : codeReads (compile fig5cS) = [1] := by decide
theorem reads_fig6bS : codeReads (compile fig6bS) = [1] := by decide
theorem reads_fig6cS : codeReads (compile fig6cS) = [1] := by decide

/-- T2 (the class `Imm` is unsound on the scheme). For each obfuscated program of Figures 5 and 6 there is a design
satisfying S1–S3 (in which the placeholder bytes of the cells are true, the run-time values false) whose image the class
`Imm` provably fails to determine, whatever the analyzer does beyond reading the code bytes. -/
theorem imm_unsound {orig prog : Stmt} (ho : Obfuscates orig prog) {A : Analyzer} (hC : ImmCap A) :
    ∃ d : Design, Assumptions d ∧ d.orig = orig ∧ d.img.prog = prog ∧ ¬ Determines A d.img := by
  have key : ∀ (hc : ∀ k ∈ codeReads (compile prog), k = 1 ∨ k = 2) (k : Nat), k ∈ codeReads (compile prog) →
      ∃ d : Design, Assumptions d ∧ d.orig = orig ∧ d.img.prog = prog ∧ ¬ Determines A d.img :=
    fun hc k hk => ⟨witness orig prog, witness_assumptions hc, rfl, rfl,
      imm_fails hC _ hk (witness_cells_diff hc hk)⟩
  cases ho
  · exact key (by rw [reads_fig5bS]; simp) 1 (by rw [reads_fig5bS]; simp)
  · exact key (by rw [reads_fig5cS]; simp) 1 (by rw [reads_fig5cS]; simp)
  · exact key (by rw [reads_fig6bS]; simp) 1 (by rw [reads_fig6bS]; simp)
  · exact key (by rw [reads_fig6cS]; simp) 1 (by rw [reads_fig6cS]; simp)

/-- At the level of behaviour: with placeholder bytes all true the static reading of the obfuscated programs is not the
behaviour of the original program (so a class that trusts the code bytes misreads the control flow). -/
theorem static_reading_wrong :
    (∃ c, traceS (fun _ => true) fig5bS c true ≠ trace fig5a c true) ∧
    (∃ c, traceS (fun _ => true) fig5cS c true ≠ trace fig5a c true) ∧
    (∃ c, traceS (fun _ => true) fig6bS c true ≠ trace fig6a c true) ∧
    (∃ c, traceS (fun _ => true) fig6cS c true ≠ trace fig6a c true) := by
  refine ⟨⟨true, by decide⟩, ⟨true, by decide⟩, ⟨true, by decide⟩, ⟨true, by decide⟩⟩

end SmcIrred.Threat
