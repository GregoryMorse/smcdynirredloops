module

public import SmcIrred.Threat.Immutable

public section

namespace SmcIrred.Threat

open Lang Dyn

/-- The image with the program of Figure 5(b) and a given formula. -/
@[expose] def imgOf (f : TwoSat) : Image := ⟨fig5bS, f, fun _ => true⟩

theorem run_wrong_of_true {f : TwoSat} (h1 : rtVal (imgOf f) 1 = true) (h2 : rtVal (imgOf f) 2 = true) :
    (imgOf f).run true ≠ trace fig5a true true := by
  show traceS (rtVal (imgOf f)) fig5bS true true ≠ _
  rw [traceS_congr (sol' := fun _ => true) fig5bS ?_ true true]
  · decide
  · intro i hi
    have : codeReads (compile fig5bS) = [1, 2] := reads_fig5bS
    rw [this] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact h1
    · exact h2

theorem hw5 : Assumptions (witness fig5a fig5bS) :=
  witness_assumptions (orig := fig5a) (prog := fig5bS) (by rw [reads_fig5bS]; simp)

/-- No forest. -/
@[expose] def dForce : Design := { witness fig5a fig5bS with forest := [], img := imgOf (impFormula 3 []) }

/-- Necessity of the forcing paths of S1 (`planted.forcing`): with no forest every other field of `Assumptions` holds and the
solver gives the free variables the value true, so the image misbehaves. -/
theorem nec_forcing :
    dForce.img.prog = fig5bS ∧ (∀ e ∈ dForce.forest, e.1.var < dForce.n ∧ e.2.var < dForce.n) ∧
      (∀ e ∈ dForce.forest, Respecting dForce.σ e) ∧ (∀ e ∈ dForce.extra, Respecting dForce.σ e) ∧
      (∀ e ∈ dForce.extra, e.1.var < dForce.n ∧ e.2.var < dForce.n) ∧
      dForce.img.formula = impFormula dForce.n (dForce.forest ++ dForce.extra) ∧
      (∀ k ∈ dForce.img.cells, k < dForce.n ∧ dForce.req k ∧ dForce.σ k = false) ∧
      dForce.circ.Topo ∧ FinalOrdered dForce.circ dForce.acts ∧ dForce.img.run true ≠ trace fig5a true true :=
  ⟨rfl, by simp [dForce], by simp [dForce], hw5.extra_respects, hw5.extra_wf, by simp [dForce, imgOf, witness],
    hw5.cells_planted, hw5.schedule_topo, hw5.schedule_ordered,
    run_wrong_of_true (f := impFormula 3 []) (by decide) (by decide)⟩

/-- The image carries a different formula. -/
@[expose] def dStamp : Design := { witness fig5a fig5bS with img := imgOf (impFormula 3 []) }

/-- Necessity of stamping (`stamped`): the planted data are the witness's, but the image carries a different formula. -/
theorem nec_stamped :
    dStamp.img.prog = fig5bS ∧ Planted dStamp.n dStamp.σ dStamp.req dStamp.forest ∧
      (∀ e ∈ dStamp.extra, Respecting dStamp.σ e) ∧ (∀ e ∈ dStamp.extra, e.1.var < dStamp.n ∧ e.2.var < dStamp.n) ∧
      (∀ k ∈ dStamp.img.cells, k < dStamp.n ∧ dStamp.req k ∧ dStamp.σ k = false) ∧
      dStamp.circ.Topo ∧ FinalOrdered dStamp.circ dStamp.acts ∧
      dStamp.img.formula.clauses ≠ (impFormula dStamp.n (dStamp.forest ++ dStamp.extra)).clauses ∧
      dStamp.img.run true ≠ trace fig5a true true :=
  ⟨rfl, hw5.planted, hw5.extra_respects, hw5.extra_wf, hw5.cells_planted, hw5.schedule_topo, hw5.schedule_ordered,
    by simp [dStamp, imgOf, witness, impFormula],
    run_wrong_of_true (f := impFormula 3 []) (by decide) (by decide)⟩

@[expose] def forestT : List (Lit × Lit) := [(⟨1, false⟩, ⟨1, true⟩), (⟨2, false⟩, ⟨2, true⟩)]

theorem planted_true : Planted 3 (fun _ => true) (fun x => x = 1 ∨ x = 2) forestT :=
  ⟨by decide,
   by
    intro e he
    simp only [forestT, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [Respecting, Lit.Holds],
   by
    intro x hx hr
    rcases hr with rfl | rfl
    · exact .step (by simp [forestT]) (.refl _)
    · exact .step (by simp [forestT]) (.refl _)⟩

/-- Intended value true. -/
@[expose] def dFalse : Design :=
  { witness fig5a fig5bS with σ := (fun _ => true), forest := forestT, img := imgOf (impFormula 3 forestT) }

/-- Necessity of the false intended values of the cells (`cells_planted`, third conjunct): with intended value true the
formula is planted for that assignment and the solver returns it, so the opaque conditions are true and the image misbehaves. -/
theorem nec_false_cells :
    dFalse.img.prog = fig5bS ∧ Planted dFalse.n dFalse.σ dFalse.req dFalse.forest ∧
      (∀ e ∈ dFalse.extra, Respecting dFalse.σ e) ∧ (∀ e ∈ dFalse.extra, e.1.var < dFalse.n ∧ e.2.var < dFalse.n) ∧
      dFalse.img.formula = impFormula dFalse.n (dFalse.forest ++ dFalse.extra) ∧
      (∀ k ∈ dFalse.img.cells, k < dFalse.n ∧ dFalse.req k) ∧ dFalse.circ.Topo ∧ FinalOrdered dFalse.circ dFalse.acts ∧
      dFalse.img.run true ≠ trace fig5a true true :=
  ⟨rfl, planted_true, by simp [dFalse, witness], by simp [dFalse, witness], by simp [dFalse, imgOf, witness],
    fun k hk => ((hw5.cells_planted k hk).imp id (·.1)), hw5.schedule_topo, hw5.schedule_ordered,
    run_wrong_of_true (f := impFormula 3 forestT) (by decide) (by decide)⟩

/-- An extra implication that the intended assignment does not respect. -/
@[expose] def extraBad : List (Lit × Lit) := [(⟨1, false⟩, ⟨1, true⟩)]

@[expose] def dExtra : Design :=
  { witness fig5a fig5bS with extra := extraBad, img := imgOf (impFormula 3 ((witness fig5a fig5bS).forest ++ extraBad)) }

/-- Necessity of the extra implications respecting the intended assignment (`extra_respects`): with one that does not, the
stamped formula is unsatisfiable and the solver returns nothing, so T1's premise that the solver produces the cells fails. -/
theorem nec_extra_respects :
    Planted dExtra.n dExtra.σ dExtra.req dExtra.forest ∧ (∀ e ∈ dExtra.extra, e.1.var < dExtra.n ∧ e.2.var < dExtra.n) ∧
      dExtra.img.formula = impFormula dExtra.n (dExtra.forest ++ dExtra.extra) ∧
      ¬ (∀ e ∈ dExtra.extra, Respecting dExtra.σ e) ∧ smcSolve dExtra.img.formula = none := by
  refine ⟨hw5.planted, by decide, rfl, ?_, by decide⟩
  intro h
  have := h (⟨1, false⟩, ⟨1, true⟩) (by simp [dExtra, witness, extraBad])
  simp [Respecting, Lit.Holds, dExtra, witness] at this

/-- Necessity of the schedule respecting dependencies (`schedule_ordered`): the circuit is topologically numbered, but the
schedule that runs the output before its input leaves a final value different from the circuit's. -/
theorem nec_schedule :
    wcirc.Topo ∧ ¬ FinalOrdered wcirc (execs [1, 0] : List (Act Bool)) ∧
      runA wcirc (fun _ => false) (execs [1, 0]) 1 ≠ valOf wcirc (fun _ => false) 1 :=
  ⟨wcirc_topo, wcirc_bad_not_ordered, wcirc_bad_order⟩

theorem split_cases {β : Type} {x y : β} (hxy : x ≠ y) : ∀ {pre0 post0 pre1 post1 : List β},
    pre0 ++ x :: post0 = pre1 ++ y :: post1 → y ∈ post0 ∨ x ∈ post1 := by
  intro pre0
  induction pre0 with
  | nil =>
    intro post0 pre1 post1 h
    cases pre1 with
    | nil => simp at h; exact absurd h.1 hxy
    | cons b pre1 =>
      simp at h
      left; rw [h.2]; simp
  | cons a pre0 ih =>
    intro post0 pre1 post1 h
    cases pre1 with
    | nil =>
      simp at h
      right; rw [← h.2]; simp
    | cons b pre1 =>
      simp at h
      exact ih h.2

/-- A cyclic circuit (each of two vertices reads the other). -/
@[expose] def ccirc : DCirc Bool where
  n := 2
  ps v := if v = 0 then [1] else [0]
  f _ _ := true

/-- Necessity of the topological numbering of the circuit (`schedule_topo`): in a circuit with a dependency cycle no schedule
has its final executions in dependency order, so the correctness theorem for the dynamic scheme would be vacuous. -/
theorem nec_topo : ¬ ccirc.Topo ∧ ∀ acts : List (Act Bool), ¬ FinalOrdered ccirc acts := by
  refine ⟨?_, ?_⟩
  · intro h
    have := h 0 (by decide) 1 (by simp [ccirc])
    omega
  · intro acts h
    obtain ⟨pre0, post0, h0, _, hq0⟩ := h 0 (by decide)
    obtain ⟨pre1, post1, h1, _, hq1⟩ := h 1 (by decide)
    have hne : ((0 : Nat), (none : Option Bool)) ≠ (1, none) := by decide
    rcases split_cases hne (h0.symm.trans h1) with hy | hx
    · exact hq0 1 (by simp [ccirc]) _ hy rfl
    · exact hq1 0 (by simp [ccirc]) _ hx rfl

end SmcIrred.Threat
