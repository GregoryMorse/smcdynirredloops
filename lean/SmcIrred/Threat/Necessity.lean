module

public import SmcIrred.Threat.Immutable

public section

namespace SmcIrred.Threat

open Lang Dyn

/-- The image with the program of Figure 5(c) and a given formula. -/
@[expose] def imgOf (f : TwoSat) : Image := ⟨fig5cS, f⟩

theorem ob5c : Obfuscates fig5a fig5cS := .c5 trivial trivial fun _ => ⟨trivial, trivial⟩

/-- An image whose run-time values make the program halt with another trace than the original does behaves differently. -/
theorem not_behaves {img : Image} {orig : Stmt} {c : Bool} {r r' : List Nat × Bool}
    (h1 : exec 100 (compile img.prog) (fun _ => true) c 0 true [] = some r')
    (h2 : exec 100 (compile orig) (fun _ => false) c 0 true [] = some r) (hne : r ≠ r')
    (hs : ∀ i ∈ codeReads (compile img.prog), rtVal img i = (fun _ => true) i) : ¬ img.Behaves orig := by
  intro hB
  obtain ⟨f, hf⟩ := (hB c r).2 ⟨100, h2⟩
  rw [exec_congr hs c f 0 true []] at hf
  exact hne (exec_det f 100 0 true [] hf h1)

theorem exec_fig5cS_true : exec 100 (compile fig5cS) (fun _ => true) true 0 true [] = some ([1, 0, 1], true) := by decide

theorem exec_fig5a : exec 100 (compile fig5a) (fun _ => false) true 0 true [] = some ([0, 1], true) := by decide

theorem not_behaves_of_true {f : TwoSat} (h1 : rtVal (imgOf f) 1 = true) : ¬ (imgOf f).Behaves fig5a := by
  refine not_behaves (c := true) (r := ([0, 1], true)) (r' := ([1, 0, 1], true)) exec_fig5cS_true exec_fig5a (by decide) ?_
  intro i hi
  change i ∈ codeReads (compile fig5cS) at hi
  rw [reads_fig5cS] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  exact h1

theorem hw5 : Assumptions (witness fig5a fig5cS) :=
  witness_assumptions (orig := fig5a) (prog := fig5cS) (by rw [reads_fig5cS]; simp)

/-- No forest. -/
@[expose] def dForce : Design := { witness fig5a fig5cS with forest := [], img := imgOf (impFormula 3 []) }

/-- Necessity of the forcing paths of S1 (`planted.forcing`): with no forest every other field of `Assumptions` holds and the
solver gives the free variables the value true, so the image misbehaves. -/
theorem nec_forcing :
    Obfuscates dForce.orig dForce.img.prog ∧ (∀ e ∈ dForce.forest, e.1.var < dForce.n ∧ e.2.var < dForce.n) ∧
      (∀ e ∈ dForce.forest, Respecting dForce.σ e) ∧ (∀ e ∈ dForce.extra, Respecting dForce.σ e) ∧
      (∀ e ∈ dForce.extra, e.1.var < dForce.n ∧ e.2.var < dForce.n) ∧
      dForce.img.formula = impFormula dForce.n (dForce.forest ++ dForce.extra) ∧
      (∀ k ∈ dForce.img.cells, k < dForce.n ∧ dForce.req k ∧ dForce.σ k = false) ∧
      dForce.circ.Topo ∧ FinalOrdered dForce.circ dForce.acts ∧ ¬ dForce.img.Behaves dForce.orig :=
  ⟨ob5c, by simp [dForce], by simp [dForce], hw5.extra_respects, dForce.extra_wf, by simp [dForce, imgOf, witness],
    hw5.cells_planted, hw5.schedule_topo, hw5.schedule_ordered,
    not_behaves_of_true (f := impFormula 3 []) (by decide)⟩

/-- The image carries a different formula. -/
@[expose] def dStamp : Design := { witness fig5a fig5cS with img := imgOf (impFormula 3 []) }

/-- Necessity of stamping (`stamped`): the planted data are the witness's, but the image carries a different formula. -/
theorem nec_stamped :
    Obfuscates dStamp.orig dStamp.img.prog ∧ Planted dStamp.n dStamp.σ dStamp.req dStamp.forest ∧
      (∀ e ∈ dStamp.extra, Respecting dStamp.σ e) ∧ (∀ e ∈ dStamp.extra, e.1.var < dStamp.n ∧ e.2.var < dStamp.n) ∧
      (∀ k ∈ dStamp.img.cells, k < dStamp.n ∧ dStamp.req k ∧ dStamp.σ k = false) ∧
      dStamp.circ.Topo ∧ FinalOrdered dStamp.circ dStamp.acts ∧
      dStamp.img.formula.clauses ≠ (impFormula dStamp.n (dStamp.forest ++ dStamp.extra)).clauses ∧
      ¬ dStamp.img.Behaves dStamp.orig :=
  ⟨ob5c, hw5.planted, hw5.extra_respects, dStamp.extra_wf, hw5.cells_planted, hw5.schedule_topo, hw5.schedule_ordered,
    by simp [dStamp, imgOf, witness, impFormula],
    not_behaves_of_true (f := impFormula 3 []) (by decide)⟩

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
  { witness fig5a fig5cS with σ := (fun _ => true), forest := forestT, img := imgOf (impFormula 3 forestT) }

/-- Necessity of the false intended values of the cells (`cells_planted`, third conjunct): with intended value true the
formula is planted for that assignment and the solver returns it, so the opaque conditions are true and the image misbehaves. -/
theorem nec_false_cells :
    Obfuscates dFalse.orig dFalse.img.prog ∧ Planted dFalse.n dFalse.σ dFalse.req dFalse.forest ∧
      (∀ e ∈ dFalse.extra, Respecting dFalse.σ e) ∧ (∀ e ∈ dFalse.extra, e.1.var < dFalse.n ∧ e.2.var < dFalse.n) ∧
      dFalse.img.formula = impFormula dFalse.n (dFalse.forest ++ dFalse.extra) ∧
      (∀ k ∈ dFalse.img.cells, k < dFalse.n ∧ dFalse.req k) ∧ dFalse.circ.Topo ∧ FinalOrdered dFalse.circ dFalse.acts ∧
      ¬ dFalse.img.Behaves dFalse.orig :=
  ⟨ob5c, planted_true, by simp [dFalse, witness], by simp [dFalse, witness], by simp [dFalse, imgOf, witness],
    fun k hk => ((hw5.cells_planted k hk).imp id (·.1)), hw5.schedule_topo, hw5.schedule_ordered,
    not_behaves_of_true (f := impFormula 3 forestT) (by decide)⟩

/-- An extra implication that the intended assignment does not respect. -/
@[expose] def extraBad : List (Lit × Lit) := [(⟨1, false⟩, ⟨1, true⟩)]

@[expose] def dExtra : Design :=
  { witness fig5a fig5cS with extra := extraBad, extra_wf := by intro e he; simp [extraBad] at he; subst he; decide, img := imgOf (impFormula 3 ((witness fig5a fig5cS).forest ++ extraBad)) }

/-- Necessity of the extra implications respecting the intended assignment (`extra_respects`): with one that does not and
every other assumption kept, the stamped formula is unsatisfiable and the solver returns nothing (T3's conclusion that the
solver succeeds fails). -/
theorem nec_extra_respects :
    Obfuscates dExtra.orig dExtra.img.prog ∧ Planted dExtra.n dExtra.σ dExtra.req dExtra.forest ∧
      (∀ e ∈ dExtra.extra, e.1.var < dExtra.n ∧ e.2.var < dExtra.n) ∧
      dExtra.img.formula = impFormula dExtra.n (dExtra.forest ++ dExtra.extra) ∧
      (∀ k ∈ dExtra.img.cells, k < dExtra.n ∧ dExtra.req k ∧ dExtra.σ k = false) ∧ dExtra.circ.Topo ∧
      FinalOrdered dExtra.circ dExtra.acts ∧
      ¬ (∀ e ∈ dExtra.extra, Respecting dExtra.σ e) ∧ smcSolve dExtra.img.formula = none := by
  refine ⟨ob5c, hw5.planted, by decide, rfl, hw5.cells_planted, hw5.schedule_topo, hw5.schedule_ordered, ?_, by decide⟩
  intro h
  have := h (⟨1, false⟩, ⟨1, true⟩) (by simp [dExtra, witness, extraBad])
  simp [Respecting, Lit.Holds, dExtra, witness] at this

/-- No required variable. -/
@[expose] def dReq : Design :=
  { witness fig5a fig5cS with req := fun _ => False, forest := [], img := imgOf (impFormula 3 []) }

/-- Necessity of the cells being required variables (`cells_planted`, second conjunct): with no required variable the
planted data hold vacuously, every other assumption is kept, and the solver gives the free cell the value true, so the image
misbehaves. -/
theorem nec_req_cells :
    Obfuscates dReq.orig dReq.img.prog ∧ Planted dReq.n dReq.σ dReq.req dReq.forest ∧
      (∀ e ∈ dReq.extra, Respecting dReq.σ e) ∧ (∀ e ∈ dReq.extra, e.1.var < dReq.n ∧ e.2.var < dReq.n) ∧
      dReq.img.formula = impFormula dReq.n (dReq.forest ++ dReq.extra) ∧
      (∀ k ∈ dReq.img.cells, k < dReq.n ∧ ¬ dReq.req k ∧ dReq.σ k = false) ∧ dReq.circ.Topo ∧
      FinalOrdered dReq.circ dReq.acts ∧ ¬ dReq.img.Behaves dReq.orig :=
  ⟨ob5c, ⟨by simp [dReq], by simp [dReq], by simp [dReq]⟩, by simp [dReq, witness], by simp [dReq, witness],
    by simp [dReq, imgOf, witness],
    fun k hk => ⟨(hw5.cells_planted k hk).1, by simp [dReq], (hw5.cells_planted k hk).2.2⟩,
    hw5.schedule_topo, hw5.schedule_ordered, not_behaves_of_true (f := impFormula 3 []) (by decide)⟩

/-- A forest with the forcing implication of variable `1` and one implication that the intended assignment does not
respect. -/
@[expose] def forestBad : List (Lit × Lit) := [(⟨1, true⟩, ⟨1, false⟩), (⟨1, false⟩, ⟨1, true⟩)]

@[expose] def dForestBad : Design :=
  { witness fig5a fig5cS with req := fun x => x = 1, forest := forestBad, img := imgOf (impFormula 3 forestBad) }

/-- Necessity of the forest respecting the intended assignment (`planted.respect`): with every other assumption kept (the
forcing paths included), the stamped formula is unsatisfiable and the solver returns nothing (T3's conclusion that the
solver succeeds fails). -/
theorem nec_forest_respects :
    Obfuscates dForestBad.orig dForestBad.img.prog ∧
      (∀ e ∈ dForestBad.forest, e.1.var < dForestBad.n ∧ e.2.var < dForestBad.n) ∧
      (∀ x, x < dForestBad.n → dForestBad.req x →
        ImpPath dForestBad.forest ⟨x, !dForestBad.σ x⟩ ⟨x, dForestBad.σ x⟩) ∧
      (∀ e ∈ dForestBad.extra, Respecting dForestBad.σ e) ∧
      (∀ e ∈ dForestBad.extra, e.1.var < dForestBad.n ∧ e.2.var < dForestBad.n) ∧
      dForestBad.img.formula = impFormula dForestBad.n (dForestBad.forest ++ dForestBad.extra) ∧
      (∀ k ∈ dForestBad.img.cells, k < dForestBad.n ∧ dForestBad.req k ∧ dForestBad.σ k = false) ∧
      dForestBad.circ.Topo ∧ FinalOrdered dForestBad.circ dForestBad.acts ∧
      ¬ (∀ e ∈ dForestBad.forest, Respecting dForestBad.σ e) ∧ smcSolve dForestBad.img.formula = none := by
  refine ⟨ob5c, by decide, ?_, by simp [dForestBad, witness], by simp [dForestBad, witness],
    by simp [dForestBad, imgOf, witness], ?_, hw5.schedule_topo, hw5.schedule_ordered, ?_, by decide⟩
  · intro x _ hx
    subst hx
    exact .step (by simp [dForestBad, forestBad, witness]) (.refl _)
  · intro k hk
    have : k ∈ codeReads (compile fig5cS) := hk
    rw [reads_fig5cS] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    subst this
    exact ⟨by decide, rfl, rfl⟩
  · intro h
    have := h (⟨1, false⟩, ⟨1, true⟩) (by simp [dForestBad, forestBad, witness])
    simp [Respecting, Lit.Holds, dForestBad, witness] at this

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

/-- A circuit that is not numbered topologically although it is acyclic: vertex `0` copies vertex `1`, which is the constant
`true`. -/
@[expose] def ncirc : DCirc Bool where
  n := 2
  ps v := if v = 0 then [1] else []
  f v l := if v = 0 then l.headD false else true

/-- Necessity of the topological numbering of the circuit, with the other assumptions kept: `ncirc` has a schedule whose final
executions are in dependency order (`FinalOrdered`), yet the final value of vertex `0` differs from `valOf`, which executes the
vertices in numbering order. -/
theorem ncirc_not_topo : ¬ ncirc.Topo := by
  intro h
  have := h 0 (by decide) 1 (by simp [ncirc])
  omega

theorem ncirc_ordered : FinalOrdered ncirc (execs [1, 0] : List (Act Bool)) := by
  intro v hv
  have : v = 0 ∨ v = 1 := by simp [ncirc] at hv; omega
  rcases this with rfl | rfl
  · exact ⟨[(1, none)], [], rfl, by simp, by intro u _ a ha; simp at ha⟩
  · exact ⟨[], [(0, none)], rfl, by simp [execs], by intro u hu; simp [ncirc] at hu⟩

theorem ncirc_bad : runA ncirc (fun _ => false) (execs [1, 0]) 0 ≠ valOf ncirc (fun _ => false) 0 := by decide +kernel

end SmcIrred.Threat
