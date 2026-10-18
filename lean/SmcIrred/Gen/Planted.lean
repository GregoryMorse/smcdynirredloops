module

public import SmcIrred.Spec.Generator
public import SmcIrred.Tarjan.Solver
public import SmcIrred.Smc.Solve

public section

namespace SmcIrred

theorem holds_neg (a : Nat → Bool) (l : Lit) : l.neg.Holds a ↔ ¬ l.Holds a := by
  unfold Lit.Holds Lit.neg
  cases h : a l.var <;> cases hp : l.pos <;> simp

theorem impFormula_sat (n : Nat) (imps : List (Lit × Lit)) (a : Nat → Bool) :
    (impFormula n imps).Sat a ↔ ∀ e ∈ imps, e.1.Holds a → e.2.Holds a := by
  unfold TwoSat.Sat impFormula ClauseSat
  simp only [List.mem_map]
  constructor
  · intro h e he h1
    obtain ⟨l, hl, hh⟩ := h _ ⟨e, he, rfl⟩
    rcases List.mem_cons.1 hl with rfl | hl
    · exact absurd h1 ((holds_neg a e.1).1 hh)
    · rw [List.mem_singleton.1 hl] at hh; exact hh
  · rintro h c ⟨e, he, rfl⟩
    by_cases h1 : e.1.Holds a
    · exact ⟨e.2, by simp, h e he h1⟩
    · exact ⟨e.1.neg, by simp, (holds_neg a e.1).2 h1⟩

theorem impFormula_wf (n : Nat) (imps : List (Lit × Lit)) (h : ∀ e ∈ imps, e.1.var < n ∧ e.2.var < n) :
    (impFormula n imps).Wf := by
  intro c hc
  simp only [impFormula, List.mem_map] at hc
  obtain ⟨e, he, rfl⟩ := hc
  refine ⟨by simp, ?_⟩
  intro l hl
  rcases List.mem_cons.1 hl with rfl | hl
  · exact (h e he).1
  · rw [List.mem_singleton.1 hl]; exact (h e he).2

theorem impFormula_ne_nil (n : Nat) (imps : List (Lit × Lit)) : ∀ c ∈ (impFormula n imps).clauses, c ≠ [] := by
  intro c hc
  simp only [impFormula, List.mem_map] at hc
  obtain ⟨e, _, rfl⟩ := hc
  simp

variable {n : Nat} {σ : Nat → Bool} {req : Nat → Prop} {forest extra : List (Lit × Lit)}

/-- The generated formula: the forest together with any further implications that respect `σ`. -/
theorem planted_sat (hp : Planted n σ req forest) (hx : ∀ e ∈ extra, Respecting σ e) :
    (impFormula n (forest ++ extra)).Sat σ := by
  rw [impFormula_sat]
  intro e he h1
  apply Classical.byContradiction
  intro h2
  rcases List.mem_append.1 he with he | he
  · exact hp.respect e he ⟨h1, h2⟩
  · exact hx e he ⟨h1, h2⟩

theorem impPath_holds {imps : List (Lit × Lit)} {a : Nat → Bool} (hs : ∀ e ∈ imps, e.1.Holds a → e.2.Holds a)
    {p q : Lit} (h : ImpPath imps p q) : p.Holds a → q.Holds a := by
  induction h with
  | refl _ => exact id
  | step he _ ih => exact fun h1 => ih (hs _ he h1)

/-- Forcing (C40): every solution of the generated formula agrees with the desired assignment on the required variables. -/
theorem forcing_agree (hp : Planted n σ req forest) {a : Nat → Bool}
    (ha : (impFormula n (forest ++ extra)).Sat a) {x : Nat} (hxn : x < n) (hr : req x) : a x = σ x := by
  rw [impFormula_sat] at ha
  have hs : ∀ e ∈ forest, e.1.Holds a → e.2.Holds a := fun e he => ha e (List.mem_append_left _ he)
  have hpath := impPath_holds hs (hp.forcing x hxn hr)
  have hnot : ¬ (⟨x, !σ x⟩ : Lit).Holds a := by
    intro h1
    have h2 := hpath h1
    unfold Lit.Holds at h1 h2
    simp only at h1 h2
    rw [h1] at h2
    cases hσ : σ x <;> simp [hσ] at h2
  unfold Lit.Holds at hnot
  simp only at hnot
  cases hσ : σ x <;> cases hax : a x <;> simp_all

theorem gen_wf (hp : Planted n σ req forest) (hwx : ∀ e ∈ extra, e.1.var < n ∧ e.2.var < n) :
    (impFormula n (forest ++ extra)).Wf := by
  apply impFormula_wf
  intro e he
  rcases List.mem_append.1 he with he | he
  · exact hp.wf e he
  · exact hwx e he

/-- The reference solver returns a solution of the generated formula and every such solution agrees with the desired
assignment on the required variables. -/
theorem planted_solve (hp : Planted n σ req forest) (hx : ∀ e ∈ extra, Respecting σ e)
    (hwx : ∀ e ∈ extra, e.1.var < n ∧ e.2.var < n) :
    ∃ a, twoSatSolve (impFormula n (forest ++ extra)) = some a ∧
      (impFormula n (forest ++ extra)).Sat a ∧ ∀ x, x < n → req x → a x = σ x := by
  obtain ⟨hnone, hsome⟩ := twoSatSolve_spec _ (gen_wf hp hwx) (impFormula_ne_nil _ _)
  cases h : twoSatSolve (impFormula n (forest ++ extra)) with
  | none => exact absurd (planted_sat hp hx) (hnone.1 h σ)
  | some a => exact ⟨a, rfl, hsome a h, fun x hxn hr => forcing_agree hp (hsome a h) hxn hr⟩

/-- The same for the self-modifying-code solver (Level 2 machine): its output is the set of true literal nodes. -/
theorem planted_smc (hp : Planted n σ req forest) (hx : ∀ e ∈ extra, Respecting σ e)
    (hwx : ∀ e ∈ extra, e.1.var < n ∧ e.2.var < n) :
    ∃ sol, smcSolve (impFormula n (forest ++ extra)) = some sol ∧
      ∀ x, x < n → req x → decide (2 * x ∈ sol) = σ x := by
  obtain ⟨hnone, hsome⟩ := smcSolve_spec _ (gen_wf hp hwx) (impFormula_ne_nil _ _)
  cases h : smcSolve (impFormula n (forest ++ extra)) with
  | none => exact absurd (planted_sat hp hx) (hnone.1 h σ)
  | some sol => exact ⟨sol, rfl, fun x hxn hr => forcing_agree hp (hsome sol h) hxn hr⟩

/-- P04, not sufficient: an implication from a true to a false literal, even when added without creating any loop,
destroys the desired assignment as a solution. -/
theorem counter_violates {a b : Lit} (h1 : a.Holds σ) (h2 : ¬ b.Holds σ) :
    ¬ (impFormula n (forest ++ (extra ++ [(a, b)]))).Sat σ := by
  rw [impFormula_sat]
  intro h
  exact h2 (h (a, b) (by simp) h1)

/-- P04, even worse: when both ends are required variables the formula has no solution at all. -/
theorem counter_unsat (hp : Planted n σ req forest) {a b : Lit} (h1 : a.Holds σ) (h2 : ¬ b.Holds σ)
    (ha : a.var < n) (hb : b.var < n) (hra : req a.var) (hrb : req b.var) :
    ∀ x, ¬ (impFormula n (forest ++ (extra ++ [(a, b)]))).Sat x := by
  intro x hx
  have e1 := forcing_agree hp hx ha hra
  have e2 := forcing_agree hp hx hb hrb
  have hax : a.Holds x := by unfold Lit.Holds at h1 ⊢; rw [e1]; exact h1
  rw [impFormula_sat] at hx
  have hbx := hx (a, b) (by simp) hax
  exact h2 (by unfold Lit.Holds at hbx ⊢; rw [← e2]; exact hbx)

/-- P04, not necessary: implications among literals that are true under `σ` keep `σ` a solution, even when they form a
loop (the two literals end up in one strongly connected component). -/
theorem loop_keeps (hp : Planted n σ req forest) {a b : Lit} (h1 : a.Holds σ) (h2 : b.Holds σ) :
    (impFormula n (forest ++ [(a, b), (b, a)])).Sat σ ∧
      ImpPath [(a, b), (b, a)] a b ∧ ImpPath [(a, b), (b, a)] b a := by
  refine ⟨planted_sat hp ?_, ?_, ?_⟩
  · intro e he
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact fun h => h.2 h2
    · exact fun h => h.2 h1
  · exact .step (by simp) (.refl _)
  · exact .step (by simp) (.refl _)

/-- P04: under the generator's condition no loop through a variable and its negation arises (it would need a path from
the `σ`-true literal to the `σ`-false one). -/
theorem no_loop_through_negation (hp : Planted n σ req forest) (hx : ∀ e ∈ extra, Respecting σ e) (x : Nat) :
    ¬ (ImpPath (forest ++ extra) ⟨x, true⟩ ⟨x, false⟩ ∧ ImpPath (forest ++ extra) ⟨x, false⟩ ⟨x, true⟩) := by
  rintro ⟨h1, h2⟩
  have hs : ∀ e ∈ forest ++ extra, e.1.Holds σ → e.2.Holds σ := by
    intro e he h
    apply Classical.byContradiction
    intro h'
    rcases List.mem_append.1 he with he | he
    · exact hp.respect e he ⟨h, h'⟩
    · exact hx e he ⟨h, h'⟩
  have a1 := impPath_holds hs h1
  have a2 := impPath_holds hs h2
  unfold Lit.Holds at a1 a2
  simp only at a1 a2
  cases hσ : σ x <;> simp_all

end SmcIrred
