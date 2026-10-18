module

public import SmcIrred.Smc.Visit
public import SmcIrred.Tarjan.Solver
public import SmcIrred.Tarjan.TwoSatLink

public section

namespace SmcIrred

theorem revG_edge (g : Digraph) (a b : Nat) : (revG g).edge a b ↔ g.edge a b := by
  simp [Digraph.edge, revG]

theorem revG_reach (g : Digraph) : ∀ a b, (revG g).Reach a b ↔ g.Reach a b := by
  have key : ∀ (g1 g2 : Digraph), (∀ a b, g1.edge a b → g2.edge a b) → ∀ a b, g1.Reach a b → g2.Reach a b := by
    intro g1 g2 h a b hr
    induction hr with
    | refl a => exact Digraph.Reach.refl a
    | step e _ ih => exact Digraph.Reach.step (h _ _ e) ih
  intro a b
  exact ⟨key _ _ (fun a b => (revG_edge g a b).1) a b, key _ _ (fun a b => (revG_edge g a b).2) a b⟩

theorem revG_scc (g : Digraph) (a b : Nat) : (revG g).SameSCC a b ↔ g.SameSCC a b := by
  simp only [Digraph.SameSCC, revG_reach]

theorem sSolFold_none (lab : Nat → Nat) : ∀ (ch sol : List Nat),
    sSolFold lab ch sol = none ↔ ∃ x ∈ ch, lab x = lab (nneg x) := by
  intro ch
  induction ch with
  | nil => intro sol; simp [sSolFold]
  | cons x xs ih =>
    intro sol
    by_cases h : lab x = lab (nneg x)
    · simp [sSolFold, h]
    · simp [sSolFold, h, ih]

theorem sSolFold_append (lab : Nat → Nat) : ∀ (a b sol : List Nat),
    sSolFold lab (a ++ b) sol = (sSolFold lab a sol).bind (fun s => sSolFold lab b s) := by
  intro a
  induction a with
  | nil => intro b sol; simp [sSolFold]
  | cons x xs ih =>
    intro b sol
    by_cases h : lab x = lab (nneg x)
    · simp [sSolFold, h]
    · simp [sSolFold, h, ih]

/-- On a clash-free component the node-wise solution fold equals the legacy `tsComp`. -/
theorem sSolFold_comp (lab : Nat → Nat) : ∀ (C u sol : List Nat),
    (∀ v, (v ∈ u ∨ v ∈ C) → ¬ (nneg v ∈ u ∨ nneg v ∈ C)) → (∀ v ∈ C, lab v ≠ lab (nneg v)) →
    sSolFold lab C sol = some (tsComp C u (false, sol)).2 := by
  intro C
  induction C with
  | nil => intro u sol _ _; simp [sSolFold, tsComp]
  | cons v vs ih =>
    intro u sol hfree hset
    have hu : ¬ nneg v ∈ u := fun h => hfree v (Or.inr List.mem_cons_self) (Or.inl h)
    have hs : lab v ≠ lab (nneg v) := hset v List.mem_cons_self
    have hfree' : ∀ y, (y ∈ v :: u ∨ y ∈ vs) → ¬ (nneg y ∈ v :: u ∨ nneg y ∈ vs) := by
      intro y hy hn
      have hy' : y ∈ u ∨ y ∈ v :: vs := by
        rcases hy with hy | hy
        · rcases List.mem_cons.1 hy with rfl | hy
          · exact Or.inr List.mem_cons_self
          · exact Or.inl hy
        · exact Or.inr (List.mem_cons_of_mem _ hy)
      have hn' : nneg y ∈ u ∨ nneg y ∈ v :: vs := by
        rcases hn with hn | hn
        · rcases List.mem_cons.1 hn with h | hn
          · exact Or.inr (h ▸ List.mem_cons_self)
          · exact Or.inl hn
        · exact Or.inr (List.mem_cons_of_mem _ hn)
      exact hfree y hy' hn'
    have e : tsComp (v :: vs) u (false, sol) =
        tsComp vs (v :: u) (false, if nneg v ∈ sol then sol else v :: sol) := by
      simp [tsComp, hu]
    rw [e, ← ih (v :: u) (if nneg v ∈ sol then sol else v :: sol) hfree'
      (fun y hy => hset y (List.mem_cons_of_mem _ hy))]
    simp [sSolFold, hs]

theorem sSolFold_flat (lab : Nat → Nat) : ∀ (comps : List (List Nat)) (sol : List Nat),
    (∀ C ∈ comps, ∀ v ∈ C, nneg v ∉ C) → (∀ C ∈ comps, ∀ v ∈ C, lab v ≠ lab (nneg v)) →
    sSolFold lab comps.flatten sol = some (comps.foldl (fun st C => tsComp C [] st) (false, sol)).2 ∧
    (comps.foldl (fun st C => tsComp C [] st) (false, sol)).1 = false := by
  intro comps
  induction comps with
  | nil => intro sol _ _; simp [sSolFold]
  | cons C cs ih =>
    intro sol hn hl
    have hfree : ∀ v, (v ∈ ([] : List Nat) ∨ v ∈ C) → ¬ (nneg v ∈ ([] : List Nat) ∨ nneg v ∈ C) := by
      intro v hv hh
      rcases hv with hv | hv
      · simp at hv
      · rcases hh with hh | hh
        · simp at hh
        · exact hn C List.mem_cons_self v hv hh
    have hC := sSolFold_comp lab C [] sol hfree (hl C List.mem_cons_self)
    obtain ⟨hf1, _⟩ := tsComp_free C [] sol hfree
    have e : tsComp C [] (false, sol) = (false, (tsComp C [] (false, sol)).2) := Prod.ext hf1 rfl
    have ih' := ih (tsComp C [] (false, sol)).2 (fun D hD => hn D (List.mem_cons_of_mem _ hD))
      (fun D hD => hl D (List.mem_cons_of_mem _ hD))
    rw [List.foldl_cons, List.flatten_cons, sSolFold_append, hC]
    simp only [Option.bind_some]
    rw [e]
    exact ih'

theorem comp_unique (comps : List (List Nat)) (hnd : comps.flatten.Nodup) {C D : List Nat} (hC : C ∈ comps)
    (hD : D ∈ comps) {x : Nat} (hx : x ∈ C) (hxD : x ∈ D) : C = D := by
  obtain ⟨L, R, e⟩ := List.append_of_mem hC
  have hnd' : (L.flatten ++ (C ++ R.flatten)).Nodup := by
    have : comps.flatten = L.flatten ++ (C ++ R.flatten) := by rw [e]; simp
    rw [← this]; exact hnd
  have h1 := List.nodup_append.1 hnd'
  have h2 := List.nodup_append.1 h1.2.1
  have hD' : D ∈ L ∨ D = C ∨ D ∈ R := by
    rw [e] at hD
    simpa using hD
  rcases hD' with hL | rfl | hR
  · exfalso
    exact h1.2.2 x (List.mem_flatten.2 ⟨D, hL, hxD⟩) x (List.mem_append_left _ hx) rfl
  · rfl
  · exfalso
    exact h2.2.2 x hx x (List.mem_flatten.2 ⟨D, hR, hxD⟩) rfl

theorem compIdx_not_mem : ∀ (comps : List (List Nat)) (y : Nat), y ∉ comps.flatten → compIdx comps y = comps.length := by
  intro comps
  induction comps with
  | nil => intro y _; rfl
  | cons C cs ih =>
    intro y h
    have h1 : y ∉ C := fun hh => h (by simp [hh])
    have h2 : y ∉ cs.flatten := fun hh => h (by simp [hh])
    simp [compIdx, h1, ih y h2]

/-- The solution phase of the machine over the components it extracted (labelled by one member each) agrees with the
legacy `twosat` fold and with the component-index rule. -/
theorem smc_link (n : Nat) (comps : List (List Nat)) (lab : Nat → Nat) (hnd : comps.flatten.Nodup)
    (hcov : ∀ v, v < 2 * n → v ∈ comps.flatten) (hrng : ∀ C ∈ comps, ∀ w ∈ C, w < 2 * n)
    (hset : ∀ C ∈ comps, ∃ r ∈ C, ∀ u ∈ C, lab u = r) :
    (sSolFold lab comps.flatten [] = none ↔ ∃ x, x < n ∧ compIdx comps (2 * x) = compIdx comps (2 * x + 1)) ∧
    (∀ sol, sSolFold lab comps.flatten [] = some sol →
      (∀ x, x < n → (2 * x ∈ sol ↔ compIdx comps (2 * x) < compIdx comps (2 * x + 1))) ∧ ∀ y ∈ sol, y < 2 * n) := by
  obtain ⟨hl1, hl2⟩ := tsFold_link n comps hnd hcov hrng
  have hu := tsFold_unsat comps
  by_cases hB : ∃ C ∈ comps, ∃ v ∈ C, nneg v ∈ C
  · have hnone : sSolFold lab comps.flatten [] = none := by
      rw [sSolFold_none]
      obtain ⟨C, hC, v, hv, hn⟩ := hB
      obtain ⟨r, _, hr⟩ := hset C hC
      exact ⟨v, List.mem_flatten.2 ⟨C, hC, hv⟩, by rw [hr v hv, hr _ hn]⟩
    refine ⟨?_, ?_⟩
    · rw [hnone]
      have : (tsFold comps).1 = true := hu.2 hB
      exact ⟨fun _ => hl1.1 this, fun _ => rfl⟩
    · intro sol h; rw [hnone] at h; exact absurd h (by simp)
  · have hn : ∀ C ∈ comps, ∀ v ∈ C, nneg v ∉ C := fun C hC v hv hh => hB ⟨C, hC, v, hv, hh⟩
    have hl : ∀ C ∈ comps, ∀ v ∈ C, lab v ≠ lab (nneg v) := by
      intro C hC v hv he
      have hvl : nneg v ∈ comps.flatten := hcov _ (nneg_lt (hrng C hC v hv))
      obtain ⟨D, hD, hvD⟩ := List.mem_flatten.1 hvl
      obtain ⟨r1, hr1, h1⟩ := hset C hC
      obtain ⟨r2, hr2, h2⟩ := hset D hD
      have hr : r1 = r2 := by rw [← h1 v hv, ← h2 _ hvD, he]
      have : C = D := comp_unique comps hnd hC hD hr1 (hr ▸ hr2)
      subst this
      exact hn C hC v hv hvD
    obtain ⟨hs1, hs2⟩ := sSolFold_flat lab comps [] hn hl
    have hfl : (tsFold comps).1 = false := hs2
    have hsome : sSolFold lab comps.flatten [] = some (tsFold comps).2 := hs1
    refine ⟨?_, ?_⟩
    · rw [hsome]
      constructor
      · intro h; exact absurd h (by simp)
      · intro hx
        have := hl1.2 hx
        rw [hfl] at this
        exact absurd this (by simp)
    · intro sol h
      rw [hsome] at h
      have hsol : (tsFold comps).2 = sol := Option.some.inj h
      subst hsol
      refine ⟨fun x hx => hl2 hfl x hx, fun y hy => ?_⟩
      have := (tsFold_sol comps hnd hfl y).1 hy
      obtain ⟨C, hC, hyC⟩ := List.mem_flatten.1 this.1
      exact hrng C hC y hyC

end SmcIrred
