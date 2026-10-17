module

public import SmcIrred.Graph.DfsDone

public section

namespace SmcIrred

variable {g : Digraph}

theorem undisc_pos {s : DfsState} {v : Nat} (hv : v < g.n) (h0 : s.pre v = 0) : 0 < s.undisc g := by
  unfold DfsState.undisc
  apply List.length_pos_of_mem (a := v)
  simp [List.mem_filter, h0, hv]

/-- Every fuel-bounded visit of an undiscovered vertex with enough fuel has the summary `Done`. -/
theorem visit_done : ∀ (fuel v : Nat) (s : DfsState), v < g.n → s.pre v = 0 → s.Wf → s.undisc g ≤ fuel →
    Done g v s (dfsVisit g fuel v s)
  | 0, v, s, hv, h0, _, hu => absurd (undisc_pos hv h0) (by omega)
  | fuel + 1, v, s, hv, h0, hw, hu => by
    show Done g v s (((g.succ v).foldl _ (s.opening v)).closing v)
    have hw1 := Wf.opening hw h0
    have hlt : (s.opening v).undisc g < s.undisc g := by
      refine undisc_lt (v := v) ?_ hv h0 ?_
      · intro x hx
        by_cases hxv : x = v
        · subst hxv; simp [DfsState.opening]; have := hw.clock; omega
        · simpa [DfsState.opening, hxv] using hx
      · simp [DfsState.opening]; have := hw.clock; omega
    have hL := foldl_loop (s1 := s.opening v) (v := v) hv (fuel := fuel) (by omega) (visit_done fuel)
      (g.succ v) [] (s.opening v) (fun _ h => h) (Loop.init hw1)
    exact Done.of_loop hw hv h0 (by simpa using hL)

/-- The depth-first search from the root of a CFG produces a valid jungle (hence the declarative description of a
DFS in `Jungle.Valid` covers the algorithm), for any starting clock `c ≥ 1`. -/
theorem dfsRun_valid {r c : Nat} (hcfg : g.IsCFG r) (hc : 1 ≤ c) : (dfsRun g r c).Valid g r := by
  have hr : r < g.n := hcfg.1
  have wf0 : (DfsState.mk c (fun _ => 0) (fun _ => 0)).Wf :=
    ⟨hc, fun _ => by simp; omega, fun _ => by simp; omega, fun _ h => absurd rfl h⟩
  have hu : (DfsState.mk c (fun _ => 0) (fun _ => 0)).undisc g ≤ g.n + 1 := by
    unfold DfsState.undisc
    have := List.length_filter_le (fun x : Nat => decide (((DfsState.mk c (fun _ => 0) (fun _ => 0)).pre x) = 0)) (List.range g.n)
    simp at this ⊢; omega
  have D := visit_done (g.n + 1) r _ hr rfl wf0 hu
  have hroot : ∀ s' : DfsState, s'.pre r = c → s'.pre r ≠ 0 := fun s' h => by omega
  unfold dfsRun
  dsimp only
  generalize dfsVisit g (g.n + 1) r (DfsState.mk c (fun _ => 0) (fun _ => 0)) = s' at D ⊢
  have hr1 : s'.pre r = c := D.vroot.1
  have hdisc : ∀ a b, g.Reach a b → s'.pre a ≠ 0 → s'.pre b ≠ 0 := by
    intro a b h
    induction h with
    | refl => exact id
    | step he _ ih =>
      intro ha
      exact ih (D.closure _ ⟨rfl, ha⟩ _ he).1
  have hnew : ∀ x, x < g.n → DfsState.New (DfsState.mk c (fun _ => 0) (fun _ => 0)) s' x :=
    fun x hx => ⟨rfl, hdisc r x (hcfg.2 x hx) (hroot s' hr1)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv; exact (D.new v (hnew v hv)).2.2.1
  · intro a b ha hb; exact (D.distinct a b (hnew a ha) (hnew b hb)).1
  · intro a b ha hb; exact (D.distinct a b (hnew a ha) (hnew b hb)).2.1
  · intro a b ha hb; exact (D.distinct a b (hnew a ha) (hnew b hb)).2.2
  · intro a b ha hb; exact D.laminar a b (hnew a ha) (hnew b hb)
  · intro v hv
    have h := D.contain v (hnew v hv)
    have h2 : s'.pre r ≤ s'.pre v ∧ s'.post v ≤ s'.post r := h
    exact h2
  · intro v hv hne
    obtain ⟨u, hu, he, hne2, hanc, hmin⟩ := D.parent v (hnew v hv) hne
    exact ⟨u, ⟨he.1, hne2, hanc, fun w hw hwv hwa => hmin w (hnew w hw) hwv hwa⟩, he⟩
  · intro a b he hlt
    have := (D.closure a (hnew a he.1) b he).2
    have hlt' : s'.post a < s'.pre b := hlt
    omega

end SmcIrred
