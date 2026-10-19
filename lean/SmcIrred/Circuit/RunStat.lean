module

public import SmcIrred.Spec.RunStat

public section

namespace SmcIrred

/-! # The statistic of `do_run_virtual` (C49, G29)

The reported edge count of a run is the structural count (`edgesOf`) plus the number of active inputs, so it depends on the
input; the dictionary of subgraph statistics reports the sum over the executed runs exactly when all runs of the same
subgraph have the same statistic (the "constant time" case), and in general it multiplies the first run's statistic by the
number of runs. -/

theorem pyEdges_eq (c : Circ) (inp : Nat → Bool) :
    pyEdges c inp = ((List.range c.n).map (edgesOf c)).sum + (List.range c.n).countP (fun x => inp x) := by
  unfold pyEdges edgesOf
  induction c.n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_append, List.sum_append, List.countP_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.countP_cons, List.countP_nil]
    by_cases h : inp n = true <;> simp [h] <;> omega

/-- Two inputs of the same circuit with different numbers of active inputs give different reported edge counts, so the reported
edge count is not constant time in the number of examined edges. -/
theorem pyEdges_data_dependent :
    ∃ (c : Circ) (i1 i2 : Nat → Bool), pyEdges c i1 ≠ pyEdges c i2 :=
  ⟨⟨1, fun _ => .flow, fun _ => []⟩, fun _ => true, fun _ => false, by decide⟩

theorem dictAdd_keys_nodup (d : StatDict) (sid : Nat) (st : Nat × Nat) (hnd : (d.map (·.1)).Nodup) :
    ((dictAdd d sid st).map (·.1)).Nodup := by
  unfold dictAdd
  by_cases h : d.any (fun e => e.1 == sid) = true
  · simp only [h, ↓reduceIte]
    have : (d.map fun e => if e.1 == sid then (e.1, e.2.1, e.2.2 + 1) else e).map (·.1) = d.map (·.1) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro e _
      by_cases he : (e.1 == sid) = true
      · simp only [Function.comp, he, ↓reduceIte]
      · simp only [Function.comp, he, Bool.false_eq_true, ↓reduceIte]
    rw [this]; exact hnd
  · simp only [h, Bool.false_eq_true, ↓reduceIte, List.map_append, List.map_cons, List.map_nil]
    rw [List.nodup_append]
    refine ⟨hnd, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩, ?_⟩
    intro a ha b hb hab
    have hb' : b = sid := by simpa using hb
    subst hb'
    subst hab
    apply h
    simp only [List.any_eq_true]
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
    exact ⟨e, he, by simp⟩

theorem dW_update_old (f : Nat × Nat → Nat) (sid : Nat) (st : Nat × Nat) : ∀ (d : StatDict), (d.map (·.1)).Nodup →
    d.any (fun e => e.1 == sid) = true → (∀ e ∈ d, e.1 = sid → e.2.1 = st) →
    dW f (d.map fun e => if e.1 == sid then (e.1, e.2.1, e.2.2 + 1) else e) = dW f d + f st := by
  intro d
  induction d with
  | nil => intro _ h; simp at h
  | cons e t ih =>
    intro hnd hany hst
    rw [List.map_cons, List.nodup_cons] at hnd
    by_cases he : e.1 = sid
    · have hnt : ∀ x ∈ t, x.1 ≠ sid := by
        intro x hx hxs
        exact hnd.1 (List.mem_map.2 ⟨x, hx, by rw [hxs, he]⟩)
      have hmap : (t.map fun x => if x.1 == sid then (x.1, x.2.1, x.2.2 + 1) else x) = t := by
        conv => rhs; rw [← List.map_id t]
        apply List.map_congr_left
        intro x hx
        have := hnt x hx
        simp [this]
      have hes := hst e (by simp) he
      unfold dW
      simp only [List.map_cons, hmap, he, beq_self_eq_true, ↓reduceIte, List.sum_cons]
      rw [hes, Nat.mul_add]
      omega
    · have hany' : t.any (fun x => x.1 == sid) = true := by
        simp only [List.any_cons] at hany
        have : (e.1 == sid) = false := by simpa using he
        simpa [this] using hany
      have := ih hnd.2 hany' (fun x hx => hst x (by simp [hx]))
      unfold dW at this ⊢
      have hb : (e.1 == sid) = false := by simpa using he
      simp only [List.map_cons, hb, Bool.false_eq_true, ↓reduceIte, List.sum_cons] at this ⊢
      omega

theorem dictAdd_dW (f : Nat × Nat → Nat) (d : StatDict) (sid : Nat) (st : Nat × Nat) (hnd : (d.map (·.1)).Nodup)
    (hst : ∀ e ∈ d, e.1 = sid → e.2.1 = st) : dW f (dictAdd d sid st) = dW f d + f st := by
  by_cases h : d.any (fun e => e.1 == sid) = true
  · unfold dictAdd
    simp only [h, ↓reduceIte]
    exact dW_update_old f sid st d hnd h hst
  · unfold dictAdd dW
    have h' : d.any (fun e => e.1 == sid) = false := Bool.eq_false_iff.2 h
    simp only [h', Bool.false_eq_true, ↓reduceIte, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    omega

theorem dictFold_dW (f : Nat × Nat → Nat) : ∀ (runs : List (Nat × (Nat × Nat))) (d : StatDict),
    (d.map (·.1)).Nodup → (∀ r ∈ runs, ∀ e ∈ d, e.1 = r.1 → e.2.1 = r.2) →
    (∀ r ∈ runs, ∀ r' ∈ runs, r.1 = r'.1 → r.2 = r'.2) →
    dW f (runs.foldl (fun d r => dictAdd d r.1 r.2) d) = dW f d + runsW f runs := by
  intro runs
  induction runs with
  | nil => intro d _ _ _; simp [runsW]
  | cons r t ih =>
    intro d hnd h1 h2
    rw [List.foldl_cons]
    have hr : ∀ e ∈ d, e.1 = r.1 → e.2.1 = r.2 := h1 r (by simp)
    have hnd' := dictAdd_keys_nodup d r.1 r.2 hnd
    have hadd := dictAdd_dW f d r.1 r.2 hnd hr
    have hnew : ∀ r' ∈ t, ∀ e ∈ dictAdd d r.1 r.2, e.1 = r'.1 → e.2.1 = r'.2 := by
      intro r' hr' e he hee
      unfold dictAdd at he
      by_cases h : d.any (fun e => e.1 == r.1) = true
      · simp only [h, ↓reduceIte, List.mem_map] at he
        obtain ⟨e0, he0, rfl⟩ := he
        by_cases hk : (e0.1 == r.1) = true
        · simp only [hk, ↓reduceIte] at hee ⊢
          have := h2 r (by simp) r' (by simp [hr']) ((beq_iff_eq.1 hk).symm.trans hee)
          rw [← this]; exact hr e0 he0 (beq_iff_eq.1 hk)
        · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hee ⊢
          exact h1 r' (by simp [hr']) e0 he0 hee
      · simp only [h, Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_singleton] at he
        rcases he with he | he
        · exact h1 r' (by simp [hr']) e he hee
        · subst he
          exact (h2 r (by simp) r' (by simp [hr']) hee)
    rw [ih _ hnd' hnew (fun a ha b hb => h2 a (by simp [ha]) b (by simp [hb])), hadd]
    unfold runsW
    simp only [List.map_cons, List.sum_cons]
    omega

/-- **The dictionary reports the executed runs exactly when the runs of each subgraph have equal statistics.** -/
theorem dictOf_total_uniform (runs : List (Nat × (Nat × Nat)))
    (hu : ∀ r ∈ runs, ∀ r' ∈ runs, r.1 = r'.1 → r.2 = r'.2) :
    dictTotal (dictOf runs) = runsTotal runs := by
  have h1 := dictFold_dW Prod.fst runs [] (by simp) (by simp) hu
  have h2 := dictFold_dW Prod.snd runs [] (by simp) (by simp) hu
  unfold dictTotal runsTotal dictOf
  rw [h1, h2]
  simp [dW]

/-- Without equal statistics the dictionary multiplies the first run's statistic by the number of runs: two runs of the same
subgraph with statistics `(1, 1)` and `(2, 2)` are reported as `(2, 2)`, the executed total is `(3, 3)`. -/
theorem dictOf_total_nonuniform :
    dictTotal (dictOf [(0, (1, 1)), (0, (2, 2))]) = (2, 2) ∧ runsTotal [(0, (1, 1)), (0, (2, 2))] = (3, 3) := by
  decide

end SmcIrred
