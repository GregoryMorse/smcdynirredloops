module

public import SmcIrred.LNF.HvClose

public section

namespace SmcIrred

variable {g : Digraph} {r : Nat} {J : Jungle}

theorem dedup_aux : ∀ (l acc : List Nat), acc.Nodup →
    (l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) acc).Nodup ∧
    ∀ a, a ∈ l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) acc ↔ a ∈ acc ∨ a ∈ l := by
  intro l
  induction l with
  | nil => intro acc h; exact ⟨h, fun a => by simp⟩
  | cons b l ih =>
    intro acc h
    by_cases hc : acc.contains b = true
    · have hb : b ∈ acc := by simpa using hc
      simp only [List.foldl_cons, hc, ↓reduceIte]
      obtain ⟨h1, h2⟩ := ih acc h
      refine ⟨h1, fun a => ?_⟩
      rw [h2]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rintro (h | h)
        · exact Or.inl h
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inl hb
          · exact Or.inr h
    · have hb : b ∉ acc := by simpa using hc
      have hc' : acc.contains b = false := by simpa using hc
      simp only [List.foldl_cons, hc', Bool.false_eq_true, ↓reduceIte]
      have hnd : (acc ++ [b]).Nodup := List.nodup_append.2 ⟨h, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩, by
        intro x hx y hy hxy
        rw [List.mem_singleton] at hy
        subst hy; subst hxy
        exact hb hx⟩
      obtain ⟨h1, h2⟩ := ih (acc ++ [b]) hnd
      refine ⟨h1, fun a => ?_⟩
      rw [h2]
      constructor
      · rintro (h | h)
        · rcases List.mem_append.1 h with h | h
          · exact Or.inl h
          · exact Or.inr (by rw [List.mem_singleton] at h; subst h; exact List.mem_cons_self)
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rintro (h | h)
        · exact Or.inl (List.mem_append_left _ h)
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inl (List.mem_append_right _ (List.mem_singleton_self _))
          · exact Or.inr h

theorem dedup_nodup (l : List Nat) : (dedup l).Nodup := (dedup_aux l [] List.nodup_nil).1

theorem mem_dedup (l : List Nat) (a : Nat) : a ∈ dedup l ↔ a ∈ l := by
  unfold dedup
  rw [(dedup_aux l [] List.nodup_nil).2 a]
  simp

/-- The loop of `w`: the worklist loop computes exactly the representatives of the loop body, the recorded entries and the
irreducibility flag. -/
theorem drain_result {Pr : Nat → Prop} {w : Nat} {fd : Nat → Nat} {hs : HavlakState}
    (env : DEnv g J r Pr w fd hs.extra) :
    ∃ mem ext : List Nat, ∃ irr : Bool,
      havlakDrain g J w hs fd (g.n + 1)
        (dedup (((preds g w).filter fun v => decide (J.Anc w v ∧ v ≠ w)).map fd),
         dedup (((preds g w).filter fun v => decide (J.Anc w v ∧ v ≠ w)).map fd), [], false) = (mem, ext, irr) ∧
      mem.Nodup ∧ (∀ x, x ∈ mem ↔ RepZ g J w fd x ∧ x < g.n) ∧
      (∀ e ∈ ext, e < g.n ∧ ∃ y0, Entry g J w y0 ∧ fd e = fd y0) ∧
      (∀ y z, g.Body J w z → z ≠ w → g.edge y z → ¬ J.Anc w y → ∃ e ∈ ext, fd e = fd y) ∧
      (irr = true ↔ ∃ y0, Entry g J w y0) := by
  have hwn := env.sh.wn
  have hP0mem : ∀ t, t ≠ w → g.edge t w → J.Anc w t → fd t ∈
      dedup (((preds g w).filter fun v => decide (J.Anc w v ∧ v ≠ w)).map fd) := by
    intro t htw he ha
    rw [mem_dedup]
    refine List.mem_map.2 ⟨t, List.mem_filter.2 ⟨mem_preds.2 ⟨he.1, he.2.2⟩, ?_⟩, rfl⟩
    simp [ha, htw]
  have hd0 : Dinv g J w fd (dedup (((preds g w).filter fun v => decide (J.Anc w v ∧ v ≠ w)).map fd),
      dedup (((preds g w).filter fun v => decide (J.Anc w v ∧ v ≠ w)).map fd), [], false) := by
    refine ⟨dedup_nodup _, ?_, fun a ha => ha, fun e he => by simp at he, fun h => by simp at h⟩
    intro x hx
    rw [mem_dedup] at hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    obtain ⟨ht1, ht2⟩ := List.mem_filter.1 ht
    have hp := mem_preds.1 ht1
    have hc : J.Anc w t ∧ t ≠ w := by simpa using ht2
    have he : g.edge t w := ⟨hp.1, hwn, hp.2⟩
    have hbody : g.Body J w t := ⟨⟨t, he, hc.1⟩, Or.inr ⟨t, hc.2, ⟨he, hc.1⟩, .refl hp.1 hc⟩⟩
    exact ⟨fd_lt env hp.1, t, hbody, hc.2, rfl⟩
  have hlen : (dedup (((preds g w).filter fun v => decide (J.Anc w v ∧ v ≠ w)).map fd)).length ≤ g.n := by
    have hsub : (dedup (((preds g w).filter fun v => decide (J.Anc w v ∧ v ≠ w)).map fd)) ⊆ List.range g.n :=
      fun a ha => List.mem_range.2 (hd0.mem a ha).1
    have := List.Nodup.length_le_of_subset hd0.nodup hsub
    simpa using this
  obtain ⟨st', he, hd', hwl', hmem', hsd'⟩ := drain_spec env (g.n + 1) _ hd0 (fun x hx => Or.inl hx) (by dsimp only; omega)
  obtain ⟨h1, h2⟩ := close_spec env (st := st') (fun t htw he' ha => hmem' _ (hP0mem t htw he' ha)) hsd'
  refine ⟨st'.2.1, st'.2.2.1, st'.2.2.2, he, hd'.nodup, ?_, hd'.ext, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      exact ⟨(hd'.mem x hx).2, (hd'.mem x hx).1⟩
    · rintro ⟨⟨z, hz, hzw, rfl⟩, hlt⟩
      exact h1 z hz hzw
  · intro y z hz hzw he' hna
    obtain ⟨h3, _⟩ := h2 y z hz hzw he' hna
    exact ⟨fd y, h3, fd_idem env he'.1⟩
  · constructor
    · exact hd'.irr
    · rintro ⟨y0, z0, hz0, hz0w, he0, hna⟩
      exact (h2 y0 z0 hz0 hz0w he0 hna).2

end SmcIrred
