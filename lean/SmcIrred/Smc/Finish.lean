module

public import SmcIrred.Smc.Rel
public import SmcIrred.Tarjan.Finish

public section

namespace SmcIrred

variable {g : Digraph}

theorem SRel.with_stk {t : TState} {s : SState} {pend : Option Nat} (h : SRel g t s pend) (X : List (Option Nat))
    (pend' : Option Nat) (hX : StkRel t.stk X pend') : SRel g t { s with stk := X } pend' :=
  ⟨hX, h.idx, h.none_iff, h.stk_ent, h.done_ent, h.vis, h.disj, h.nodup, h.num_le, h.low, h.low_le, h.chk, h.chain,
    h.set, h.bound, h.pk⟩

/-- The component extraction pops the cells of the component, appends them to the chain, labels them with the root and
marks them finished; every other field is untouched. -/
theorem sExtract_spec (n w : Nat) : ∀ (N tl : List Nat) (s : SState) (fuel : Nat), w ∉ N → N.length + 1 ≤ fuel →
    s.stk = (N ++ w :: tl).map some →
    (sExtract n w fuel s).stk = tl.map some ∧ (sExtract n w fuel s).chain = s.chain ++ (N ++ [w]) ∧
    (∀ u, (sExtract n w fuel s).set u = if u ∈ N ++ [w] then w else s.set u) ∧
    (∀ u, (sExtract n w fuel s).ent u = if u ∈ N ++ [w] then some n else s.ent u) ∧
    (sExtract n w fuel s).idx = s.idx ∧ (sExtract n w fuel s).low = s.low ∧ (sExtract n w fuel s).chk = s.chk ∧
    (sExtract n w fuel s).pk = s.pk ∧ (sExtract n w fuel s).dep = s.dep := by
  intro N
  induction N with
  | nil =>
    intro tl s fuel _ hf hs
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    have hs' : s.stk = some w :: tl.map some := by simpa using hs
    have e : sExtract n w (k + 1) s = { s with stk := tl.map some, chain := s.chain ++ [w], set := fupd s.set w w, ent := fupd s.ent w (some n) } := by simp only [sExtract, hs', ↓reduceIte]
    rw [e]
    refine ⟨rfl, by simp, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · intro u
      by_cases e : u = w
      · subst e; simp [fupd]
      · simp [fupd, e]
    · intro u
      by_cases e : u = w
      · subst e; simp [fupd]
      · simp [fupd, e]
  | cons u0 N ih =>
    intro tl s fuel hw hf hs
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hs' : s.stk = some u0 :: ((N ++ w :: tl).map some) := by simpa using hs
    have hne : u0 ≠ w := fun e => hw (by simp [e])
    have hwN : w ∉ N := fun hm => hw (List.mem_cons_of_mem _ hm)
    have hfk : N.length + 1 ≤ k := by simp at hf; omega
    have hstep : sExtract n w (k + 1) s = sExtract n w k { s with stk := (N ++ w :: tl).map some, chain := s.chain ++ [u0], set := fupd s.set u0 w, ent := fupd s.ent u0 (some n) } := by
      simp only [sExtract, hs']
      simp [hne]
    rw [hstep]
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := ih tl { s with stk := (N ++ w :: tl).map some, chain := s.chain ++ [u0], set := fupd s.set u0 w, ent := fupd s.ent u0 (some n) } k hwN hfk rfl
    refine ⟨r1, ?_, ?_, ?_, r5, r6, r7, r8, r9⟩
    · rw [r2]; simp
    · intro u
      rw [r3]
      by_cases e : u = u0
      · subst e; simp [fupd]
      · simp only [fupd_ne _ _ e]
        by_cases hu : u ∈ N ++ [w]
        · simp [hu]
        · have : ¬ (u = u0 ∨ u ∈ N ++ [w]) := fun h => h.elim e hu
          simp [hu, e]
    · intro u
      rw [r4]
      by_cases e : u = u0
      · subst e; simp [fupd]
      · simp only [fupd_ne _ _ e]
        by_cases hu : u ∈ N ++ [w]
        · simp [hu]
        · simp [hu, e]

theorem sLeave_eq {t : TState} {s : SState} {pend : Option Nat} (h : SRel g t s pend) {v : Nat}
    (hq : pend = none ∨ pend = some v) {N tl : List Nat} (hstk : t.stk = N ++ v :: tl) (hdep : s.dep v = tl.length)
    (hN0 : pend = some v → N = []) :
    sLeave g.n v s = if s.chk v = true then { s with stk := (N ++ v :: tl).map some }
      else sExtract g.n v (N.length + 1 + tl.length) { s with stk := (N ++ v :: tl).map some } := by
  have e5 : (if s.stk.length = s.dep v then { s with stk := some v :: s.stk } else s) =
      ({ s with stk := (N ++ v :: tl).map some } : SState) := by
    rcases hq with hq | hq
    · subst hq
      have hs : s.stk = (N ++ v :: tl).map some := by have := h.stk; simp only [StkRel] at this; rw [this, hstk]
      have hne : ¬ s.stk.length = s.dep v := by rw [hs, hdep]; simp; omega
      simp only [hne, ↓reduceIte]
      rw [← hs]
    · subst hq
      obtain ⟨tl', e1, e2⟩ := h.stk
      have hN := hN0 rfl
      subst hN
      have : tl' = tl := by rw [hstk] at e1; exact (List.cons.inj e1).2.symm
      subst this
      have hc : s.stk.length = s.dep v := by rw [e2, hdep]; simp
      simp only [hc, ↓reduceIte]
      rw [e2]; simp
  unfold sLeave
  simp only [e5]
  have hl : ({ s with stk := (N ++ v :: tl).map some } : SState).stk.length = N.length + 1 + tl.length := by simp; omega
  simp only [hl]

theorem ssim_leave {t : TState} {s : SState} {pend : Option Nat} (h : SRel g t s pend) {v : Nat}
    (hq : pend = none ∨ pend = some v) (hvn : t.num v ≠ 0) {N tl : List Nat} (hstk : t.stk = N ++ v :: tl)
    (hdep : s.dep v = tl.length) (hN0 : pend = some v → N = []) :
    SRel g (tFinish v none t) (sLeave g.n v s) none ∧ (sLeave g.n v s).low v = s.low v ∧
    (sLeave g.n v s).dep = s.dep ∧ ((tFinish v none t).stk = tl ∨ (tFinish v none t).stk = t.stk) ∧
    (tFinish v none t).num = t.num ∧ (tFinish v none t).low = t.low := by
  have hnd := h.nodup
  rw [hstk] at hnd
  have hv : v ∉ N := fun hm => (List.nodup_append.1 hnd).2.2 v hm v List.mem_cons_self rfl
  have hvtl : v ∉ tl := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
  have hdisjN : ∀ u ∈ N, u ∉ tl := fun u hu hm => (List.nodup_append.1 hnd).2.2 u hu u (List.mem_cons_of_mem _ hm) rfl
  have hndtl : tl.Nodup := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).2
  rw [sLeave_eq h hq hstk hdep hN0]
  have hX : StkRel t.stk ((N ++ v :: tl).map some) none := by simp [StkRel, hstk]
  by_cases hc : s.chk v = true
  · have hlt : t.low v < t.num v := (h.chk v hvn).1 hc
    have hne : ¬ t.low v = t.num v := by omega
    have hT : tFinish v none t = t := by unfold tFinish; simp [hne]
    rw [if_pos hc, hT]
    exact ⟨h.with_stk _ none hX, rfl, rfl, Or.inr rfl, rfl, rfl⟩
  · have hlt : ¬ t.low v < t.num v := fun hh => hc ((h.chk v hvn).2 hh)
    have hle := h.low_le v hvn
    have heq : t.low v = t.num v := by omega
    have hpt : popTo v t.stk = (N ++ [v], tl) := by rw [hstk]; exact popTo_split hv
    have hT : tFinish v none t = { t with stk := tl, out := t.out ++ [N ++ [v]], ticks := t.ticks + (N ++ [v]).length } := by
      unfold tFinish; simp [heq, hpt]
    have hcfalse : ¬ s.chk v = true := hc
    rw [if_neg hcfalse, hT]
    have hf : N.length + 1 ≤ N.length + 1 + tl.length := by omega
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := sExtract_spec g.n v N tl { s with stk := (N ++ v :: tl).map some }
      (N.length + 1 + tl.length) hv hf rfl
    have hCsub : ∀ u, u ∈ N ++ [v] → u ∈ t.stk := by
      intro u hu
      rw [hstk]
      rcases List.mem_append.1 hu with hu | hu
      · exact List.mem_append_left _ hu
      · rw [List.mem_singleton] at hu; subst hu; exact List.mem_append_right _ List.mem_cons_self
    have hnotC : ∀ u, u ∈ tl → u ∉ N ++ [v] := by
      intro u hu hm
      rcases List.mem_append.1 hm with hm | hm
      · exact hdisjN u hm hu
      · rw [List.mem_singleton] at hm; subst hm; exact hvtl hu
    have holdC : ∀ u, t.Done u → u ∉ N ++ [v] := fun u hd hm => h.disj u (hCsub u hm) hd
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, congrFun r6 v, r9, Or.inl rfl, rfl, rfl⟩
    · exact r1
    · rw [r5]; exact h.idx
    · intro u
      rw [r4 u]
      by_cases hu : u ∈ N ++ [v]
      · have := h.stk_ent u (hCsub u hu)
        have hn0 : t.num u ≠ 0 := fun h0 => by rw [(h.none_iff u).2 h0] at this; simp at this
        simp [hu, hn0]
      · simp only [hu, ↓reduceIte]; exact h.none_iff u
    · intro u hu
      rw [r4 u]
      simp only [hnotC u hu, ↓reduceIte]
      exact h.stk_ent u (by rw [hstk]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hu))
    · intro u hd
      rw [r4 u]
      obtain ⟨C', hC', hu⟩ := hd
      rcases List.mem_append.1 hC' with hC' | hC'
      · have hd' : t.Done u := ⟨C', hC', hu⟩
        simp only [holdC u hd', ↓reduceIte]
        exact h.done_ent u hd'
      · rw [List.mem_singleton] at hC'; subst hC'
        simp [hu]
    · intro u hu
      rcases h.vis u hu with hs | hd
      · rw [hstk] at hs
        rcases List.mem_append.1 hs with hs | hs
        · right; exact ⟨N ++ [v], by simp, List.mem_append_left _ hs⟩
        · rcases List.mem_cons.1 hs with rfl | hs
          · right; exact ⟨N ++ [u], by simp, by simp⟩
          · left; exact hs
      · right; obtain ⟨C', hC', hu'⟩ := hd; exact ⟨C', List.mem_append_left _ hC', hu'⟩
    · intro u hu hd
      obtain ⟨C', hC', hu'⟩ := hd
      rcases List.mem_append.1 hC' with hC' | hC'
      · exact h.disj u (by rw [hstk]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hu)) ⟨C', hC', hu'⟩
      · rw [List.mem_singleton] at hC'; subst hC'; exact hnotC u hu hu'
    · exact hndtl
    · exact h.num_le
    · intro u hu
      rw [r6]; exact h.low u hu
    · intro u hu
      exact h.low_le u hu
    · intro u hu
      rw [r7]; exact h.chk u hu
    · rw [r2]
      have := h.chain
      simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
      rw [show ({ s with stk := (N ++ v :: tl).map some } : SState).chain = t.out.flatten from this]
    · intro C' hC'
      rcases List.mem_append.1 hC' with hC' | hC'
      · obtain ⟨r0, hr0, hr1⟩ := h.set C' hC'
        refine ⟨r0, hr0, fun u hu => ?_⟩
        rw [r3 u]
        simp only [holdC u ⟨C', hC', hu⟩, ↓reduceIte]
        exact hr1 u hu
      · rw [List.mem_singleton] at hC'; subst hC'
        refine ⟨v, by simp, fun u hu => ?_⟩
        rw [r3 u]; simp [hu]
    · obtain ⟨L, hL1, hL2, hL3, hL4⟩ := h.bound
      refine ⟨L, hL1, fun u => ?_, by rw [r5]; exact hL3, hL4⟩
      rw [r4 u]
      by_cases hu : u ∈ N ++ [v]
      · have : s.ent u ≠ none := by
          have := h.stk_ent u (hCsub u hu); rw [this]; simp
        simp only [hu, ↓reduceIte]
        constructor
        · intro _; simp
        · intro _; exact (hL2 u).2 this
      · simp only [hu, ↓reduceIte]; exact hL2 u
    · intro u hu
      rw [r4 u] at hu
      by_cases hmu : u ∈ N ++ [v]
      · simp [hmu] at hu
      · simp only [hmu, ↓reduceIte] at hu
        rw [r8]; exact h.pk u hu

end SmcIrred
