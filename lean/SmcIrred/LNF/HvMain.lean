module

public import SmcIrred.LNF.HvStep

public section

namespace SmcIrred

variable {g : Digraph} {r : Nat} {J : Jungle}

/-- Processing the vertex `w` preserves the invariant of Havlak's algorithm. -/
theorem hstep {Pr : Nat → Prop} {hs : HavlakState} {w : Nat} (hi : HInv g J r Pr hs) (sh : SH g J Pr w) :
    HInv g J r (fun u => Pr u ∨ u = w) (havlakStep g J hs w) := by
  have env := hi.env sh
  obtain ⟨mem, ext, irr, hres, hnd, hmem, hext, hextc, hirr⟩ := drain_result env
  have hmc : ∀ x, mem.contains x = true ↔ x ∈ mem := fun x => by simp
  have hm : ∀ x, mem.contains x = true ↔ (RepZ g J w (ufFind hs.uf g.n) x ∧ x < g.n) := fun x => by
    rw [hmc, hmem]
  have hstepEq : havlakStep g J hs w =
      ⟨fun x => if mem.contains x = true then w else hs.uf x,
       fun x => if mem.contains x = true then some w else hs.hdr x,
       fun x => if x = w then (irr || hs.irr x) else hs.irr x,
       fun x => if x = w then hs.extra w ++ ext else hs.extra x⟩ := by
    simp only [havlakStep]
    rw [hres]
  have huf : ∀ x, (havlakStep g J hs w).uf x = if mem.contains x = true then w else hs.uf x := by
    intro x; rw [hstepEq]
  have hhdr : ∀ x, (havlakStep g J hs w).hdr x = if mem.contains x = true then some w else hs.hdr x := by
    intro x; rw [hstepEq]
  have hirrE : ∀ x, (havlakStep g J hs w).irr x = if x = w then (irr || hs.irr x) else hs.irr x := by
    intro x; rw [hstepEq]
  have hext' : ∀ x, (havlakStep g J hs w).extra x = if x = w then hs.extra w ++ ext else hs.extra x := by
    intro x; rw [hstepEq]
  have hufE : (havlakStep g J hs w).uf = fun x => if mem.contains x = true then w else hs.uf x := by
    funext x; exact huf x
  have hwr : hs.uf w = w := by
    apply Classical.byContradiction
    intro hne
    exact sh.nw (hi.ufPr w hne)
  have hmw : mem.contains w = false := by
    cases h : mem.contains w
    · rfl
    · exfalso
      exact (mem_facts hi sh ((hm w).1 h).1).2.2.1 rfl
  have hM : ∀ x, mem.contains x = true → hs.uf x = x ∧ x < g.n ∧ J.pre w < J.pre x := by
    intro x hx
    obtain ⟨hxn, _, _, _, hroot, hpre, _⟩ := mem_facts hi sh ((hm x).1 hx).1
    exact ⟨hroot, hxn, hpre⟩
  have hfind : ∀ x, x < g.n → ufFind (havlakStep g J hs w).uf g.n x =
      if mem.contains (ufFind hs.uf g.n x) = true then w else ufFind hs.uf g.n x := by
    intro x hx
    rw [hufE]
    exact find_update hi.chain (fun x => mem.contains x) w sh.wn hwr hmw hM g.n x hx (pcnt_le J g.n x)
  have hcongr : ∀ a b, a < g.n → b < g.n → ufFind hs.uf g.n a = ufFind hs.uf g.n b →
      ufFind (havlakStep g J hs w).uf g.n a = ufFind (havlakStep g J hs w).uf g.n b := by
    intro a b ha hb h
    rw [hfind a ha, hfind b hb, h]
  have hnil : hs.extra w = [] := by
    cases h : hs.extra w with
    | nil => rfl
    | cons e l =>
      exfalso
      exact sh.nw (hi.es w e (by rw [h]; exact List.mem_cons_self)).2.1.1
  refine ⟨hi.hv, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hne
    rw [huf x] at hne ⊢
    by_cases hx : mem.contains x = true
    · simp only [hx, ↓reduceIte] at hne ⊢
      obtain ⟨hxn, _, _, _, _, hpre, _⟩ := mem_facts hi sh ((hm x).1 hx).1
      exact ⟨sh.wn, hpre⟩
    · simp only [hx] at hne ⊢
      exact hi.chain x hne
  · intro x hne
    rw [huf x] at hne
    by_cases hx : mem.contains x = true
    · exact Or.inl (mem_facts hi sh ((hm x).1 hx).1).2.2.2.2.2.2.2
    · simp only [hx] at hne
      exact Or.inl (hi.ufPr x hne)
  · exact fdO_step hi sh (fun x => mem.contains x) hm _ hfind
  · exact hdr_step hi sh (fun x => mem.contains x) hm _ hhdr
  · refine irr_step hi sh irr hirr _ ?_
    intro w'
    rw [hirrE w']
    by_cases e : w' = w
    · subst e; rfl
    · simp only [e, ↓reduceIte]
  · intro h e he
    rw [hext' h] at he
    by_cases hw : h = w
    · subst hw
      simp only [↓reduceIte, hnil, List.nil_append] at he
      obtain ⟨elt, y0, ⟨z0, hb, hzw, hed, hna⟩, hfe⟩ := hext e he
      exact ⟨elt, ⟨Or.inr rfl, hb.1⟩, y0, z0, hb, hzw, hed, hna, hcongr e y0 elt hed.1 hfe⟩
    · simp only [hw, ↓reduceIte] at he
      obtain ⟨elt, hp, y, z, hb, hz, hed, hna, hfe⟩ := hi.es h e he
      exact ⟨elt, ⟨Or.inl hp.1, hp.2⟩, y, z, hb, hz, hed, hna, hcongr e y elt hed.1 hfe⟩
  · intro h hp z hb hzh y hed hna
    rw [hext' h]
    by_cases hw : h = w
    · subst hw
      simp only [↓reduceIte, hnil, List.nil_append]
      obtain ⟨e, he, hfe⟩ := hextc y z hb hzh hed hna
      exact ⟨e, he, hcongr e y (hext e he).1 hed.1 hfe⟩
    · simp only [hw, ↓reduceIte]
      have hpr : Pr h := by
        rcases hp.1 with h1 | h1
        · exact h1
        · exact absurd h1 hw
      obtain ⟨e, he, hfe⟩ := hi.ec h ⟨hpr, hp.2⟩ z hb hzh y hed hna
      exact ⟨e, he, hcongr e y (hi.es h e he).1 hed.1 hfe⟩

/-- The processing loop of Havlak's algorithm over a suffix of the vertices ordered by decreasing preorder. -/
theorem havlak_fold (hv : J.Valid g r) : ∀ (l pre : List Nat) (hs : HavlakState),
    pre ++ l = byPreDesc J g.n → HInv g J r (fun u => u ∈ pre) hs →
    HInv g J r (fun u => u ∈ pre ++ l) (l.foldl (havlakStep g J) hs) := by
  intro l
  induction l with
  | nil => intro pre hs _ hi; simpa using hi
  | cons w l ih =>
    intro pre hs hL hi
    have hstrict := byPreDesc_strict J g.n hv.pre_inj
    have hnd : (byPreDesc J g.n).Nodup := (byPreDesc_perm J g.n).nodup_iff.2 List.nodup_range
    rw [← hL] at hstrict hnd
    have hmem : ∀ u, u ∈ pre ++ w :: l ↔ u < g.n := fun u => by rw [hL]; exact mem_byPreDesc J g.n u
    have hpw := List.pairwise_append.1 hstrict
    have sh : SH g J (fun u => u ∈ pre) w :=
      { wn := (hmem w).1 (by simp)
        pr := fun u hu => ⟨(hmem u).1 (List.mem_append_left _ hu), hpw.2.2 u hu w List.mem_cons_self⟩
        desc := by
          intro u hu hanc huw
          rcases List.mem_append.1 ((hmem u).2 hu) with h | h
          · exact h
          · rcases List.mem_cons.1 h with h | h
            · exact absurd h huw
            · have h1 := (List.pairwise_cons.1 hpw.2.1).1 u h
              have h2 : J.pre w ≤ J.pre u := hanc.1
              omega
        nw := fun h => (List.nodup_append.1 hnd).2.2 w h w List.mem_cons_self rfl }
    have h1 := hstep hi sh
    have hfun : (fun u => u ∈ pre ∨ u = w) = (fun u => u ∈ pre ++ [w]) :=
      funext fun u => propext (by simp)
    rw [hfun] at h1
    have h2 := ih (pre ++ [w]) _ (by simpa using hL) h1
    simpa using h2

theorem havlak_inv (hv : J.Valid g r) : HInv g J r (fun u => u < g.n) (havlak g J) := by
  have hi0 : HInv g J r (fun u => u ∈ ([] : List Nat)) ⟨fun v => v, fun _ => none, fun _ => false, fun _ => []⟩ := by
    have hfun : (fun u => u ∈ ([] : List Nat)) = (fun _ => False) :=
      funext fun u => propext (by simp)
    rw [hfun]; exact HInv.init hv
  have h := havlak_fold hv (byPreDesc J g.n) [] _ (by simp) hi0
  have hfun : (fun u => u ∈ [] ++ byPreDesc J g.n) = (fun u => u < g.n) :=
    funext fun u => propext (by simpa using mem_byPreDesc J g.n u)
  rw [hfun] at h
  exact h

theorem procHdr_iff (g : Digraph) (J : Jungle) (h : Nat) :
    ProcHdr g J (fun u => u < g.n) h ↔ g.IsHeader J h :=
  ⟨fun hp => hp.2, fun hh => ⟨by obtain ⟨t, he, _⟩ := hh; exact he.2.1, hh⟩⟩

/-- Correctness of Havlak's algorithm (headers): the computed header of `x` is its parent in the loop nesting forest. -/
theorem havlak_hdr (hv : J.Valid g r) {x : Nat} (hx : x < g.n) (h : Nat) :
    (havlak g J).hdr x = some h ↔ g.LnfParent J h x := by
  rw [(havlak_inv hv).hdr x hx h]
  unfold ParentP Digraph.LnfParent
  simp only [procHdr_iff]

theorem havlak_hdr_none (hv : J.Valid g r) {x : Nat} (hx : x < g.n) :
    (havlak g J).hdr x = none ↔ ∀ h, ¬ g.LnfParent J h x := by
  constructor
  · intro hn h hp
    have := (havlak_hdr hv hx h).2 hp
    rw [hn] at this
    exact absurd this (by simp)
  · intro hall
    cases hh : (havlak g J).hdr x with
    | none => rfl
    | some h => exact absurd ((havlak_hdr hv hx h).1 hh) (hall h)

/-- Correctness of Havlak's algorithm (irreducibility): the flag of `w` is set exactly for irreducible loops. -/
theorem havlak_irr (hv : J.Valid g r) (w : Nat) :
    (havlak g J).irr w = true ↔ g.Irreducible J w := by
  rw [(havlak_inv hv).irr w]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨t, he, _⟩ := h.1
    exact ⟨he.2.1, h⟩

end SmcIrred
