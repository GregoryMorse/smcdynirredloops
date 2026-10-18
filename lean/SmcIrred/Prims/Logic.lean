module

public import SmcIrred.Prims.Eval

public section

namespace SmcIrred

theorem ok_mono {n n' : Nat} {w : Wire} (h : w.ok n) (hle : n ≤ n') : w.ok n' := by
  cases w with
  | cst b => trivial
  | nd i => exact Nat.lt_of_lt_of_le h hle

theorem Post.ok_old {gb gb' : GB} {inp : Nat → Bool} {w : Wire} {v : Bool} (_ : Post gb gb' inp w v) {x : Wire}
    (hx : x.ok gb.n) : x.ok gb'.n := ok_mono hx (Post.ext ‹_›).n_le

theorem xorL_single (v : Bool) : xorL [v] = v := by cases v <;> rfl
theorem andL_single (v : Bool) : andL [v] = v := by cases v <;> rfl
theorem orL_single (v : Bool) : orL [v] = v := by cases v <;> rfl

theorem wev_cst (gb : GB) (inp : Nat → Bool) {w : Wire} (h : w.isc = true) : wev gb inp w = (w == .cst true) := by
  cases w with
  | cst b => cases b <;> simp [wev, Wire.ev]
  | nd i => exact absurd h (by simp [Wire.isc])

theorem andL_map_iff {α : Type} (f : α → Bool) (l : List α) : andL (l.map f) = true ↔ ∀ x ∈ l, f x = true := by
  unfold andL; simp [List.all_eq_true]

theorem orL_map_iff {α : Type} (f : α → Bool) (l : List α) : orL (l.map f) = true ↔ ∃ x ∈ l, f x = true := by
  unfold orL; simp [List.any_eq_true]

theorem map_idx_ev (gb : GB) (inp : Nat → Bool) (L : List Wire) (h : ∀ w ∈ L, w.isc = false) :
    (L.map Wire.idx).map (fun u => wev gb inp (.nd u)) = L.map (wev gb inp) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro w hw
  cases w with
  | cst b => exact absurd (h _ hw) (by simp [Wire.isc])
  | nd i => rfl

/-! ### The set of `and_to_virtual` -/

theorem dedupW_aux : ∀ (l acc : List Wire), acc.Nodup →
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

theorem dedupW_nodup (l : List Wire) : (dedupW l).Nodup := (dedupW_aux l [] List.nodup_nil).1

theorem mem_dedupW (l : List Wire) (a : Wire) : a ∈ dedupW l ↔ a ∈ l := by
  unfold dedupW
  rw [(dedupW_aux l [] List.nodup_nil).2 a]
  simp

theorem dedupW_id_aux : ∀ (l acc : List Wire), (acc ++ l).Nodup →
    l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) acc = acc ++ l := by
  intro l
  induction l with
  | nil => intro acc _; simp
  | cons b t ih =>
    intro acc h
    have hb : b ∉ acc := by
      intro hb
      have := (List.nodup_append.1 h).2.2 b hb b List.mem_cons_self
      exact this rfl
    have hc : acc.contains b = false := by simpa using hb
    simp only [List.foldl_cons, hc, Bool.false_eq_true, ↓reduceIte]
    rw [ih (acc ++ [b]) (by simpa using h)]
    simp

theorem dedupW_id (l : List Wire) (h : l.Nodup) : dedupW l = l := by
  unfold dedupW
  rw [dedupW_id_aux l [] (by simpa using h)]
  simp

/-! ### Toggling (the duplicate-cancelling set of `xor_to_virtual`) -/

theorem xorL_append (a b : List Bool) : xorL (a ++ b) = (xorL a != xorL b) := by
  induction a with
  | nil => rw [List.nil_append, xorL_nil]; cases xorL b <;> rfl
  | cons x t ih =>
    rw [List.cons_append, xorL_cons, xorL_cons, ih]
    cases x <;> cases xorL t <;> cases xorL b <;> rfl

theorem xorL_perm {l1 l2 : List Bool} (h : l1.Perm l2) : xorL l1 = xorL l2 := by
  induction h with
  | nil => rfl
  | cons x _ ih => rw [xorL_cons, xorL_cons, ih]
  | swap x y l =>
    rw [xorL_cons, xorL_cons, xorL_cons, xorL_cons]
    cases x <;> cases y <;> cases xorL l <;> rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem toggle_aux (f : Wire → Bool) : ∀ (l acc : List Wire),
    xorL ((l.foldl (fun acc x => if acc.contains x then acc.erase x else acc ++ [x]) acc).map f) =
      (xorL (acc.map f) != xorL (l.map f)) := by
  intro l
  induction l with
  | nil => intro acc; simp only [List.foldl_nil, List.map_nil, xorL_nil]; cases xorL (acc.map f) <;> rfl
  | cons x t ih =>
    intro acc
    simp only [List.foldl_cons, List.map_cons, xorL_cons]
    by_cases hc : acc.contains x = true
    · have hx : x ∈ acc := by simpa using hc
      simp only [hc, ↓reduceIte]
      rw [ih]
      have hp := xorL_perm (List.Perm.map f (List.perm_cons_erase hx))
      rw [List.map_cons, xorL_cons] at hp
      rw [hp]
      cases f x <;> cases xorL ((acc.erase x).map f) <;> cases xorL (t.map f) <;> rfl
    · have hc' : acc.contains x = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte]
      rw [ih, List.map_append, xorL_append, List.map_cons, List.map_nil, xorL_single]
      cases f x <;> cases xorL (acc.map f) <;> cases xorL (t.map f) <;> rfl

theorem toggle_xor (f : Wire → Bool) (l : List Wire) : xorL ((toggle l).map f) = xorL (l.map f) := by
  unfold toggle
  rw [toggle_aux]
  simp [xorL_nil]

theorem mem_toggle_sub (l : List Wire) : ∀ x ∈ toggle l, x ∈ l := by
  have key : ∀ (l acc : List Wire), ∀ x ∈ l.foldl (fun acc x => if acc.contains x then acc.erase x else acc ++ [x]) acc,
      x ∈ acc ∨ x ∈ l := by
    intro l
    induction l with
    | nil => intro acc x hx; exact Or.inl (by simpa using hx)
    | cons y t ih =>
      intro acc x hx
      simp only [List.foldl_cons] at hx
      by_cases hc : acc.contains y = true
      · rw [if_pos hc] at hx
        rcases ih _ x hx with h | h
        · exact Or.inl (List.mem_of_mem_erase h)
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rw [if_neg hc] at hx
        rcases ih _ x hx with h | h
        · rcases List.mem_append.1 h with h | h
          · exact Or.inl h
          · exact Or.inr (by rw [List.mem_singleton.1 h]; exact List.mem_cons_self)
        · exact Or.inr (List.mem_cons_of_mem _ h)
  intro x hx
  rcases key l [] x hx with h | h
  · simp at h
  · exact h

/-! ### Gadgets -/

section Gadgets

variable {gb : GB} {inp : Nat → Bool} {k : Nat}

theorem notV_post (hinp : ∀ i, k ≤ i → inp i = false) (hk : k ≤ gb.n) (hr : Reach gb) {w : Wire} (hw : w.ok gb.n) :
    Post gb (notV gb w).2 inp (notV gb w).1 (!wev gb inp w) := by
  cases w with
  | cst b => exact ⟨Ext.refl _, hr, trivial, by simp [notV, wev, Wire.ev]⟩
  | nd i =>
    have h := add_post hinp hk hr .addneg [i] (by simp [Simple]) (by intro u hu; simp at hu; subst hu; exact hw)
    show Post gb (gb.add .addneg [i]).2 inp (gb.add .addneg [i]).1 (!wev gb inp (.nd i))
    refine ⟨h.ext, h.reach, h.ok, ?_⟩
    rw [h.val]
    simp only [List.map_cons, List.map_nil, nodeVal_addneg, xorL_single]

theorem andV_post (hinp : ∀ i, k ≤ i → inp i = false) (hk : k ≤ gb.n) (hr : Reach gb) (ws : List Wire)
    (hok : ∀ w ∈ ws, w.ok gb.n) :
    Post gb (andV gb ws).2 inp (andV gb ws).1 (andL (ws.map (wev gb inp))) := by
  unfold andV
  by_cases h1 : ws.all Wire.isc = true
  · rw [if_pos h1]
    refine ⟨Ext.refl _, hr, trivial, ?_⟩
    have hc : ∀ w ∈ ws, wev gb inp w = (w == .cst true) := fun w hw => wev_cst gb inp (List.all_eq_true.1 h1 w hw)
    show (ws.all fun w => w == .cst true) = _
    apply Bool.eq_iff_iff.2
    rw [andL_map_iff, List.all_eq_true]
    constructor
    · intro h w hw; rw [hc w hw]; exact h w hw
    · intro h w hw; rw [← hc w hw]; exact h w hw
  · rw [if_neg h1]
    by_cases h2 : (ws.any fun w => w == .cst false) = true
    · rw [if_pos h2]
      refine ⟨Ext.refl _, hr, trivial, ?_⟩
      obtain ⟨w, hw, hwf⟩ := List.any_eq_true.1 h2
      have hw' : w = .cst false := by simpa using hwf
      show false = _
      symm
      cases hh : andL (ws.map (wev gb inp))
      · rfl
      · have := (andL_map_iff _ _).1 hh w hw
        rw [hw'] at this
        simp [wev, Wire.ev] at this
    · rw [if_neg h2]
      have hconst : ∀ w ∈ ws, w.isc = true → wev gb inp w = true := by
        intro w hw hc
        rw [wev_cst gb inp hc]
        cases w with
        | cst b =>
          cases b
          · exact absurd (List.any_eq_true.2 ⟨_, hw, by simp⟩) h2
          · simp
        | nd i => simp [Wire.isc] at hc
      have hmem : ∀ x, x ∈ dedupW (ws.filter fun w => !w.isc) ↔ x ∈ ws ∧ x.isc = false := by
        intro x
        rw [mem_dedupW, List.mem_filter]
        simp
      have hval : andL ((dedupW (ws.filter fun w => !w.isc)).map (wev gb inp)) = andL (ws.map (wev gb inp)) := by
        apply Bool.eq_iff_iff.2
        rw [andL_map_iff, andL_map_iff]
        constructor
        · intro h w hw
          by_cases hc : w.isc = true
          · exact hconst w hw hc
          · exact h w ((hmem w).2 ⟨hw, by simpa using hc⟩)
        · intro h x hx
          exact h x ((hmem x).1 hx).1
      have hne : ∃ w ∈ ws, w.isc = false := by
        apply Classical.byContradiction
        intro hno
        apply h1
        apply List.all_eq_true.2
        intro w hw
        apply Classical.byContradiction
        intro hc
        exact hno ⟨w, hw, by simpa using hc⟩
      generalize dedupW (ws.filter fun w => !w.isc) = nums at hmem hval ⊢
      rcases nums with _ | ⟨w, _ | ⟨w2, rest⟩⟩
      · obtain ⟨w, hw, hc⟩ := hne
        have := (hmem w).2 ⟨hw, hc⟩
        simp at this
      · have hw := (hmem w).1 (by simp)
        refine ⟨Ext.refl _, hr, hok w hw.1, ?_⟩
        rw [← hval]
        simp [andL_single]
      · have hn : ∀ x ∈ w :: w2 :: rest, x.isc = false := fun x hx => ((hmem x).1 hx).2
        have hokn : ∀ u ∈ ((w :: w2 :: rest).map Wire.idx), u < gb.n := by
          intro u hu
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu
          have := hok x ((hmem x).1 hx).1
          have h3 := hn x hx
          cases x with
          | cst b => simp [Wire.isc] at h3
          | nd i => exact this
        have h := add_post hinp hk hr .flow _ (by simp [Simple]) hokn
        refine ⟨h.ext, h.reach, h.ok, ?_⟩
        show wev _ inp (gb.add .flow _).1 = _
        rw [h.val, map_idx_ev gb inp _ hn, nodeVal_flow _ (by simp), hval]

theorem orV_post (hinp : ∀ i, k ≤ i → inp i = false) (hk : k ≤ gb.n) (hr : Reach gb) (ws : List Wire)
    (hok : ∀ w ∈ ws, w.ok gb.n) :
    Post gb (orV gb ws).2 inp (orV gb ws).1 (orL (ws.map (wev gb inp))) := by
  unfold orV
  by_cases h1 : ws.all Wire.isc = true
  · rw [if_pos h1]
    refine ⟨Ext.refl _, hr, trivial, ?_⟩
    have hc : ∀ w ∈ ws, wev gb inp w = (w == .cst true) := fun w hw => wev_cst gb inp (List.all_eq_true.1 h1 w hw)
    show (ws.any fun w => w == .cst true) = _
    apply Bool.eq_iff_iff.2
    rw [orL_map_iff, List.any_eq_true]
    constructor
    · rintro ⟨w, hw, h⟩; exact ⟨w, hw, by rw [hc w hw]; exact h⟩
    · rintro ⟨w, hw, h⟩; exact ⟨w, hw, by rw [← hc w hw]; exact h⟩
  · rw [if_neg h1]
    by_cases h2 : (ws.any fun w => w == .cst true) = true
    · rw [if_pos h2]
      refine ⟨Ext.refl _, hr, trivial, ?_⟩
      obtain ⟨w, hw, hwf⟩ := List.any_eq_true.1 h2
      have hw' : w = .cst true := by simpa using hwf
      show true = _
      symm
      apply (orL_map_iff _ _).2
      exact ⟨w, hw, by rw [hw']; simp [wev, Wire.ev]⟩
    · rw [if_neg h2]
      have hconst : ∀ w ∈ ws, w.isc = true → wev gb inp w = false := by
        intro w hw hc
        rw [wev_cst gb inp hc]
        cases w with
        | cst b =>
          cases b
          · simp
          · exact absurd (List.any_eq_true.2 ⟨_, hw, by simp⟩) h2
        | nd i => simp [Wire.isc] at hc
      have hmem : ∀ x, x ∈ dedupW (ws.filter fun w => !w.isc) ↔ x ∈ ws ∧ x.isc = false := by
        intro x
        rw [mem_dedupW, List.mem_filter]
        simp
      have hval : orL ((dedupW (ws.filter fun w => !w.isc)).map (wev gb inp)) = orL (ws.map (wev gb inp)) := by
        apply Bool.eq_iff_iff.2
        rw [orL_map_iff, orL_map_iff]
        constructor
        · rintro ⟨x, hx, h⟩
          exact ⟨x, ((hmem x).1 hx).1, h⟩
        · rintro ⟨w, hw, h⟩
          by_cases hc : w.isc = true
          · rw [hconst w hw hc] at h; exact absurd h (by simp)
          · exact ⟨w, (hmem w).2 ⟨hw, by simpa using hc⟩, h⟩
      have hne : ∃ w ∈ ws, w.isc = false := by
        apply Classical.byContradiction
        intro hno
        apply h1
        apply List.all_eq_true.2
        intro w hw
        apply Classical.byContradiction
        intro hc
        exact hno ⟨w, hw, by simpa using hc⟩
      generalize dedupW (ws.filter fun w => !w.isc) = nums at hmem hval ⊢
      rcases nums with _ | ⟨w, _ | ⟨w2, rest⟩⟩
      · obtain ⟨w, hw, hc⟩ := hne
        have := (hmem w).2 ⟨hw, hc⟩
        simp at this
      · have hw := (hmem w).1 (by simp)
        refine ⟨Ext.refl _, hr, hok w hw.1, ?_⟩
        rw [← hval]
        simp [orL_single]
      · have hn : ∀ x ∈ w :: w2 :: rest, x.isc = false := fun x hx => ((hmem x).1 hx).2
        have hokn : ∀ u ∈ ((w :: w2 :: rest).map Wire.idx), u < gb.n := by
          intro u hu
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu
          have := hok x ((hmem x).1 hx).1
          have h3 := hn x hx
          cases x with
          | cst b => simp [Wire.isc] at h3
          | nd i => exact this
        have h := add_post hinp hk hr .any _ (by simp [Simple]) hokn
        refine ⟨h.ext, h.reach, h.ok, ?_⟩
        show wev _ inp (gb.add .any _).1 = _
        rw [h.val, map_idx_ev gb inp _ hn, nodeVal_any _ (by simp), hval]

theorem xor_split (f : Wire → Bool) (hf : ∀ w, w.isc = true → f w = (w == .cst true)) : ∀ ws : List Wire,
    xorL (ws.map f) = (((ws.filter fun w => w == .cst true).length % 2 == 1) !=
      xorL ((ws.filter fun w => !w.isc).map f)) := by
  intro ws
  induction ws with
  | nil => rfl
  | cons w t ih =>
    rw [List.map_cons, xorL_cons, ih]
    generalize hX : xorL ((t.filter fun w => !w.isc).map f) = X
    generalize hN : (t.filter fun w => w == .cst true).length = N
    cases w with
    | nd i =>
      have e1 : ((Wire.nd i == Wire.cst true)) = false := by simp
      have e2 : (!(Wire.nd i).isc) = true := by simp [Wire.isc]
      simp only [List.filter_cons, e1, e2, Bool.false_eq_true, ↓reduceIte, List.map_cons, xorL_cons, hX, hN]
      cases f (.nd i) <;> cases (N % 2 == 1) <;> cases X <;> rfl
    | cst b =>
      have e2 : (!(Wire.cst b).isc) = false := by simp [Wire.isc]
      have hfb := hf (.cst b) rfl
      cases b
      · have e1 : (Wire.cst false == Wire.cst true) = false := by simp
        simp only [List.filter_cons, e1, e2, Bool.false_eq_true, ↓reduceIte, hX, hN]
        rw [hfb, e1]
        cases (N % 2 == 1) <;> cases X <;> rfl
      · have e1 : (Wire.cst true == Wire.cst true) = true := by simp
        simp only [List.filter_cons, e1, e2, Bool.false_eq_true, ↓reduceIte, hX, hN, List.length_cons]
        rw [hfb, e1]
        have hp : (((N + 1) % 2 == 1)) = !(N % 2 == 1) := by
          by_cases hh : N % 2 = 1
          · have : (N + 1) % 2 = 0 := by omega
            simp [hh, this]
          · have : (N + 1) % 2 = 1 := by omega
            simp [hh, this]
        rw [hp]
        cases (N % 2 == 1) <;> cases X <;> rfl

theorem xorV_post (hinp : ∀ i, k ≤ i → inp i = false) (hk : k ≤ gb.n) (hr : Reach gb) (ws : List Wire)
    (hok : ∀ w ∈ ws, w.ok gb.n) :
    Post gb (xorV gb ws).2 inp (xorV gb ws).1 (xorL (ws.map (wev gb inp))) := by
  have hsplit := xor_split (wev gb inp) (fun w hw => wev_cst gb inp hw) ws
  unfold xorV
  dsimp only
  by_cases h1 : ws.all Wire.isc = true
  · rw [if_pos h1]
    refine ⟨Ext.refl _, hr, trivial, ?_⟩
    have hnil : (ws.filter fun w => !w.isc) = [] :=
      List.filter_eq_nil_iff.2 (fun w hw => by simp [List.all_eq_true.1 h1 w hw])
    rw [hsplit, hnil]
    simp [wev, Wire.ev, xorL_nil]
  · rw [if_neg h1]
    have hval := toggle_xor (wev gb inp) (ws.filter fun w => !w.isc)
    have hmem : ∀ x ∈ toggle (ws.filter fun w => !w.isc), x ∈ ws ∧ x.isc = false := by
      intro x hx
      have := mem_toggle_sub _ x hx
      rw [List.mem_filter] at this
      simpa using this
    generalize toggle (ws.filter fun w => !w.isc) = T at hval hmem ⊢
    generalize ((ws.filter fun w => w == .cst true).length % 2 == 1) = fl at hsplit ⊢
    rw [hsplit, ← hval]
    rcases T with _ | ⟨w, _ | ⟨w2, rest⟩⟩
    · refine ⟨Ext.refl _, hr, trivial, ?_⟩
      simp [wev, Wire.ev, xorL_nil]
    · have hw := hmem w (by simp)
      have hwo := hok w hw.1
      cases fl
      · refine ⟨Ext.refl _, hr, hwo, ?_⟩
        simp [xorL_single]
      · have h := notV_post hinp hk hr hwo
        show Post gb (notV gb w).2 inp (notV gb w).1 _
        refine ⟨h.ext, h.reach, h.ok, ?_⟩
        rw [h.val]
        simp [xorL_single]
    · have hn : ∀ x ∈ w :: w2 :: rest, x.isc = false := fun x hx => (hmem x hx).2
      have hokn : ∀ u ∈ ((w :: w2 :: rest).map Wire.idx), u < gb.n := by
        intro u hu
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu
        have := hok x (hmem x hx).1
        have h3 := hn x hx
        cases x with
        | cst b => simp [Wire.isc] at h3
        | nd i => exact this
      cases fl
      · have h := add_post hinp hk hr .add _ (by simp [Simple]) hokn
        show Post gb (gb.add .add _).2 inp (gb.add .add _).1 _
        refine ⟨h.ext, h.reach, h.ok, ?_⟩
        rw [h.val, map_idx_ev gb inp _ hn, nodeVal_add]
        cases xorL ((w :: w2 :: rest).map (wev gb inp)) <;> rfl
      · have h := add_post hinp hk hr .addneg _ (by simp [Simple]) hokn
        show Post gb (gb.add .addneg _).2 inp (gb.add .addneg _).1 _
        refine ⟨h.ext, h.reach, h.ok, ?_⟩
        rw [h.val, map_idx_ev gb inp _ hn, nodeVal_addneg]
        cases xorL ((w :: w2 :: rest).map (wev gb inp)) <;> rfl

end Gadgets

end SmcIrred
