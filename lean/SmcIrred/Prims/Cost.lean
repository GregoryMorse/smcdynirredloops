module

public import SmcIrred.Prims.Decoder

public section

namespace SmcIrred

theorem add_n (gb : GB) (k : Kind) (ps : List Nat) : (gb.add k ps).2.n = gb.n + 1 := by
  simp [GB.add, GB.n]

theorem add_e (gb : GB) (k : Kind) (ps : List Nat) : (gb.add k ps).2.e = gb.e + ps.length := by
  simp [GB.add, GB.e]

theorem add_fst (gb : GB) (k : Kind) (ps : List Nat) : (gb.add k ps).1 = Wire.nd gb.n := rfl

theorem notV_nd (gb : GB) (j : Nat) :
    (notV gb (.nd j)).2.n = gb.n + 1 ∧ (notV gb (.nd j)).2.e = gb.e + 1 ∧ (notV gb (.nd j)).1 = .nd gb.n :=
  ⟨add_n _ _ _, by rw [show notV gb (.nd j) = gb.add .addneg [j] from rfl, add_e]; rfl, rfl⟩

theorem andV_two (gb : GB) {w1 w2 : Wire} (h1 : w1.isc = false) (h2 : w2.isc = false) (hne : w1 ≠ w2) :
    (andV gb [w1, w2]).2.n = gb.n + 1 ∧ (andV gb [w1, w2]).2.e = gb.e + 2 ∧ (andV gb [w1, w2]).1 = .nd gb.n := by
  cases w1 with
  | cst b => simp [Wire.isc] at h1
  | nd i =>
    cases w2 with
    | cst b => simp [Wire.isc] at h2
    | nd j =>
      have hij : i ≠ j := fun e => hne (by rw [e])
      have hd : dedupW [Wire.nd i, Wire.nd j] = [Wire.nd i, Wire.nd j] :=
        dedupW_id _ (by simp [hij])
      have e : andV gb [Wire.nd i, Wire.nd j] = gb.add .flow [i, j] := by
        simp [andV, Wire.isc, Wire.idx, hd]
      rw [e]
      exact ⟨add_n _ _ _, by rw [add_e]; rfl, rfl⟩

theorem andV_true_left (gb : GB) {w : Wire} (h : w.isc = false) : andV gb [.cst true, w] = (w, gb) := by
  cases w with
  | cst b => simp [Wire.isc] at h
  | nd i => simp [andV, dedupW, Wire.isc]

theorem orV_many (gb : GB) (ws : List Wire) (hnc : ∀ w ∈ ws, w.isc = false) (hnd : ws.Nodup) (h2 : 2 ≤ ws.length) :
    (orV gb ws).2.n = gb.n + 1 ∧ (orV gb ws).2.e = gb.e + ws.length ∧ (orV gb ws).1 = .nd gb.n := by
  have hall : ws.all Wire.isc = false := by
    cases ws with
    | nil => simp at h2
    | cons w t => simp [List.all_cons, hnc w List.mem_cons_self]
  have hany : (ws.any fun w => w == .cst true) = false := by
    apply Bool.eq_false_iff.2
    intro h
    obtain ⟨w, hw, hh⟩ := List.any_eq_true.1 h
    have h3 := hnc w hw
    have : w = .cst true := by simpa using hh
    subst this
    simp [Wire.isc] at h3
  have hfilt : (ws.filter fun w => !w.isc) = ws := List.filter_eq_self.2 (fun w hw => by simp [hnc w hw])
  have e : orV gb ws = gb.add .any (ws.map Wire.idx) := by
    rcases ws with _ | ⟨w, _ | ⟨w2, rest⟩⟩
    · simp at h2
    · simp at h2
    · unfold orV
      rw [hall, hany, hfilt, dedupW_id _ hnd]
      simp
  rw [e]
  exact ⟨add_n _ _ _, by rw [add_e]; simp, rfl⟩

theorem orV_one (gb : GB) {w : Wire} (h : w.isc = false) : orV gb [w] = (w, gb) := by
  cases w with
  | cst b => simp [Wire.isc] at h
  | nd i => simp [orV, dedupW, Wire.isc]

theorem xorV_false_nd (gb : GB) (j : Nat) : xorV gb [.cst false, .nd j] = (.nd j, gb) := by
  simp [xorV, toggle, Wire.isc]

theorem xorV_true_nd (gb : GB) (j : Nat) : xorV gb [.cst true, .nd j] = notV gb (.nd j) := by
  simp [xorV, toggle, Wire.isc]

/-- Cost bookkeeping for threading a gadget through a list. -/
theorem mapG_cost {α : Type} (f : GB → α → Wire × GB) (c ce : α → Nat) (P : α → Prop) (Q : GB → Prop)
    (hQ : ∀ gb gb' : GB, gb.n ≤ gb'.n → Q gb → Q gb')
    (hf : ∀ (gb : GB) (a : α), P a → Q gb → (f gb a).2.n = gb.n + c a ∧ (f gb a).2.e = gb.e + ce a) :
    ∀ (l : List α) (gb : GB), (∀ a ∈ l, P a) → Q gb →
      (mapG f gb l).2.n = gb.n + (l.map c).sum ∧ (mapG f gb l).2.e = gb.e + (l.map ce).sum := by
  intro l
  induction l with
  | nil => intro gb _ _; simp [mapG]
  | cons a l ih =>
    intro gb hP hq
    have hm : mapG f gb (a :: l) = ((f gb a).1 :: (mapG f (f gb a).2 l).1, (mapG f (f gb a).2 l).2) := rfl
    rw [hm]
    obtain ⟨h1, h2⟩ := hf gb a (hP a List.mem_cons_self) hq
    have hq' : Q (f gb a).2 := hQ gb _ (by omega) hq
    obtain ⟨i1, i2⟩ := ih (f gb a).2 (fun a' ha' => hP a' (List.mem_cons_of_mem _ ha')) hq'
    show (mapG f (f gb a).2 l).2.n = _ ∧ (mapG f (f gb a).2 l).2.e = _
    rw [i1, i2, h1, h2]
    simp only [List.map_cons, List.sum_cons]
    omega

end SmcIrred
