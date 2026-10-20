module

public import SmcIrred.RSA.Mont
public import SmcIrred.Arith.Window

public section

namespace SmcIrred

open RSA

/-! # The compiled RSA graph (R15, G30)

The products of the program are compiled one by one (`mmulG`); the wires of a product are shared by everything that reads
them. `Rel gb W x` says that the wires `W` exist in the state and carry the number `x`. The table, the window loop and the
squarings of `winExpG` are related step by step to the pure schedule `Arith.winExp` instantiated with the Montgomery product,
and the whole graph to `Arith.modexpMontWin`. -/

section
variable {inp : Nat → Bool} {k : Nat}

/-- The wires exist in the state and carry the number `x`. -/
@[expose] def Rel (inp : Nat → Bool) (gb : GB) (W : List Wire) (x : Nat) : Prop :=
  (∀ w ∈ W, w.ok gb.n) ∧ bv (W.map (wev gb inp)) = x

theorem Rel.mono {gb gb' : GB} (e : Ext gb gb') {W : List Wire} {x : Nat} (h : Rel inp gb W x) : Rel inp gb' W x := by
  refine ⟨fun w hw => ok_mono (h.1 w hw) e.n_le, ?_⟩
  rw [← h.2]
  congr 1
  exact List.map_congr_left (fun w hw => wev_ext e (h.1 w hw))

/-- The generator state is usable: reachable by simple nodes, past the input nodes. -/
@[expose] def WI (k : Nat) (gb : GB) : Prop := Reach gb ∧ k ≤ gb.n

theorem WI.mono {gb gb' : GB} (e : Ext gb gb') (h : WI k gb) (hr : Reach gb') : WI k gb' := ⟨hr, Nat.le_trans h.2 e.n_le⟩

theorem ok_mulE {n : Nat} {a b : BvExp} (ha : a.ok n) (hb : b.ok n) : (mulE a b).ok n := by
  unfold mulE
  have : ∀ (l : List Nat) (acc : BvExp), acc.ok n →
      ((l.foldl (fun acc i => BvExp.add acc (BvExp.ite (BvExp.slice b i 1) (shiftE a i) zeroE)) acc).ok n) := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons i t ih =>
      intro acc h
      apply ih
      refine ⟨h, hb, ⟨?_, ha⟩, ?_⟩
      · intro w hw
        simp only [List.mem_replicate] at hw
        rw [hw.2]; trivial
      · intro w hw; simp [zeroE] at hw
  exact this _ _ (by intro w hw; simp [zeroE] at hw)

theorem ok_litW (n w m : Nat) : (litW n w).ok m := by
  intro w' hw
  simp only [litW, List.mem_map] at hw
  obtain ⟨j, _, rfl⟩ := hw
  trivial

theorem ok_boundE {n : Nat} {t N : BvExp} (ht : t.ok n) (hN : N.ok n) : (boundE t N).ok n := by
  have hd : (boundD t N).ok n := by
    refine ⟨⟨ht, ?_⟩, ⟨hN, ?_⟩⟩ <;> (intro w hw; simp at hw; rw [hw]; trivial)
  exact ⟨hd, ht, hd⟩

theorem ok_redcE {n : Nat} (B N Np : Nat) {T : BvExp} (hT : T.ok n) : (redcE B N Np T).ok n := by
  have hm : (redcM B Np T).ok n := ok_mulE (a := .slice T 0 B) hT (ok_litW _ _ _)
  have hs : (redcS B N Np T).ok n := ⟨hT, ok_mulE hm (ok_litW _ _ _)⟩
  exact ok_boundE hs (ok_litW _ _ _)

/-- One Montgomery product on wires: new wires carrying `redc (x * y)`. -/
theorem mmulG_rel (hinp : ∀ i, k ≤ i → inp i = false) (B N Np : Nat) (hN : N < 2 ^ B) (hNp : Np < 2 ^ B) {gb : GB}
    (h : WI k gb) {x y : List Wire} {X Y : Nat} (hx : Rel inp gb x X) (hy : Rel inp gb y Y) :
    Ext gb (mmulG B N Np gb x y).2 ∧ WI k (mmulG B N Np gb x y).2 ∧
      Rel inp (mmulG B N Np gb x y).2 (mmulG B N Np gb x y).1 (Arith.redc B N Np (X * Y)) := by
  have hok : (redcE B N Np (mulE (.inp x) (.inp y))).ok gb.n :=
    ok_redcE B N Np (ok_mulE (fun w hw => (Wire.inb_iff _ _).2 (hx.1 w hw)) (fun w hw => (Wire.inb_iff _ _).2 (hy.1 w hw)))
  obtain ⟨e1, r1, o1, v1⟩ := comp_correct hinp _ gb h.2 h.1 hok
  refine ⟨e1, ⟨r1, Nat.le_trans h.2 e1.n_le⟩, o1, ?_⟩
  unfold mmulG
  rw [v1, val_redcE _ (fun _ => rfl) B N Np hN hNp, val_mulE _ (fun _ => rfl)]
  simp only [BvExp.sem]
  rw [hx.2, hy.2]

/-! ### The table of powers -/

/-- The table of wires carries the table of numbers (same length, same entries; the default entry is the one). -/
@[expose] def TRel (inp : Nat → Bool) (gb : GB) (oneW : List Wire) (oneV : Nat) (TW : List (List Wire))
    (TV : List Nat) : Prop :=
  TW.length = TV.length ∧ ∀ i, Rel inp gb (TW.getD i oneW) (TV.getD i oneV)

theorem TRel.mono {gb gb' : GB} (e : Ext gb gb') {oneW : List Wire} {oneV : Nat} {TW : List (List Wire)} {TV : List Nat}
    (h : TRel inp gb oneW oneV TW TV) : TRel inp gb' oneW oneV TW TV :=
  ⟨h.1, fun i => (h.2 i).mono e⟩

theorem getD_append_gt {α : Type} (t : List α) (x d : α) {j : Nat} (h : t.length < j) : (t ++ [x]).getD j d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  obtain ⟨d', hd'⟩ : ∃ d', j - t.length = d' + 1 := ⟨j - t.length - 1, by omega⟩
  rw [hd']
  simp

theorem TRel.append {gb : GB} {oneW : List Wire} {oneV : Nat} {TW : List (List Wire)} {TV : List Nat}
    (h : TRel inp gb oneW oneV TW TV) (hone : Rel inp gb oneW oneV) {r : List Wire} {x : Nat} (hr : Rel inp gb r x) :
    TRel inp gb oneW oneV (TW ++ [r]) (TV ++ [x]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i
  by_cases h1 : i < TW.length
  · rw [Arith.getD_append_lt TW r oneW h1, Arith.getD_append_lt TV x oneV (by rw [← h.1]; exact h1)]
    exact h.2 i
  · by_cases h2 : i = TW.length
    · subst h2
      rw [Arith.getD_append_len, h.1, Arith.getD_append_len]
      exact hr
    · have hl := h.1
      rw [getD_append_gt TW r oneW (by omega), getD_append_gt TV x oneV (by omega)]
      exact hone

theorem tblInit_rel {gb : GB} {oneW b : List Wire} {oneV bV : Nat} (hone : Rel inp gb oneW oneV) (hb : Rel inp gb b bV) :
    TRel inp gb oneW oneV [oneW, b] [oneV, bV] := by
  refine ⟨rfl, ?_⟩
  intro i
  match i with
  | 0 => exact hone
  | 1 => exact hb
  | i + 2 => simpa using hone

theorem tblStep_rel (hinp : ∀ i, k ≤ i → inp i = false) (B N Np : Nat) (hN : N < 2 ^ B) (hNp : Np < 2 ^ B)
    {oneW b : List Wire} {oneV bV : Nat} (k' : Nat) (st : List (List Wire) × GB) (TV : List Nat)
    (h : WI k st.2) (hone : Rel inp st.2 oneW oneV) (hb : Rel inp st.2 b bV) (ht : TRel inp st.2 oneW oneV st.1 TV) :
    Ext st.2 (tblStepG B N Np oneW b st k').2 ∧ WI k (tblStepG B N Np oneW b st k').2 ∧
      Rel inp (tblStepG B N Np oneW b st k').2 oneW oneV ∧ Rel inp (tblStepG B N Np oneW b st k').2 b bV ∧
      TRel inp (tblStepG B N Np oneW b st k').2 oneW oneV (tblStepG B N Np oneW b st k').1
        (Arith.tblStep (fun x y => Arith.redc B N Np (x * y)) oneV bV TV k') := by
  unfold tblStepG Arith.tblStep
  dsimp only
  by_cases hk : (k' + 2) % 2 = 0
  · simp only [hk, ↓reduceIte]
    obtain ⟨e1, w1, r1⟩ := mmulG_rel hinp B N Np hN hNp h (ht.2 ((k' + 2) / 2)) (ht.2 ((k' + 2) / 2))
    exact ⟨e1, w1, hone.mono e1, hb.mono e1, (ht.mono e1).append (hone.mono e1) r1⟩
  · simp only [hk, ↓reduceIte]
    obtain ⟨e1, w1, r1⟩ := mmulG_rel hinp B N Np hN hNp h (ht.2 (k' + 2 - 1)) hb
    exact ⟨e1, w1, hone.mono e1, hb.mono e1, (ht.mono e1).append (hone.mono e1) r1⟩

theorem winTbl_rel (hinp : ∀ i, k ≤ i → inp i = false) (B N Np : Nat) (hN : N < 2 ^ B) (hNp : Np < 2 ^ B)
    {oneW b : List Wire} {oneV bV : Nat} :
    ∀ (n : Nat) (st : List (List Wire) × GB) (TV : List Nat), WI k st.2 → Rel inp st.2 oneW oneV →
      Rel inp st.2 b bV → TRel inp st.2 oneW oneV st.1 TV →
      Ext st.2 ((List.range n).foldl (tblStepG B N Np oneW b) st).2 ∧
        WI k ((List.range n).foldl (tblStepG B N Np oneW b) st).2 ∧
        Rel inp ((List.range n).foldl (tblStepG B N Np oneW b) st).2 oneW oneV ∧
        Rel inp ((List.range n).foldl (tblStepG B N Np oneW b) st).2 b bV ∧
        TRel inp ((List.range n).foldl (tblStepG B N Np oneW b) st).2 oneW oneV
          ((List.range n).foldl (tblStepG B N Np oneW b) st).1
          ((List.range n).foldl (Arith.tblStep (fun x y => Arith.redc B N Np (x * y)) oneV bV) TV) := by
  intro n
  induction n with
  | zero => intro st TV h h1 h2 h3; exact ⟨Ext.refl _, h, h1, h2, h3⟩
  | succ n ih =>
    intro st TV h h1 h2 h3
    obtain ⟨e1, w1, o1, b1, t1⟩ := ih st TV h h1 h2 h3
    obtain ⟨e2, w2, o2, b2, t2⟩ := tblStep_rel hinp B N Np hN hNp n _ _ w1 o1 b1 t1
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil,
      List.foldl_nil]
    exact ⟨e1.trans e2, w2, o2, b2, t2⟩

/-! ### The squarings, the window loop and the whole exponentiation -/

theorem sqLoop_rel (hinp : ∀ i, k ≤ i → inp i = false) (B N Np : Nat) (hN : N < 2 ^ B) (hNp : Np < 2 ^ B) :
    ∀ (n : Nat) (st : List Wire × GB) (X : Nat), WI k st.2 → Rel inp st.2 st.1 X →
      Ext st.2 ((List.range n).foldl (fun (s : List Wire × GB) _ => mmulG B N Np s.2 s.1 s.1) st).2 ∧
        WI k ((List.range n).foldl (fun (s : List Wire × GB) _ => mmulG B N Np s.2 s.1 s.1) st).2 ∧
        Rel inp ((List.range n).foldl (fun (s : List Wire × GB) _ => mmulG B N Np s.2 s.1 s.1) st).2
          ((List.range n).foldl (fun (s : List Wire × GB) _ => mmulG B N Np s.2 s.1 s.1) st).1
          ((List.range n).foldl (fun r _ => Arith.redc B N Np (r * r)) X) := by
  intro n
  induction n with
  | zero => intro st X h hx; exact ⟨Ext.refl _, h, hx⟩
  | succ n ih =>
    intro st X h hx
    obtain ⟨e1, w1, r1⟩ := ih st X h hx
    obtain ⟨e2, w2, r2⟩ := mmulG_rel hinp B N Np hN hNp w1 r1 r1
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil,
      List.foldl_nil]
    exact ⟨e1.trans e2, w2, r2⟩

/-- The pure window step of `Arith.winExp` with the Montgomery product. -/
@[expose] def winStepV (mulN : Nat → Nat → Nat) (T : List Nat) (one w e : Nat) (res j : Nat) : Nat :=
  let res := mulN (T.getD ((e >>> (j * w)) &&& (2 ^ w - 1)) one) res
  if j = 0 then res else (List.range w).foldl (fun r _ => mulN r r) res

theorem winStep_rel (hinp : ∀ i, k ≤ i → inp i = false) (B N Np : Nat) (hN : N < 2 ^ B) (hNp : Np < 2 ^ B)
    {oneW : List Wire} {oneV : Nat} {TW : List (List Wire)} {TV : List Nat} (w e : Nat) (st : List Wire × GB)
    (resV j : Nat) (h : WI k st.2) (hone : Rel inp st.2 oneW oneV) (ht : TRel inp st.2 oneW oneV TW TV)
    (hres : Rel inp st.2 st.1 resV) :
    Ext st.2 (winStepG B N Np oneW TW w e st j).2 ∧ WI k (winStepG B N Np oneW TW w e st j).2 ∧
      Rel inp (winStepG B N Np oneW TW w e st j).2 oneW oneV ∧
      TRel inp (winStepG B N Np oneW TW w e st j).2 oneW oneV TW TV ∧
      Rel inp (winStepG B N Np oneW TW w e st j).2 (winStepG B N Np oneW TW w e st j).1
        (winStepV (fun x y => Arith.redc B N Np (x * y)) TV oneV w e resV j) := by
  unfold winStepG winStepV sqLoopG
  dsimp only
  have hm := mmulG_rel hinp B N Np hN hNp h (ht.2 ((e >>> (j * w)) &&& (2 ^ w - 1))) hres
  generalize mmulG B N Np st.2 (TW.getD ((e >>> (j * w)) &&& (2 ^ w - 1)) oneW) st.1 = m at hm ⊢
  obtain ⟨e1, w1, r1⟩ := hm
  by_cases hj : j = 0
  · subst hj
    simp only [↓reduceIte]
    exact ⟨e1, w1, hone.mono e1, ht.mono e1, r1⟩
  · simp only [hj, ↓reduceIte]
    obtain ⟨e2, w2, r2⟩ := sqLoop_rel hinp B N Np hN hNp w m _ w1 r1
    exact ⟨e1.trans e2, w2, (hone.mono e1).mono e2, (ht.mono e1).mono e2, r2⟩

theorem winLoop_rel (hinp : ∀ i, k ≤ i → inp i = false) (B N Np : Nat) (hN : N < 2 ^ B) (hNp : Np < 2 ^ B)
    {oneW : List Wire} {oneV : Nat} {TW : List (List Wire)} {TV : List Nat} (w e : Nat) :
    ∀ (L : List Nat) (st : List Wire × GB) (resV : Nat), WI k st.2 → Rel inp st.2 oneW oneV →
      TRel inp st.2 oneW oneV TW TV → Rel inp st.2 st.1 resV →
      Ext st.2 (L.foldl (winStepG B N Np oneW TW w e) st).2 ∧ WI k (L.foldl (winStepG B N Np oneW TW w e) st).2 ∧
        Rel inp (L.foldl (winStepG B N Np oneW TW w e) st).2 (L.foldl (winStepG B N Np oneW TW w e) st).1
          (L.foldl (winStepV (fun x y => Arith.redc B N Np (x * y)) TV oneV w e) resV) := by
  intro L
  induction L with
  | nil => intro st resV h _ _ hr; exact ⟨Ext.refl _, h, hr⟩
  | cons j L ih =>
    intro st resV h hone ht hr
    obtain ⟨e1, w1, o1, t1, r1⟩ := winStep_rel hinp B N Np hN hNp w e st resV j h hone ht hr
    obtain ⟨e2, w2, r2⟩ := ih _ _ w1 o1 t1 r1
    exact ⟨e1.trans e2, w2, r2⟩

/-- `winExpG` computes `Arith.winExp` with the Montgomery product. -/
theorem winExpG_rel (hinp : ∀ i, k ≤ i → inp i = false) (B N Np : Nat) (hN : N < 2 ^ B) (hNp : Np < 2 ^ B)
    {gb : GB} {oneW b : List Wire} {oneV bV : Nat} (w e : Nat) (h : WI k gb) (hone : Rel inp gb oneW oneV)
    (hb : Rel inp gb b bV) :
    Ext gb (winExpG B N Np oneW b w e gb).2 ∧ WI k (winExpG B N Np oneW b w e gb).2 ∧
      Rel inp (winExpG B N Np oneW b w e gb).2 (winExpG B N Np oneW b w e gb).1
        (Arith.winExp (fun x y => Arith.redc B N Np (x * y)) oneV bV B w e) := by
  have hT := winTbl_rel hinp B N Np hN hNp (oneW := oneW) (b := b) (oneV := oneV) (bV := bV) (2 ^ w - 2)
    ([oneW, b], gb) [oneV, bV] h hone hb (tblInit_rel hone hb)
  obtain ⟨e1, w1, o1, b1, t1⟩ := hT
  obtain ⟨e2, w2, r2⟩ := winLoop_rel hinp B N Np hN hNp w e ((List.range ((B + w - 1) / w)).reverse)
    (oneW, (winTblG B N Np oneW b w gb).2) oneV w1 o1 t1 o1
  exact ⟨e1.trans e2, w2, r2⟩

end

end SmcIrred
