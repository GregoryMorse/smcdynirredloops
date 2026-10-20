module

public import SmcIrred.Spec.VirtSel
public import SmcIrred.Prims.Decoder
public import SmcIrred.Prims.Nat

public section

namespace SmcIrred

/-! # Correctness of the selection and table-lookup gadgets (G30, R13) -/

theorem xorL_zipWith_false (a b : List Bool) (h : ∀ x ∈ a, x = false) : xorL (List.zipWith (· && ·) a b) = false := by
  induction a generalizing b with
  | nil => rfl
  | cons x t ih =>
    cases b with
    | nil => rfl
    | cons y u =>
      simp only [List.zipWith_cons_cons, xorL_cons]
      rw [h x List.mem_cons_self, ih u (fun z hz => h z (List.mem_cons_of_mem _ hz))]
      rfl

theorem filter_id_eq_nil (l : List Bool) : (l.filter id).length = 0 ↔ ∀ x ∈ l, x = false := by
  constructor
  · intro h x hx
    cases x with
    | false => rfl
    | true =>
      have hm : true ∈ l.filter id := List.mem_filter.2 ⟨hx, rfl⟩
      have := List.length_pos_of_mem hm
      omega
  · intro h
    have : l.filter id = [] := List.filter_eq_nil_iff.2 (fun x hx => by simp [h x hx])
    rw [this]; rfl

variable {inp : Nat → Bool} {k : Nat}

/-- The facts the scan guarantees: the state grows, the survivors and the early result exist, and the value is `target`. -/
@[expose] def SelRes (gb : GB) (inp : Nat → Bool) (target : Bool) (r : Option Wire × List Wire × GB) : Prop :=
  Ext gb r.2.2 ∧ Reach r.2.2 ∧ (∀ w ∈ r.2.1, w.ok r.2.2.n) ∧
    (match r.1 with
     | none => xorL (r.2.1.map (wev r.2.2 inp)) = target
     | some w => w.ok r.2.2.n ∧ wev r.2.2 inp w = target)

theorem selLoop_post (hinp : ∀ i, k ≤ i → inp i = false) :
    ∀ (ss ns : List Wire) (gb : GB) (acc : List Wire) (ps pn : List Bool),
      ss.length = ns.length → k ≤ gb.n → Reach gb → (∀ w ∈ ss, w.ok gb.n) → (∀ w ∈ ns, w.ok gb.n) → (∀ w ∈ acc, w.ok gb.n) →
      ps.length = pn.length →
      xorL (acc.map (wev gb inp)) = xorL (List.zipWith (· && ·) ps pn) →
      ((ps ++ ss.map (wev gb inp)).filter id).length ≤ 1 →
      SelRes gb inp (xorL (List.zipWith (· && ·) (ps ++ ss.map (wev gb inp)) (pn ++ ns.map (wev gb inp))))
        (selLoop gb acc ss ns) := by
  intro ss
  induction ss with
  | nil =>
    intro ns gb acc ps pn hl hk hr hss hns hacc hlen hx hc
    cases ns with
    | nil =>
      simp only [selLoop, SelRes, List.map_nil, List.append_nil]
      refine ⟨Ext.refl _, hr, hacc, ?_⟩
      rw [hx]
    | cons n ns => simp at hl
  | cons s ss ih =>
    intro ns gb acc ps pn hl hk hr hss hns hacc hlen hx hc
    cases ns with
    | nil => simp at hl
    | cons n ns =>
      have hl' : ss.length = ns.length := by simpa using hl
      simp only [List.map_cons] at hc
      have hsok : s.ok gb.n := hss s List.mem_cons_self
      have hnok : n.ok gb.n := hns n List.mem_cons_self
      have hss' : ∀ w ∈ ss, w.ok gb.n := fun w hw => hss w (List.mem_cons_of_mem _ hw)
      have hns' : ∀ w ∈ ns, w.ok gb.n := fun w hw => hns w (List.mem_cons_of_mem _ hw)
      have hmove : ∀ (sv nv : Bool),
          List.zipWith (· && ·) (ps ++ sv :: ss.map (wev gb inp)) (pn ++ nv :: ns.map (wev gb inp)) =
          List.zipWith (· && ·) ((ps ++ [sv]) ++ ss.map (wev gb inp)) ((pn ++ [nv]) ++ ns.map (wev gb inp)) := by
        intro sv nv
        simp
      have hxs : ∀ (sv nv : Bool), xorL (List.zipWith (· && ·) (ps ++ [sv]) (pn ++ [nv])) =
          (xorL (List.zipWith (· && ·) ps pn) != (sv && nv)) := by
        intro sv nv
        rw [List.zipWith_append hlen]
        simp [xorL_append_singleton]
      have hcnt : ∀ sv : Bool, ((ps ++ sv :: ss.map (wev gb inp)).filter id).length =
          (((ps ++ [sv]) ++ ss.map (wev gb inp)).filter id).length := by
        intro sv; rw [List.append_cons]
      cases s with
      | cst b =>
        cases b with
        | false =>
          have e : wev gb inp (.cst false) = false := rfl
          have hrec := ih ns gb acc (ps ++ [false]) (pn ++ [wev gb inp n]) hl' hk hr hss' hns' hacc
            (by simp [hlen])
            (by rw [hxs, ← hx]; simp)
            (by
              have := hcnt false
              rw [← this]
              simpa [e] using hc)
          simp only [selLoop, SelRes, List.map_cons]
          rw [e, hmove false (wev gb inp n)]
          exact hrec
        | true =>
          simp only [selLoop, SelRes, List.map_cons]
          have e : wev gb inp (.cst true) = true := rfl
          rw [e] at hc ⊢
          have hc2 : ((ps ++ true :: ss.map (wev gb inp)).filter id).length ≤ 1 := hc
          rw [List.filter_append, List.length_append, List.filter_cons_of_pos (by rfl)] at hc2
          simp only [List.length_cons] at hc2
          have hps : ∀ x ∈ ps, x = false := by
            rw [← filter_id_eq_nil]; omega
          have hss0 : ∀ x ∈ ss.map (wev gb inp), x = false := by
            rw [← filter_id_eq_nil]; omega
          refine ⟨Ext.refl _, hr, hacc, hnok, ?_⟩
          rw [List.zipWith_append hlen, xorL_append, xorL_zipWith_false ps pn hps]
          simp only [List.zipWith_cons_cons, xorL_cons, Bool.true_and]
          rw [xorL_zipWith_false _ _ hss0]
          simp
      | nd i =>
        cases n with
        | cst b =>
          cases b with
          | true =>
            have hacc' : ∀ w ∈ acc ++ [Wire.nd i], w.ok gb.n := by
              intro w hw
              rcases List.mem_append.1 hw with h | h
              · exact hacc w h
              · simp at h; rw [h]; exact hsok
            have e : wev gb inp (.cst true) = true := rfl
            have hrec := ih ns gb (acc ++ [Wire.nd i]) (ps ++ [wev gb inp (.nd i)]) (pn ++ [true]) hl' hk hr hss' hns' hacc'
              (by simp [hlen])
              (by rw [hxs, List.map_append]; simp only [List.map_cons, List.map_nil]; rw [xorL_append_singleton, hx]; simp)
              (by rw [← hcnt]; exact hc)
            simp only [selLoop, SelRes, List.map_cons]
            rw [e, hmove (wev gb inp (.nd i)) true]
            exact hrec
          | false =>
            have e : wev gb inp (.cst false) = false := rfl
            have hrec := ih ns gb acc (ps ++ [wev gb inp (.nd i)]) (pn ++ [false]) hl' hk hr hss' hns' hacc
              (by simp [hlen])
              (by rw [hxs, ← hx]; simp)
              (by rw [← hcnt]; exact hc)
            simp only [selLoop, SelRes, List.map_cons]
            rw [e, hmove (wev gb inp (.nd i)) false]
            exact hrec
        | nd j =>
          have ha := andV_post hinp hk hr [.nd i, .nd j] (by
            intro w hw
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
            rcases hw with rfl | rfl
            · exact hsok
            · exact hnok)
          have hand : andL ([Wire.nd i, Wire.nd j].map (wev gb inp)) = (wev gb inp (.nd i) && wev gb inp (.nd j)) := by
            simp only [List.map_cons, List.map_nil]
            exact andL_two _ _
          rw [hand] at ha
          simp only [selLoop]
          generalize hr0 : andV gb [Wire.nd i, Wire.nd j] = r0 at ha ⊢
          have hk1 : k ≤ r0.2.n := Nat.le_trans hk ha.ext.n_le
          have hss1 : ∀ w ∈ ss, w.ok r0.2.n := fun w hw => ok_mono (hss' w hw) ha.ext.n_le
          have hns1 : ∀ w ∈ ns, w.ok r0.2.n := fun w hw => ok_mono (hns' w hw) ha.ext.n_le
          have hacc1 : ∀ w ∈ acc ++ [r0.1], w.ok r0.2.n := by
            intro w hw
            rcases List.mem_append.1 hw with h | h
            · exact ok_mono (hacc w h) ha.ext.n_le
            · simp at h; rw [h]; exact ha.ok
          have hssv : ss.map (wev r0.2 inp) = ss.map (wev gb inp) :=
            List.map_congr_left (fun w hw => wev_ext ha.ext (hss' w hw))
          have hnsv : ns.map (wev r0.2 inp) = ns.map (wev gb inp) :=
            List.map_congr_left (fun w hw => wev_ext ha.ext (hns' w hw))
          have haccv : acc.map (wev r0.2 inp) = acc.map (wev gb inp) :=
            List.map_congr_left (fun w hw => wev_ext ha.ext (hacc w hw))
          have hrec := ih ns r0.2 (acc ++ [r0.1]) (ps ++ [wev gb inp (.nd i)]) (pn ++ [wev gb inp (.nd j)]) hl' hk1 ha.reach
            hss1 hns1 hacc1 (by simp [hlen])
            (by
              rw [hxs, List.map_append]
              simp only [List.map_cons, List.map_nil]
              rw [xorL_append_singleton, haccv, hx, ha.val])
            (by rw [hssv, ← hcnt]; simpa using hc)
          rw [hssv, hnsv] at hrec
          simp only [List.map_cons]
          rw [hmove (wev gb inp (.nd i)) (wev gb inp (.nd j))]
          obtain ⟨f1, f2, f3, f4⟩ := hrec
          exact ⟨ha.ext.trans f1, f2, f3, f4⟩

/-- One-bit multi-selection: with at most one true selector, the result is the selected number bit (false if none). -/
theorem selV_post (hinp : ∀ i, k ≤ i → inp i = false) {gb : GB} (hk : k ≤ gb.n) (hr : Reach gb) (sels nums : List Wire)
    (hl : sels.length = nums.length) (hs : ∀ w ∈ sels, w.ok gb.n) (hn : ∀ w ∈ nums, w.ok gb.n)
    (hc : ((sels.map (wev gb inp)).filter id).length ≤ 1) :
    Post gb (selV gb sels nums).2 inp (selV gb sels nums).1
      (xorL (List.zipWith (· && ·) (sels.map (wev gb inp)) (nums.map (wev gb inp)))) := by
  have h := selLoop_post (inp := inp) (k := k) hinp sels nums gb [] [] [] hl hk hr hs hn (by simp) rfl rfl
    (by simpa using hc)
  simp only [List.nil_append, List.map_nil] at h
  unfold selV
  generalize hq : selLoop gb [] sels nums = q at h
  obtain ⟨o, acc, gb'⟩ := q
  obtain ⟨e, r, hok, hv⟩ := h
  simp only at e r hok hv
  cases o with
  | some w =>
    simp only
    exact ⟨e, r, hv.1, hv.2⟩
  | none =>
    simp only at hv
    cases acc with
    | nil =>
      simp only
      refine ⟨e, r, trivial, ?_⟩
      rw [← hv]; rfl
    | cons a t =>
      simp only
      have p := xorV_post hinp (Nat.le_trans hk e.n_le) r (a :: t) hok
      rw [hv] at p
      exact p.lift e

/-- `mapG_wire` with an invariant of the state that every step may assume and that survives extension. -/
theorem mapG_wire_inv {α : Type} (f : GB → α → Wire × GB) (inputs : α → List Wire) (T : α → List Bool → Bool)
    (P : α → Prop) (I : GB → Prop) (hI : ∀ g g', Ext g g' → I g → I g') {inp : Nat → Bool} {k : Nat}
    (hf : ∀ (gb : GB) (a : α), P a → I gb → k ≤ gb.n → Reach gb → (∀ w ∈ inputs a, w.ok gb.n) →
      Post gb (f gb a).2 inp (f gb a).1 (T a ((inputs a).map (wev gb inp)))) :
    ∀ (l : List α) (gb : GB), (∀ a ∈ l, P a) → I gb → k ≤ gb.n → Reach gb → (∀ a ∈ l, ∀ w ∈ inputs a, w.ok gb.n) →
      Ext gb (mapG f gb l).2 ∧ Reach (mapG f gb l).2 ∧ (∀ w ∈ (mapG f gb l).1, w.ok (mapG f gb l).2.n) ∧
      (mapG f gb l).1.map (wev (mapG f gb l).2 inp) = l.map (fun a => T a ((inputs a).map (wev gb inp))) := by
  intro l
  induction l with
  | nil =>
    intro gb _ _ _ hr _
    exact ⟨Ext.refl _, hr, fun w hw => by simp [mapG] at hw, rfl⟩
  | cons a l ih =>
    intro gb hP hi hk hr hok
    have p := hf gb a (hP a List.mem_cons_self) hi hk hr (hok a List.mem_cons_self)
    have hk' : k ≤ (f gb a).2.n := Nat.le_trans hk p.ext.n_le
    have hok' : ∀ a' ∈ l, ∀ w ∈ inputs a', w.ok (f gb a).2.n := fun a' ha' w hw =>
      ok_mono (hok a' (List.mem_cons_of_mem _ ha') w hw) p.ext.n_le
    obtain ⟨e1, r1, o1, v1⟩ := ih (f gb a).2 (fun a' ha' => hP a' (List.mem_cons_of_mem _ ha')) (hI _ _ p.ext hi) hk' p.reach hok'
    have hm : mapG f gb (a :: l) = ((f gb a).1 :: (mapG f (f gb a).2 l).1, (mapG f (f gb a).2 l).2) := rfl
    rw [hm]
    refine ⟨p.ext.trans e1, r1, ?_, ?_⟩
    · intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact ok_mono p.ok e1.n_le
      · exact o1 w hw
    · simp only [List.map_cons]
      have hh : wev (mapG f (f gb a).2 l).2 inp (f gb a).1 = T a ((inputs a).map (wev gb inp)) := by
        rw [wev_ext e1 p.ok]; exact p.val
      have ht : (mapG f (f gb a).2 l).1.map (wev (mapG f (f gb a).2 l).2 inp) =
          l.map (fun a => T a ((inputs a).map (wev gb inp))) := by
        rw [v1]
        apply List.map_congr_left
        intro a' ha'
        have : (inputs a').map (wev (f gb a).2 inp) = (inputs a').map (wev gb inp) :=
          List.map_congr_left (fun w hw => wev_ext p.ext (hok a' (List.mem_cons_of_mem _ ha') w hw))
        rw [this]
      rw [hh, ht]

theorem zeroExt_val (gb : GB) (inp : Nat → Bool) (m : Nat) (x : List Wire) :
    (zeroExt m x).map (wev gb inp) = padB m (x.map (wev gb inp)) := by
  simp [zeroExt, padB, wev, Wire.ev]

theorem zeroExt_ok' {n m : Nat} {x : List Wire} (h : ∀ w ∈ x, w.ok n) : ∀ w ∈ zeroExt m x, w.ok n := by
  intro w hw
  unfold zeroExt at hw
  rcases List.mem_append.1 hw with h1 | h1
  · exact h w h1
  · rw [(List.mem_replicate.1 h1).2]; trivial

theorem getD_wev (gb : GB) (inp : Nat → Bool) : ∀ (l : List Wire) (j : Nat),
    wev gb inp (l.getD j (.cst false)) = (l.map (wev gb inp)).getD j false := by
  intro l
  induction l with
  | nil => intro j; rfl
  | cons a t ih =>
    intro j
    cases j with
    | zero => rfl
    | succ j => simpa using ih j

theorem getD_ok {n j : Nat} : ∀ {l : List Wire}, (∀ w ∈ l, w.ok n) → (l.getD j (.cst false)).ok n := by
  intro l
  induction l generalizing j with
  | nil => intro _; trivial
  | cons a t ih =>
    intro h
    cases j with
    | zero => exact h a List.mem_cons_self
    | succ j => exact ih (fun w hw => h w (List.mem_cons_of_mem _ hw))

/-- A gadget applied to every bit column of several numbers (`multi_to_virtual`). -/
theorem colsV_post (f : GB → List Wire → Wire × GB) (I : GB → Prop) (hI : ∀ g g', Ext g g' → I g → I g')
    (T : List Bool → Bool) {inp : Nat → Bool} {k : Nat} (nums : List (List Wire))
    (hf : ∀ (gb : GB) (col : List Wire), I gb → k ≤ gb.n → Reach gb → (∀ w ∈ col, w.ok gb.n) →
      col.length = nums.length → Post gb (f gb col).2 inp (f gb col).1 (T (col.map (wev gb inp))))
    (gb : GB) (hi : I gb) (hk : k ≤ gb.n) (hr : Reach gb) (hn : ∀ x ∈ nums, ∀ w ∈ x, w.ok gb.n) :
    Ext gb (colsV f gb nums).2 ∧ Reach (colsV f gb nums).2 ∧ (∀ w ∈ (colsV f gb nums).1, w.ok (colsV f gb nums).2.n) ∧
    (colsV f gb nums).1.map (wev (colsV f gb nums).2 inp) =
      (List.range ((nums.map List.length).foldl max 0)).map fun j =>
        T (nums.map fun x => (padB ((nums.map List.length).foldl max 0) (x.map (wev gb inp))).getD j false) := by
  unfold colsV
  generalize hm : (nums.map List.length).foldl max 0 = m
  have := mapG_wire_inv (inp := inp) (k := k)
    (fun gb j => f gb ((nums.map (zeroExt m)).map fun x => x.getD j (.cst false)))
    (fun j => (nums.map (zeroExt m)).map fun x => x.getD j (.cst false))
    (fun _ vs => T vs) (fun _ => True) I hI
    (by
      intro gb j _ hi hk hr hc
      apply hf gb _ hi hk hr hc
      simp)
    (List.range m) gb (fun _ _ => trivial) hi hk hr
    (by
      intro j _ w hw
      simp only [List.map_map, List.mem_map, Function.comp] at hw
      obtain ⟨x, hx, rfl⟩ := hw
      exact getD_ok (zeroExt_ok' (hn x hx)))
  obtain ⟨e, r, o, v⟩ := this
  refine ⟨e, r, o, ?_⟩
  rw [v]
  apply List.map_congr_left
  intro j _
  congr 1
  simp only [List.map_map, Function.comp]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp]
  rw [getD_wev, zeroExt_val]

theorem range_getD_padB (m : Nat) (l : List Bool) (h : l.length ≤ m) :
    (List.range m).map (fun j => (padB m l).getD j false) = padB m l := by
  have hl : (padB m l).length = m := by simp [padB]; omega
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl

theorem oneHot_succ_zero (n : Nat) : oneHot (n + 1) 0 = true :: List.replicate n false := by
  unfold oneHot
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_replicate]

theorem oneHot_succ_succ (n x : Nat) : oneHot (n + 1) (x + 1) = false :: oneHot n x := by
  unfold oneHot
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp

theorem xorL_oneHot_sel : ∀ (l : List Bool) (x : Nat), x < l.length →
    xorL (List.zipWith (· && ·) (oneHot l.length x) l) = l.getD x false := by
  intro l
  induction l with
  | nil => intro x h; simp at h
  | cons a t ih =>
    intro x h
    cases x with
    | zero =>
      simp only [List.length_cons]
      rw [oneHot_succ_zero]
      simp only [List.zipWith_cons_cons, xorL_cons]
      rw [xorL_zipWith_false _ _ (fun y hy => List.eq_of_mem_replicate hy)]
      simp
    | succ x =>
      simp only [List.length_cons] at h ⊢
      rw [oneHot_succ_succ]
      simp only [List.zipWith_cons_cons, xorL_cons]
      have := ih x (by omega)
      rw [this]
      simp

theorem oneHot_count (n x : Nat) : ((oneHot n x).filter id).length = if x < n then 1 else 0 := by
  induction n with
  | zero => simp [oneHot]
  | succ n ih =>
    have e : oneHot (n + 1) x = oneHot n x ++ [decide (n = x)] := by
      unfold oneHot
      rw [List.range_succ, List.map_append]
      simp only [List.map_cons, List.map_nil]
      congr 2
    rw [e, List.filter_append, List.length_append, ih]
    by_cases h : n = x
    · subst h; simp
    · have h1 : (List.filter id [decide (n = x)]).length = 0 := by simp [h]
      rw [h1]
      by_cases hx : x < n
      · have h2 : x < n + 1 := by omega
        simp [hx, h2]
      · have h2 : ¬ x < n + 1 := by omega
        simp [hx, h2]

theorem le_foldl_max {α : Type} (f : α → Nat) : ∀ (l : List α) (c : Nat) (a : α), a ∈ l →
    f a ≤ (l.map f).foldl max c := by
  intro l
  induction l with
  | nil => intro c a h; simp at h
  | cons b t ih =>
    intro c a h
    simp only [List.map_cons, List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · have : f a ≤ max c (f a) := Nat.le_max_right _ _
      refine Nat.le_trans this ?_
      clear ih h
      generalize max c (f a) = d
      induction t generalizing d with
      | nil => exact Nat.le_refl _
      | cons u v ih2 =>
        simp only [List.map_cons, List.foldl_cons]
        exact Nat.le_trans (Nat.le_max_left _ _) (ih2 _)
    · exact ih _ a h

theorem Post.cast {gb gb' : GB} {w : Wire} {v v' : Bool} {inp : Nat → Bool} (h : v = v') (p : Post gb gb' inp w v) :
    Post gb gb' inp w v' := h ▸ p

theorem iteV_post (hinp : ∀ i, k ≤ i → inp i = false) {gb : GB} (hk : k ≤ gb.n) (hr : Reach gb) {s : Wire}
    (hs : s.ok gb.n) (a b : List Wire) (ha : ∀ w ∈ a, w.ok gb.n) (hb : ∀ w ∈ b, w.ok gb.n) :
    Ext gb (iteV gb s a b).2 ∧ Reach (iteV gb s a b).2 ∧ (∀ w ∈ (iteV gb s a b).1, w.ok (iteV gb s a b).2.n) ∧
    (iteV gb s a b).1.map (wev (iteV gb s a b).2 inp) =
      if wev gb inp s then padB (max a.length b.length) (a.map (wev gb inp))
      else padB (max a.length b.length) (b.map (wev gb inp)) := by
  unfold iteV
  have hm : ([a, b].map List.length).foldl max 0 = max a.length b.length := by simp
  obtain ⟨e, r, o, v⟩ := colsV_post (inp := inp) (k := k)
    (fun gb col => let r0 := notV gb s; selV r0.2 [s, r0.1] col) (fun g => Ext gb g)
    (fun g g' e h => h.trans e)
    (fun vs => xorL (List.zipWith (· && ·) [wev gb inp s, !wev gb inp s] vs)) [a, b]
    (by
      intro g col hi hk' hr' hcok hcl
      have hsg : s.ok g.n := ok_mono hs hi.n_le
      have wsv : wev g inp s = wev gb inp s := wev_ext hi hs
      have p0 := notV_post hinp hk' hr' hsg
      have hs2 : s.ok (notV g s).2.n := ok_mono hsg p0.ext.n_le
      have hw2 : wev (notV g s).2 inp s = wev gb inp s := by rw [wev_ext p0.ext hsg, wsv]
      have hn2 : wev (notV g s).2 inp (notV g s).1 = !wev gb inp s := by rw [p0.val, wsv]
      have hcl' : col.length = 2 := by simpa using hcl
      have hcv : col.map (wev (notV g s).2 inp) = col.map (wev g inp) :=
        List.map_congr_left (fun w hw => wev_ext p0.ext (hcok w hw))
      have p1 := selV_post (inp := inp) (k := k) hinp (Nat.le_trans hk' p0.ext.n_le) p0.reach [s, (notV g s).1] col
        (by simp [hcl'])
        (by
          intro w hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · exact hs2
          · exact p0.ok)
        (fun w hw => ok_mono (hcok w hw) p0.ext.n_le)
        (by
          simp only [List.map_cons, List.map_nil, hw2, hn2]
          cases wev gb inp s <;> simp)
      show Post g (selV (notV g s).2 [s, (notV g s).1] col).2 inp (selV (notV g s).2 [s, (notV g s).1] col).1 _
      refine Post.cast ?_ (Post.lift p0.ext p1)
      simp only [List.map_cons, List.map_nil, hw2, hn2, hcv])
    gb (Ext.refl gb) hk hr
    (by
      intro x hx w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ha w hw
      · exact hb w hw)
  refine ⟨e, r, o, ?_⟩
  rw [v, hm]
  have hla : (a.map (wev gb inp)).length ≤ max a.length b.length := by
    rw [List.length_map]; exact Nat.le_max_left _ _
  have hlb : (b.map (wev gb inp)).length ≤ max a.length b.length := by
    rw [List.length_map]; exact Nat.le_max_right _ _
  cases hsv : wev gb inp s
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← range_getD_padB _ _ hlb]
    apply List.map_congr_left
    intro j _
    simp [xorL]
  · simp only [↓reduceIte]
    rw [← range_getD_padB _ _ hla]
    apply List.map_congr_left
    intro j _
    simp [xorL]

theorem constBits_length (e : Nat) : (constBits e).length = bitLen e := by simp [constBits]

theorem constBits_col (gb : GB) (inp : Nat → Bool) (e m j : Nat) (h : bitLen e ≤ m) :
    (padB m ((constBits e).map (wev gb inp))).getD j false = e.testBit j := by
  rw [← zeroExt_val, zeroExt_constBits e m h, List.map_map]
  have : (wev gb inp ∘ Wire.cst) = id := by funext b; rfl
  rw [this, List.map_id, ← bitsOf_range, List.getD_eq_getElem?_getD]
  by_cases hj : j < m
  · rw [List.getElem?_map, List.getElem?_range hj]; rfl
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp [testBit_ge j e (by omega)]

/-- Table lookup: the decoder one-hot selects the entry; the result is the entry as a `tblW`-bit vector. -/
theorem tableLookupV_post (hinp : ∀ i, k ≤ i → inp i = false) {gb : GB} (hk : k ≤ gb.n) (hr : Reach gb)
    (idx : List Wire) (hidx : ∀ w ∈ idx, w.ok gb.n) (tab : List Nat) (htab : tab.length = 2 ^ idx.length) :
    Ext gb (tableLookupV gb idx tab).2 ∧ Reach (tableLookupV gb idx tab).2 ∧
    (∀ w ∈ (tableLookupV gb idx tab).1, w.ok (tableLookupV gb idx tab).2.n) ∧
    (tableLookupV gb idx tab).1.map (wev (tableLookupV gb idx tab).2 inp) =
      natBits (tab.getD (bv (idx.map (wev gb inp))) 0) (tblW tab) := by
  obtain ⟨de, dr, dok, dv⟩ := decoderShift_post (inp := inp) (k := k) hinp hk hr idx hidx
  simp only [tableLookupV]
  generalize hd : decoderShift gb idx = d at de dr dok dv ⊢
  obtain ⟨d1, d2⟩ := d
  simp only at de dr dok dv ⊢
  generalize hx : bv (idx.map (wev gb inp)) = x at dv
  have hxlt : x < tab.length := by
    rw [htab, ← hx]
    have := bv_lt (idx.map (wev gb inp))
    simpa using this
  have hlen1 : d1.length = 2 ^ idx.length := by
    have := congrArg List.length dv
    simpa [oneHot_length] using this
  obtain ⟨e, r, o, v⟩ := colsV_post (inp := inp) (k := k)
    (fun g col => selV g d1 col) (fun g => Ext d2 g) (fun g g' e h => h.trans e)
    (fun vs => xorL (List.zipWith (· && ·) (oneHot (2 ^ idx.length) x) vs)) (tab.map constBits)
    (by
      intro g col hi hk' hr' hcok hcl
      have hv1 : d1.map (wev g inp) = oneHot (2 ^ idx.length) x := by
        rw [← dv]; exact List.map_congr_left (fun w hw => wev_ext hi (dok w hw))
      have p1 := selV_post (inp := inp) (k := k) hinp hk' hr' d1 col
        (by rw [hlen1, hcl]; simp [htab])
        (fun w hw => ok_mono (dok w hw) hi.n_le) hcok
        (by rw [hv1, oneHot_count]; split <;> omega)
      refine Post.cast ?_ p1
      rw [hv1])
    d2 (Ext.refl _) (Nat.le_trans hk de.n_le) dr
    (by
      intro y hy w hw
      simp only [List.mem_map] at hy
      obtain ⟨t, _, rfl⟩ := hy
      simp only [constBits, List.mem_map] at hw
      obtain ⟨j, _, rfl⟩ := hw
      trivial)
  refine ⟨de.trans e, r, o, ?_⟩
  rw [v]
  have hm : ((tab.map constBits).map List.length).foldl max 0 = tblW tab := by
    unfold tblW
    rw [List.map_map]
    congr 1
    exact List.map_congr_left (fun t _ => constBits_length t)
  rw [hm, natBits_eq_bitsOf, ← bitsOf_range]
  apply List.map_congr_left
  intro j _
  have hcol : ((tab.map constBits).map fun y => (padB (tblW tab) (y.map (wev d2 inp))).getD j false) =
      tab.map (fun t => t.testBit j) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro t ht
    simp only [Function.comp]
    apply constBits_col
    unfold tblW
    exact le_foldl_max bitLen tab 0 t ht
  simp only [hcol]
  have := xorL_oneHot_sel (tab.map (fun t => t.testBit j)) x (by simpa using hxlt)
  rw [List.length_map, htab] at this
  rw [this, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hxlt]
  rfl

end SmcIrred
