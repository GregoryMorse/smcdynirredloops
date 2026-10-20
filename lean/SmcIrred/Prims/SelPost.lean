module

public import SmcIrred.Spec.VirtSel
public import SmcIrred.Prims.Decoder
public import SmcIrred.Prims.BvDsl

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

end SmcIrred
