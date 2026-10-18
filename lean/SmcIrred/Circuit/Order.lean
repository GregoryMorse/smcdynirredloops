module

public import SmcIrred.Circuit.CodeModel

public section

namespace SmcIrred

variable {lib : Lib} {V : Circ → (Nat → Bool) → Nat → Nat → Bool} {c : Circ} {inp : Nat → Bool} {ord : List Nat}

theorem cnt_congr {a1 a2 : Nat → Bool} {l : List Nat} (h : ∀ y ∈ l, a1 y = a2 y) : cnt a1 l = cnt a2 l := by
  unfold cnt
  rw [List.filter_congr h]

theorem any_congr {α : Type} {f g : α → Bool} : ∀ l : List α, (∀ p ∈ l, f p = g p) → l.any f = l.any g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    simp only [List.any_cons]
    rw [h a List.mem_cons_self, ih (fun p hp => h p (List.mem_cons_of_mem _ hp))]

theorem any_congr_zip {a1 a2 : Nat → Bool} {s l : List Nat} (h : ∀ y ∈ l, a1 y = a2 y) (u : Nat) :
    ((s.zip l).any fun p => p.1 == u && a1 p.2) = ((s.zip l).any fun p => p.1 == u && a2 p.2) :=
  any_congr _ (fun p hp => by rw [h p.2 (List.of_mem_zip hp).2])

theorem callOf_congr {a1 a2 : Nat → Bool} {ins : List Nat} (h : ∀ y ∈ ins, a1 y = a2 y) (sid reps : Nat) :
    callOf lib V a1 sid ins reps = callOf lib V a2 sid ins reps := by
  unfold callOf
  have : (fun u => ((lib sid).ins.zip ins).any fun p => p.1 == u && a1 p.2) =
      (fun u => ((lib sid).ins.zip ins).any fun p => p.1 == u && a2 p.2) := funext (any_congr_zip h)
  simp only []
  rw [this]

theorem writtenBy_congr {a1 a2 : Nat → Bool} {u v : Nat} (h : ∀ y ∈ c.reads u, a1 y = a2 y) :
    writtenBy lib V a1 c u v = writtenBy lib V a2 c u v := by
  unfold writtenBy
  cases hk : c.kind u with
  | call sid ins outs reps =>
    have hp : ∀ y ∈ c.pred u, a1 y = a2 y := fun y hy => h y (by unfold Circ.reads; exact List.mem_append_left _ hy)
    have hi : ∀ y ∈ ins, a1 y = a2 y := fun y hy => h y (by unfold Circ.reads; rw [hk]; exact List.mem_append_right _ hy)
    simp only [cnt_congr hp, callOf_congr hi]
  | _ => rfl

theorem baseVal_congr {a1 a2 : Nat → Bool} {x : Nat} (h : ∀ y ∈ c.reads x, a1 y = a2 y) :
    baseVal c inp a1 x = baseVal c inp a2 x := by
  have hp : ∀ y ∈ c.pred x, a1 y = a2 y := fun y hy => h y (by unfold Circ.reads; exact List.mem_append_left _ hy)
  unfold baseVal
  cases hk : c.kind x with
  | tbl sel tab =>
    have hs : ∀ y ∈ sel, a1 y = a2 y := fun y hy => h y (by unfold Circ.reads; rw [hk]; exact List.mem_append_right _ hy)
    simp only [cnt_congr hp]
    have e : (sel.zip tab).any (fun p : Nat × Bool => a1 p.1 && p.2) = (sel.zip tab).any (fun p : Nat × Bool => a2 p.1 && p.2) :=
      any_congr _ (fun p hp => by rw [hs p.1 (List.of_mem_zip hp).1])
    rw [e]
  | _ => simp only [cnt_congr hp]

theorem cnt_append (acc : Nat → Bool) (l1 l2 : List Nat) : cnt acc (l1 ++ l2) = cnt acc l1 + cnt acc l2 := by
  unfold cnt; rw [List.filter_append, List.length_append]

theorem step_cnt {acc : Nat → Bool} (htok : acc c.n = true) (x : Nat) :
    cnt acc (c.pred x ++ (if inp x then [c.n] else [])) = cnt acc (c.pred x) + (if inp x then 1 else 0) := by
  by_cases hi : inp x = true
  · simp only [hi, ↓reduceIte, cnt_append]; unfold cnt; simp [htok]
  · have hi' : inp x = false := by simpa using hi
    simp only [hi', Bool.false_eq_true, ↓reduceIte, List.append_nil, Nat.add_zero]

/-- The step of the code model at the vertex itself: the value from the predecessors, kept if the vertex was already
accepting (a call's output vertex). -/
theorem stepCode_self {acc : Nat → Bool} (htok : acc c.n = true) {x : Nat}
    (hnf : c.kind x = .flow ∨ acc x = false) (hinp : inp x = true → c.kind x = .flow)
    (hout : ∀ sid ins outs reps, c.kind x = .call sid ins outs reps → x ∉ outs) :
    stepCode lib V c inp x acc x = (baseVal c inp acc x || acc x) := by
  unfold stepCode baseVal
  simp only [step_cnt htok x, List.length_append]
  cases hk : c.kind x with
  | flow =>
    clear hnf hout hinp
    cases hi : inp x <;> simp only [hi, Bool.false_eq_true, ↓reduceIte, List.length_nil, Nat.add_zero, List.append_nil,
      List.length_cons, Nat.zero_add] <;> split <;> simp_all
  | any =>
    have hax : acc x = false := hnf.resolve_left (by simp [hk])
    have hi : inp x = false := by cases h : inp x; rfl; exact absurd (hinp h) (by simp [hk])
    simp only [hi] ; (repeat' split) <;> simp_all
  | add =>
    have hax : acc x = false := hnf.resolve_left (by simp [hk])
    have hi : inp x = false := by cases h : inp x; rfl; exact absurd (hinp h) (by simp [hk])
    simp only [hi]; (repeat' split) <;> simp_all
  | addneg =>
    have hax : acc x = false := hnf.resolve_left (by simp [hk])
    have hi : inp x = false := by cases h : inp x; rfl; exact absurd (hinp h) (by simp [hk])
    simp only [hi]; (repeat' split) <;> simp_all
  | tbl sel tab =>
    have hax : acc x = false := hnf.resolve_left (by simp [hk])
    have hi : inp x = false := by cases h : inp x; rfl; exact absurd (hinp h) (by simp [hk])
    simp only [hi]; (repeat' split) <;> simp_all
  | call sid ins outs reps =>
    have hax : acc x = false := hnf.resolve_left (by simp [hk])
    have hi : inp x = false := by cases h : inp x; rfl; exact absurd (hinp h) (by simp [hk])
    have hx := hout sid ins outs reps hk
    simp only [hi, Bool.false_eq_true, ↓reduceIte, List.length_nil, Nat.add_zero, List.append_nil]
    by_cases hc : cnt acc (c.pred x) = 1
    · simp only [hc, ↓reduceIte]
      have : ((outs.zip (lib sid).outs).any fun p => p.1 == x && finalZ (callOf lib V acc sid ins reps) p.2) = false := by
        apply List.any_eq_false.2
        intro p hp
        have : p.1 ≠ x := fun e => hx (e ▸ (List.of_mem_zip hp).1)
        simp [this]
      show (acc x || _) = (false || acc x)
      rw [this]; simp
    · simp [hc, hax]

theorem ite_ap {p : Prop} [Decidable p] (f g : Nat → Bool) (y : Nat) : (if p then f else g) y = if p then f y else g y := by
  split <;> rfl

/-- The step of the code model at any other vertex: unchanged, except for the outputs written by a call. -/
theorem stepCode_other {acc : Nat → Bool} {x : Nat} (hinp : inp x = true → c.kind x = .flow) {y : Nat} (hy : y ≠ x) :
    stepCode lib V c inp x acc y = (acc y || writtenBy lib V acc c x y) := by
  unfold stepCode writtenBy
  cases hk : c.kind x with
  | call sid ins outs reps =>
    have hi : inp x = false := by cases h : inp x; rfl; exact absurd (hinp h) (by simp [hk])
    simp only [hi, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.length_nil, Nat.add_zero]
    by_cases hc : cnt acc (c.pred x) = 1
    · simp [hc]
    · simp [hc]
  | _ => simp [ite_ap, hy]

theorem wb_true (h : PassWF c inp ord) {acc : Nat → Bool} {u v : Nat}
    (hw : writtenBy lib V acc c u v = true) : c.kind v = .flow ∧ c.pred v = [u] := by
  unfold writtenBy at hw
  cases hk : c.kind u with
  | call sid ins outs reps =>
    rw [hk] at hw
    simp only [Bool.and_eq_true, List.any_eq_true] at hw
    obtain ⟨-, p, hp, hpv⟩ := hw
    have hv : v ∈ outs := by
      have e : p.1 = v := by simpa using hpv.1
      rw [← e]; exact (List.of_mem_zip hp).1
    obtain ⟨-, h1, h2, -⟩ := h.port u sid ins outs reps hk v hv
    exact ⟨h1, h2⟩
  | _ => rw [hk] at hw; simp at hw

theorem pass_nodup (h : PassWF c inp ord) : ord.Nodup := h.perm.nodup_iff.2 List.nodup_range

theorem pass_length (h : PassWF c inp ord) : ord.length = c.n := by
  have := h.perm.length_eq; simpa using this

/-- The invariant of the pass after the first `k` vertices of the dependency order. -/
theorem runPass_inv (h : PassWF c inp ord) : ∀ k, k ≤ ord.length →
    (∀ x ∈ ord.take k, ∀ f, k ≤ f →
      (ord.take k).foldl (fun acc x => stepCode lib V c inp x acc) (fun u => decide (u = c.n)) x =
        valAt lib V c inp f x) ∧
    (∀ y, y ≠ c.n → y ∉ ord.take k →
      (ord.take k).foldl (fun acc x => stepCode lib V c inp x acc) (fun u => decide (u = c.n)) y =
        (c.pred y).any fun u => decide (u ∈ ord.take k) && writtenBy lib V (valAt lib V c inp c.n) c u y) ∧
    (ord.take k).foldl (fun acc x => stepCode lib V c inp x acc) (fun u => decide (u = c.n)) c.n = true := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun x hx => by simp at hx, fun y hy _ => ?_, by simp⟩
    simp [hy]
  | succ k ih =>
    intro hk1
    have hk : k < ord.length := hk1
    obtain ⟨ihA, ihB, ihC⟩ := ih (Nat.le_of_lt hk)
    generalize hS : (ord.take k).foldl (fun acc x => stepCode lib V c inp x acc) (fun u => decide (u = c.n)) = S at ihA ihB ihC
    obtain ⟨x, hxe⟩ : ∃ x, ord[k]? = some x := ⟨ord[k], List.getElem?_eq_getElem hk⟩
    have hxget : ord[k] = x := by simpa [List.getElem?_eq_getElem hk] using hxe
    have htake : ord.take (k + 1) = ord.take k ++ [x] := by rw [List.take_add_one, hxe]; rfl
    have hfold : (ord.take (k + 1)).foldl (fun acc x => stepCode lib V c inp x acc) (fun u => decide (u = c.n)) =
        stepCode lib V c inp x S := by
      rw [htake, List.foldl_append, hS]; rfl
    have hsplit : ord = ord.take k ++ x :: ord.drop (k + 1) := by
      have := List.take_append_drop k ord
      rw [List.drop_eq_getElem_cons hk, hxget] at this
      exact this.symm
    have hreads : ∀ y ∈ c.reads x, y ∈ ord.take k := h.topo _ x _ hsplit
    have hclos : ∀ u ∈ ord.take k, ∀ y ∈ c.reads u, y ∈ ord.take k := by
      intro u hu y hy
      obtain ⟨s1, t1, he⟩ := List.append_of_mem hu
      have hord : ord = s1 ++ u :: (t1 ++ ord.drop k) := by
        have := List.take_append_drop k ord
        rw [he] at this
        simpa using this.symm
      have := h.topo s1 u _ hord y hy
      rw [he]; exact List.mem_append_left _ this
    have hnd := pass_nodup h
    have hxnot : x ∉ ord.take k := by
      rw [hsplit] at hnd
      exact fun hm => (List.nodup_append.1 hnd).2.2 x hm x List.mem_cons_self rfl
    have hxlt : x < c.n := by
      have : x ∈ ord := by rw [hsplit]; simp
      exact List.mem_range.1 (h.perm.mem_iff.1 this)
    have hkn : k ≤ c.n := by have := pass_length h; omega
    have hSn : ∀ y ∈ ord.take k, valAt lib V c inp c.n y = S y := fun y hy => (ihA y hy c.n hkn).symm
    -- the written outputs of any call at an earlier vertex are not yet processed
    have hwb_conv : ∀ u ∈ ord.take k, ∀ v, writtenBy lib V (valAt lib V c inp c.n) c u v =
        writtenBy lib V S c u v := by
      intro u hu v
      apply writtenBy_congr
      intro y hy
      exact hSn y (hclos u hu y hy)
    have hout_not : ∀ z ∈ ord.take k, writtenBy lib V S c x z = false := by
      intro z hz
      apply Classical.byContradiction
      intro hne
      have hw : writtenBy lib V S c x z = true := by simpa using hne
      have hpz := (wb_true h hw).2
      have : x ∈ c.reads z := by unfold Circ.reads; rw [hpz]; simp
      exact hxnot (hclos z hz x this)
    have hinp := fun hi => (h.inp_wf x hi).1
    refine ⟨?_, ?_, ?_⟩
    · intro z hz f hf
      rw [hfold]
      rw [htake] at hz
      rcases List.mem_append.1 hz with hz | hz
      · have hzx : z ≠ x := fun e => hxnot (e ▸ hz)
        rw [stepCode_other hinp hzx, hout_not z hz, Bool.or_false]
        exact ihA z hz f (by omega)
      · have hzx : z = x := List.mem_singleton.1 hz
        subst hzx
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        have hnf : c.kind z = .flow ∨ S z = false := by
          by_cases hf : c.kind z = .flow
          · exact Or.inl hf
          · right
            rw [ihB z (Nat.ne_of_lt hxlt) hxnot]
            apply Bool.eq_false_iff.2
            intro hne
            obtain ⟨u, hu, hu2⟩ := List.any_eq_true.1 hne
            simp only [Bool.and_eq_true] at hu2
            obtain ⟨-, hw⟩ := hu2
            exact hf (wb_true h hw).1
        have hout : ∀ sid ins outs reps, c.kind z = .call sid ins outs reps → z ∉ outs := by
          intro sid ins outs reps hkz hzo
          have := (h.port z sid ins outs reps hkz z hzo).2.1
          rw [hkz] at this; cases this
        have hSn_tok : S c.n = true := ihC
        rw [stepCode_self hSn_tok hnf hinp hout]
        show (baseVal c inp S z || S z) = valAt lib V c inp (g + 1) z
        simp only [valAt]
        have hb : baseVal c inp (valAt lib V c inp g) z = baseVal c inp S z := by
          apply baseVal_congr
          intro y hy
          exact ihA y (hreads y hy) g (by omega) |>.symm
        rw [hb]
        have hany : ((c.pred z).any fun u => writtenBy lib V (valAt lib V c inp g) c u z) = S z := by
          rw [ihB z (Nat.ne_of_lt hxlt) hxnot]
          apply any_congr
          intro u hu
          have hu' : u ∈ ord.take k := hreads u (by unfold Circ.reads; exact List.mem_append_left _ hu)
          simp only [hu', decide_true, Bool.true_and]
          rw [hwb_conv u hu']
          apply writtenBy_congr
          intro y hy
          exact (ihA y (hclos u hu' y hy) g (by omega)).symm
        rw [hany]
    · intro y hyn hy
      rw [htake] at hy
      have hy1 : y ∉ ord.take k := fun hm => hy (List.mem_append_left _ hm)
      have hyx : y ≠ x := fun e => hy (by rw [e]; simp)
      rw [hfold, stepCode_other hinp hyx, ihB y hyn hy1]
      have hcv : writtenBy lib V S c x y = writtenBy lib V (valAt lib V c inp c.n) c x y := by
        apply writtenBy_congr
        intro w hw
        exact (hSn w (hreads w hw)).symm
      rw [hcv, htake]
      apply Bool.eq_iff_iff.2
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_append,
        List.mem_singleton]
      constructor
      · rintro (⟨u, hu, hu1, hu2⟩ | hw)
        · exact ⟨u, hu, Or.inl hu1, hu2⟩
        · refine ⟨x, ?_, Or.inr rfl, hw⟩
          rw [(wb_true h hw).2]; simp
      · rintro ⟨u, hu, hu1 | hu1, hu2⟩
        · exact Or.inl ⟨u, hu, hu1, hu2⟩
        · subst hu1; exact Or.inr hu2
    · rw [hfold, stepCode_other hinp (Nat.ne_of_gt hxlt), ihC]; rfl

/-- The code model computes the declarative values: the final accepting set of the pass is `valAt` with fuel `n`. -/
theorem runPass_eq_val (h : PassWF c inp ord) {x : Nat} (hx : x < c.n) :
    runPass lib V c inp ord x = valAt lib V c inp c.n x := by
  have hl := pass_length h
  have hxo : x ∈ ord.take ord.length := by
    rw [List.take_length]; exact h.perm.mem_iff.2 (List.mem_range.2 hx)
  have := (runPass_inv (lib := lib) (V := V) h ord.length (Nat.le_refl _)).1 x hxo c.n (by omega)
  rw [List.take_length] at this
  exact this

/-- Order independence (C49, C77 foundation): every dependency order gives the same accepting set, the randomized
`topo_kahn` order is harmless. -/
theorem order_independent {o1 o2 : List Nat} (h1 : PassWF c inp o1) (h2 : PassWF c inp o2) {x : Nat} (hx : x < c.n) :
    runPass lib V c inp o1 x = runPass lib V c inp o2 x := by
  rw [runPass_eq_val h1 hx, runPass_eq_val h2 hx]

/-- The code model equals the semantics of the circuit at nesting depth `d + 1`. -/
theorem runPass_eq_circ_val (d : Nat) (h : PassWF c inp ord) {x : Nat} (hx : x < c.n) (lib : Lib) :
    runPass lib (level lib d).val c inp ord x = c.val lib (d + 1) inp x := by
  rw [runPass_eq_val h hx]; rfl

end SmcIrred
