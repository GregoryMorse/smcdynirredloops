module

public import SmcIrred.Extremal.MEEBound

public section

namespace SmcIrred

variable {g : Digraph} {r : Nat} {J : Jungle}

/-- With a vertex `a0` earlier than `b` and neither a tree neighbour nor multiple-entry adjacent to `b`, the bound of
`per_vertex` is off by two. -/
theorem per_vertex_strict (hv : J.Valid g r) {b a0 : Nat} (hb : b < g.n) (hbr : b ≠ r) (ha0 : a0 < g.n)
    (hl : J.pre a0 < J.pre b) (hnp : ¬ J.IsParent g a0 b) (hn1 : ¬ g.IsMEE J a0 b) (hn2 : ¬ g.IsMEE J b a0) :
    meeA g J b + meeC g J b + 2 ≤ earlier J g.n b := by
  have hd : ∀ a ∈ List.range g.n, ¬ (decide (g.IsMEE J a b ∧ J.pre a < J.pre b) = true ∧
      decide (g.IsMEE J b a ∧ J.pre a < J.pre b) = true) := by
    intro a _ ⟨h1, h2⟩
    simp only [decide_eq_true_eq] at h1 h2
    exact hv.mee_excl h1.1 h2.1
  obtain ⟨p, hp, -⟩ := hv.parent b hb hbr
  have hpn : p < g.n := hp.1
  have hlt := hv.parent_nested hpn hb hp
  have hpa0 : a0 ≠ p := fun e => hnp (e ▸ hp)
  have h1 := filter_len_add_le (l := List.range g.n) (p := fun x => decide (g.IsMEE J x b ∧ J.pre x < J.pre b))
    (q := fun y => decide (g.IsMEE J b y ∧ J.pre y < J.pre b))
    (r := fun a => decide (J.pre a < J.pre b ∧ a ≠ p ∧ a ≠ a0))
    (fun a _ h => by
      simp only [decide_eq_true_eq] at h ⊢
      refine ⟨h.2, fun e => ?_, fun e => ?_⟩
      · subst e
        exact (Jungle.Valid.mee_not_parent h.1).1 hp
      · subst e
        exact hn1 h.1)
    (fun a _ h => by
      simp only [decide_eq_true_eq] at h ⊢
      refine ⟨h.2, fun e => ?_, fun e => ?_⟩
      · subst e
        exact (Jungle.Valid.mee_not_parent h.1).2 hp
      · subst e
        exact hn2 h.1) hd
  have h2 := filter_len_lt (l := List.range g.n) (p := fun a => decide (J.pre a < J.pre b ∧ a ≠ p ∧ a ≠ a0))
    (q := fun a => decide (J.pre a < J.pre b ∧ a ≠ p)) (v := a0)
    (fun a h => by simp only [decide_eq_true_eq] at h ⊢; exact ⟨h.1, h.2.1⟩) (List.mem_range.2 ha0)
    (by simp) (by simp only [decide_eq_true_eq]; exact ⟨hl, hpa0⟩)
  have h3 := filter_len_lt (l := List.range g.n) (p := fun a => decide (J.pre a < J.pre b ∧ a ≠ p))
    (q := fun a => decide (J.pre a < J.pre b)) (v := p)
    (fun a h => by simp only [decide_eq_true_eq] at h ⊢; exact h.1) (List.mem_range.2 hpn)
    (by simp) (by simp only [decide_eq_true_eq]; exact hlt.1)
  unfold meeA meeC earlier
  omega

theorem sum_eq_of_le (f h : Nat → Nat) : ∀ l : List Nat, (∀ b ∈ l, f b ≤ h b) →
    (l.map f).sum = (l.map h).sum → ∀ b ∈ l, f b = h b := by
  intro l
  induction l with
  | nil => intro _ _ b hb; simp at hb
  | cons a l ih =>
    intro hle hs b hb
    simp only [List.map_cons, List.sum_cons] at hs
    have h1 := hle a List.mem_cons_self
    have h2 := ih (fun c hc => hle c (List.mem_cons_of_mem _ hc))
    have h3 : (l.map f).sum ≤ (l.map h).sum := by
      have : ∀ (l : List Nat), (∀ b ∈ l, f b ≤ h b) → (l.map f).sum ≤ (l.map h).sum := by
        intro l
        induction l with
        | nil => intro _; simp
        | cons a l ih =>
          intro h
          simp only [List.map_cons, List.sum_cons]
          have := h a List.mem_cons_self
          have := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
          omega
      exact this l (fun c hc => hle c (List.mem_cons_of_mem _ hc))
    have e : f a = h a := by omega
    rcases List.mem_cons.1 hb with rfl | hb
    · exact e
    · exact h2 (by omega) b hb

/-- The extremal hypothesis, per pair of vertices: if `a` was discovered before `b` and is not its tree parent, then one of
the two edges between them is multiple-entry. -/
@[expose] def MaxPairs (g : Digraph) (J : Jungle) : Prop :=
  ∀ a b, a < g.n → b < g.n → J.pre a < J.pre b → ¬ J.IsParent g a b → g.IsMEE J a b ∨ g.IsMEE J b a

theorem tight_arith (n M E : Nat) (hn : 1 ≤ n) (hM : 2 * M = (n - 1) * (n - 2)) (hE : 2 * E + n = n * n) :
    M + (n - 1) = E := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e : m + 1 - 1 = m := by omega
  rw [e] at hM ⊢
  rcases m with _ | m
  · simp at hM hE ⊢; omega
  · have e2 : m + 1 + 1 - 2 = m := by omega
    rw [e2] at hM
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at hM hE
    omega

theorem maxPairs_of_max (hcfg : g.IsCFG r) (hv : J.Valid g r) (hmax : 2 * g.meeCount J = (g.n - 1) * (g.n - 2)) :
    MaxPairs g J := by
  have hr := hcfg.1
  have hite : ((List.range g.n).map fun b => if b = r then 0 else 1).sum = g.n - 1 := by
    have := count_ne g.n r hr
    rw [count_eq_sum] at this
    rw [← this]
    apply congrArg List.sum; apply List.map_congr_left; intro b _
    by_cases h : b = r <;> simp [h]
  have hT := earlier_sum J g.n (fun a b ha hb => hv.pre_inj a b ha hb)
  have hsum : ((List.range g.n).map fun b => meeA g J b + meeC g J b + (if b = r then 0 else 1)).sum =
      ((List.range g.n).map fun b => earlier J g.n b).sum := by
    rw [sum_map_add, ← meeCount_decomp hv, hite]
    exact tight_arith g.n _ _ (by omega) hmax hT
  have hle : ∀ b ∈ List.range g.n, (meeA g J b + meeC g J b + (if b = r then 0 else 1)) ≤ earlier J g.n b :=
    fun b hb => per_vertex hv (List.mem_range.1 hb)
  have heq := sum_eq_of_le _ _ _ hle hsum
  intro a b ha hb hl hnp
  apply Classical.byContradiction
  intro hcon
  have hn1 : ¬ g.IsMEE J a b := fun h => hcon (Or.inl h)
  have hn2 : ¬ g.IsMEE J b a := fun h => hcon (Or.inr h)
  have hbr : b ≠ r := by
    intro e
    subst e
    have := (hv.root a ha).1
    omega
  have h1 := per_vertex_strict hv hb hbr ha hl hnp hn1 hn2
  have h2 := heq b (List.mem_range.2 hb)
  simp only [hbr, ↓reduceIte] at h2
  omega

/-- Under the extremal hypothesis no vertex is discovered strictly between a vertex and its parent. -/
theorem between (hv : J.Valid g r) (hE : MaxPairs g J) {b p : Nat} (hb : b < g.n) (hp : J.IsParent g p b) :
    ∀ k x, J.pre x = k → x < g.n → J.pre p < J.pre x → J.pre x < J.pre b → False := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro x hk hx h1 h2
    have hpn := hp.1
    have hpb := hv.parent_nested hpn hb hp
    have hxr : x ≠ r := by
      intro e; subst e
      have := (hv.root p hpn).1
      omega
    obtain ⟨q, hq, _⟩ := hv.parent x hx hxr
    have hqn := hq.1
    have hib := hv.interval b hb
    have hix := hv.interval x hx
    have hanc : J.Anc p x := by
      rcases hv.laminar p x hpn hx with c | c | c | c
      · exact c
      · have := c.1; omega
      · omega
      · omega
    have hpx : p ≠ x := by intro e; subst e; omega
    have hpq : J.Anc p q := hq.2.2.2 p hpn hpx hanc
    by_cases hqp : q = p
    · have hq' : J.IsParent g p x := hqp ▸ hq
      have hxb : x ≠ b := by intro e; subst e; omega
      have hnotanc : ¬ J.Anc x b := by
        intro h
        have := (hp.2.2.2 x hx hxb h).1
        omega
      have hnpar : ¬ J.IsParent g x b := fun hxp => hnotanc hxp.2.2.1
      rcases hE x b hx hb h2 hnpar with hm | hm
      · have hpost : J.post x < J.pre b := by
          rcases hv.laminar x b hx hb with c | c | c | c
          · exact absurd c hnotanc
          · have := c.1; omega
          · exact c
          · omega
        exact hv.no_rightward x b hm.1 hpost
      · obtain ⟨-, w, hw, hwx, hnw⟩ := hm
        have hwa := Digraph.Body.anc hw
        have hwp : J.Anc w p := hq'.2.2.2 w (hw.1.lt g J) (Ne.symm hwx) hwa
        exact hnw (hwp.trans hp.2.2.1)
    · have hpq' : J.pre p ≠ J.pre q := fun e => hqp (hv.pre_inj q p hqn hpn e.symm)
      have hlt1 : J.pre p < J.pre q := by have := hpq.1; omega
      have hlt2 := (hv.parent_nested hqn hx hq).1
      exact ih (J.pre q) (by omega) q rfl hqn hlt1 (by omega)

/-- Under the extremal hypothesis every vertex that is not last in preorder has a child. -/
theorem child_exists (hv : J.Valid g r) (hE : MaxPairs g J) {y : Nat} (hy : y < g.n) :
    ∀ k x, J.pre x = k → x < g.n → J.pre y < J.pre x → ∃ c, c < g.n ∧ J.IsParent g y c := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro x hk hx hyx
    have hxr : x ≠ r := by
      intro e; subst e
      have := (hv.root y hy).1
      omega
    obtain ⟨q, hq, _⟩ := hv.parent x hx hxr
    have hqn := hq.1
    have hqx := (hv.parent_nested hqn hx hq).1
    by_cases hlt : J.pre q < J.pre y
    · exact (between hv hE hx hq (J.pre y) y rfl hy hlt hyx).elim
    · by_cases heq : J.pre q = J.pre y
      · have : q = y := hv.pre_inj q y hqn hy heq
        subst this
        exact ⟨x, hx, hq⟩
      · exact ih (J.pre q) (by omega) q rfl hqn (by omega)

/-- Under the extremal hypothesis, a vertex with a parent and a child heads a loop. -/
theorem header_of_chain (hv : J.Valid g r) (hE : MaxPairs g J) {p v c : Nat} (hcn : c < g.n)
    (hvc : J.IsParent g v c) (hpv : J.IsParent g p v) : g.IsHeader J v := by
  have hpn := hpv.1
  have hvn := hvc.1
  have hpc : J.pre p < J.pre c :=
    Nat.lt_trans (hv.parent_nested hpn hvn hpv).1 (hv.parent_nested hvn hcn hvc).1
  have hpcA : J.Anc p c := hpv.2.2.1.trans hvc.2.2.1
  have hnpar : ¬ J.IsParent g p c := by
    intro h
    have h1 : J.Anc v p := h.2.2.2 v hvn hvc.2.1 hvc.2.2.1
    exact hpv.2.1 (hv.anc_antisymm hpn hvn hpv.2.2.1 h1)
  rcases hE p c hpn hcn hpc hnpar with hm | hm
  · obtain ⟨-, w, hw, hwc, hnw⟩ := hm
    have hwa := Digraph.Body.anc hw
    have hwn := hw.1.lt g J
    have hwv : J.Anc w v := hvc.2.2.2 w hwn (Ne.symm hwc) hwa
    by_cases e : w = v
    · subst e; exact hw.1
    · exact absurd (hpv.2.2.2 w hwn e hwv) hnw
  · obtain ⟨-, w, hw, hwp, hnw⟩ := hm
    exact absurd (Digraph.Body.anc hw |>.trans hpcA) hnw

theorem sum_le_of_le (f h : Nat → Nat) : ∀ l : List Nat, (∀ b ∈ l, f b ≤ h b) → (l.map f).sum ≤ (l.map h).sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h'
    simp only [List.map_cons, List.sum_cons]
    have := h' a List.mem_cons_self
    have := ih (fun c hc => h' c (List.mem_cons_of_mem _ hc))
    omega

open Classical in
/-- In-degree bound at a vertex: besides its multiple-entry in-edges, the tree edge, and for a vertex that is neither
last in preorder nor the root also a back edge, enter it. -/
theorem indeg_bound (hv : J.Valid g r) (hE : MaxPairs g J) {y l : Nat} (hy : y < g.n) (hl : l < g.n)
    (hmax : ∀ v, v < g.n → J.pre v ≤ J.pre l) :
    (if y = r then 0 else 1) + (if y = r ∨ y = l then 0 else 1) +
      ((List.range g.n).filter fun x => decide (g.IsMEE J x y)).length ≤
    ((List.range g.n).filter fun x => decide (g.edge x y)).length := by
  have hsplit : ((List.range g.n).filter fun x => decide (g.edge x y)).length =
      ((List.range g.n).filter fun x => decide (g.IsMEE J x y)).length +
      ((List.range g.n).filter fun x => decide (g.edge x y ∧ ¬ g.IsMEE J x y)).length := by
    apply filter_len_split
    intro a _
    by_cases h1 : g.edge a y <;> by_cases h2 : g.IsMEE J a y
    · left; simp [h1, h2]
    · right; left; simp [h1, h2]
    · exact (h1 h2.1).elim
    · right; right; simp [h1, h2]
  rw [hsplit]
  have hmem : ∀ x, x ∈ ((List.range g.n).filter fun x => decide (g.edge x y ∧ ¬ g.IsMEE J x y)) ↔
      (x < g.n ∧ g.edge x y ∧ ¬ g.IsMEE J x y) := by
    intro x; simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  by_cases hyr : y = r
  · simp [hyr]
  · obtain ⟨p, hp, hpe⟩ := hv.parent y hy hyr
    have hpmem : p ∈ ((List.range g.n).filter fun x => decide (g.edge x y ∧ ¬ g.IsMEE J x y)) :=
      (hmem p).2 ⟨hp.1, hpe, fun h => (Jungle.Valid.mee_not_parent h).1 hp⟩
    by_cases hyl : y = l
    · have h1 : 1 ≤ ((List.range g.n).filter fun x => decide (g.edge x y ∧ ¬ g.IsMEE J x y)).length :=
        List.length_pos_of_mem hpmem
      rw [if_neg hyr, if_pos (Or.inr hyl)]
      omega
    · have hlt : J.pre y < J.pre l := by
        have h1 := hmax y hy
        have h2 : J.pre y ≠ J.pre l := fun e => hyl (hv.pre_inj y l hy hl e)
        omega
      obtain ⟨c, hcn, hc⟩ := child_exists hv hE hy (J.pre l) l rfl hl hlt
      have hhd : g.IsHeader J y := header_of_chain hv hE hcn hc hp
      obtain ⟨t, hte, hta⟩ := hhd
      have htmem : t ∈ ((List.range g.n).filter fun x => decide (g.edge x y ∧ ¬ g.IsMEE J x y)) := by
        refine (hmem t).2 ⟨hte.1, hte, ?_⟩
        rintro ⟨-, w, hw, hwy, hnw⟩
        exact hnw ((Digraph.Body.anc hw).trans hta)
      have hne : p ≠ t := by
        intro e
        subst e
        exact hp.2.1 (hv.anc_antisymm hp.1 hy hp.2.2.1 hta)
      have h2 : 2 ≤ ((List.range g.n).filter fun x => decide (g.edge x y ∧ ¬ g.IsMEE J x y)).length := by
        have hnd : ([p, t] : List Nat).Nodup := List.nodup_cons.2 ⟨by simp [hne], List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩⟩
        have hsub : ([p, t] : List Nat) ⊆ ((List.range g.n).filter fun x => decide (g.edge x y ∧ ¬ g.IsMEE J x y)) := by
          intro a ha
          rcases List.mem_cons.1 ha with rfl | ha
          · exact hpmem
          · rw [List.mem_singleton.1 ha]; exact htmem
        exact List.Nodup.length_le_of_subset hnd hsub
      have e1 : ¬ (y = r ∨ y = l) := by simp [hyr, hyl]
      rw [if_neg hyr, if_neg e1]
      omega

open Classical in
/-- P15, second half (G19): a CFG with the maximal number `C(n−1,2)` of multiple-entry edges has at least `2n−3` other
edges, for every depth-first jungle. -/
theorem maxMEE_others (hcfg : g.IsCFG r) (hv : J.Valid g r) (hn : 2 ≤ g.n)
    (hmax : 2 * g.meeCount J = (g.n - 1) * (g.n - 2)) : g.meeCount J + (2 * g.n - 3) ≤ g.edgeCount := by
  have hE := maxPairs_of_max hcfg hv hmax
  obtain ⟨l, hl, hlmax⟩ := exists_max_pre J g.n (by omega)
  have hr := hcfg.1
  have hrl : r ≠ l := by
    intro e
    subst e
    obtain ⟨v, hvn, hvr⟩ : ∃ v, v < g.n ∧ v ≠ r := by
      by_cases h0 : r = 0
      · exact ⟨1, by omega, by omega⟩
      · exact ⟨0, by omega, by omega⟩
    have h1 := hv.root v hvn
    have h2 := hlmax v hvn
    have h3 : J.pre r ≠ J.pre v := fun e => hvr (hv.pre_inj v r hvn hr e.symm)
    unfold Jungle.Anc at h1
    omega
  have hite1 : ((List.range g.n).map fun b => if b = r then 0 else 1).sum = g.n - 1 := by
    have := count_ne g.n r hr
    rw [count_eq_sum] at this
    rw [← this]
    apply congrArg List.sum; apply List.map_congr_left; intro b _
    by_cases h : b = r <;> simp [h]
  have hite2 : ((List.range g.n).map fun b => if b = r ∨ b = l then 0 else 1).sum = g.n - 2 := by
    have := count_ne2 g.n r l hrl
    simp only [hr, hl, ↓reduceIte] at this
    rw [count_eq_sum] at this
    have e : ((List.range g.n).map fun b => if b = r ∨ b = l then 0 else 1).sum =
        ((List.range g.n).map fun a => if decide (a ≠ r ∧ a ≠ l) = true then 1 else 0).sum := by
      apply congrArg List.sum; apply List.map_congr_left; intro b _
      by_cases h : b = r ∨ b = l
      · have h' : ¬ (b ≠ r ∧ b ≠ l) := by omega
        simp [h, h']
      · have h' : b ≠ r ∧ b ≠ l := by omega
        simp [h, h']
    rw [e]
    omega
  have hle : ((List.range g.n).map fun y => (if y = r then 0 else 1) + (if y = r ∨ y = l then 0 else 1) +
      ((List.range g.n).filter fun x => decide (g.IsMEE J x y)).length).sum ≤
      ((List.range g.n).map fun y => ((List.range g.n).filter fun x => decide (g.edge x y)).length).sum :=
    sum_le_of_le _ _ _ (fun y hy => indeg_bound hv hE (List.mem_range.1 hy) hl hlmax)
  rw [sum_map_add, sum_map_add, hite1, hite2] at hle
  have hec : g.edgeCount = ((List.range g.n).map fun y => ((List.range g.n).filter fun x => decide (g.edge x y)).length).sum := by
    have h1 : g.edgeCount = ((List.range g.n).map fun x => ((List.range g.n).filter fun y =>
        @decide (g.edge x y) (Classical.propDecidable _)).length).sum := by
      unfold Digraph.edgeCount
      apply congrArg List.sum; apply List.map_congr_left; intro x _
      exact congrArg List.length (List.filter_congr (fun y _ => by simp only [decide_eq_decide]))
    rw [h1, ← swap_count g.n g.edge]
    apply congrArg List.sum; apply List.map_congr_left; intro y _
    exact congrArg List.length (List.filter_congr (fun x _ => by simp only [decide_eq_decide]))
  have hmc : g.meeCount J = ((List.range g.n).map fun y => ((List.range g.n).filter fun x => decide (g.IsMEE J x y)).length).sum := by
    unfold Digraph.meeCount
    apply congrArg List.sum; apply List.map_congr_left; intro y _
    exact congrArg List.length (List.filter_congr (fun x _ => by simp only [decide_eq_decide]))
  omega

end SmcIrred
