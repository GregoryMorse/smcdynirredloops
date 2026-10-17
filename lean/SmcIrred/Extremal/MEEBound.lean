module

public import SmcIrred.Extremal.Count2
public import SmcIrred.Extremal.IrrBound

public section

namespace SmcIrred

/-- The number of vertices discovered before `b`. -/
@[expose] def earlier (J : Jungle) (n b : Nat) : Nat := ((List.range n).filter fun a => decide (J.pre a < J.pre b)).length

theorem earlier_sum (J : Jungle) (n : Nat) (hinj : ∀ a b, a < n → b < n → J.pre a = J.pre b → a = b) :
    2 * ((List.range n).map fun b => earlier J n b).sum + n = n * n := by
  have key : ∀ b, b < n → earlier J n b + ((List.range n).filter fun a => decide (J.pre b < J.pre a)).length + 1 = n := by
    intro b hb
    unfold earlier
    have h1 : ((List.range n).filter fun a => decide (a = b)).length = 1 := by
      refine Eq.trans (congrArg List.length (List.filter_congr (q := fun a => decide (b ≤ a ∧ a < b + 1)) ?_)) ?_
      · intro a _; simp only [decide_eq_decide]; omega
      · rw [count_interval]; omega
    have h3 := filter_len_three (l := List.range n) (p := fun a => decide (J.pre a < J.pre b))
      (q := fun a => decide (J.pre b < J.pre a)) (r := fun a => decide (a = b)) (by
        intro a ha
        have ha := List.mem_range.1 ha
        have hi := hinj a b ha hb
        have hf : a = b → J.pre a = J.pre b := fun e => by rw [e]
        simp only [decide_eq_true_eq, decide_eq_false_iff_not]
        omega)
    rw [h1, List.length_range] at h3
    omega
  have hlater : ((List.range n).map fun b => ((List.range n).filter fun a => decide (J.pre b < J.pre a)).length).sum =
      ((List.range n).map fun b => earlier J n b).sum := by
    have := swap_count n (fun x y => J.pre y < J.pre x)
    refine Eq.trans ?_ (Eq.trans this ?_)
    · apply congrArg List.sum; apply List.map_congr_left; intro y _
      exact congrArg List.length (List.filter_congr (fun x _ => by simp only [decide_eq_decide]))
    · apply congrArg List.sum; apply List.map_congr_left; intro x _
      exact congrArg List.length (List.filter_congr (fun y _ => by simp only [decide_eq_decide]))
  have hs : ((List.range n).map fun b => earlier J n b + ((List.range n).filter fun a => decide (J.pre b < J.pre a)).length + 1).sum
      = ((List.range n).map fun _ => n).sum := by
    apply congrArg List.sum; apply List.map_congr_left; intro b hb
    exact key b (List.mem_range.1 hb)
  rw [sum_map_add, sum_map_add, hlater, sum_map_const, sum_map_const] at hs
  have e : List.map (earlier J n) (List.range n) = List.map (fun b => earlier J n b) (List.range n) := rfl
  rw [e] at hs
  omega

variable {g : Digraph} {r : Nat} {J : Jungle}

theorem Digraph.IsMEE.ne {x y : Nat} (h : g.IsMEE J x y) : x ≠ y := by
  obtain ⟨-, w, hb, -, hn⟩ := h
  rintro rfl
  exact hn (Digraph.Body.anc hb)

/-- No pair of vertices carries multiple-entry edges in both directions (a DFS has no edge to the right). -/
theorem Jungle.Valid.mee_excl (h : J.Valid g r) {a b : Nat} (h1 : g.IsMEE J a b) (h2 : g.IsMEE J b a) : False := by
  obtain ⟨hab, w, hw, hbw, hnw⟩ := h1
  obtain ⟨hba, w', hw', haw', hnw'⟩ := h2
  have hbA := Digraph.Body.anc hw
  have haA := Digraph.Body.anc hw'
  have wl := hw.1.lt g J
  have wl' := hw'.1.lt g J
  rcases h.laminar w w' wl wl' with c | c | c | c
  · exact hnw (c.trans haA)
  · exact hnw' (c.trans hbA)
  · have h3 := h.no_rightward b a hba
    unfold Jungle.Anc at hbA haA
    omega
  · have h3 := h.no_rightward a b hab
    unfold Jungle.Anc at hbA haA
    omega

/-- Tree edges never carry multiple-entry edges (in either direction): a tree edge joins a vertex to its innermost
ancestor. -/
theorem Jungle.Valid.mee_not_parent {x y : Nat} (hm : g.IsMEE J x y) :
    ¬ J.IsParent g x y ∧ ¬ J.IsParent g y x := by
  obtain ⟨he, w, hb, hy, hn⟩ := hm
  refine ⟨fun hp => hn (hp.2.2.2 w (hb.1.lt g J) (Ne.symm hy) (Digraph.Body.anc hb)), fun hp => hn ?_⟩
  exact (Digraph.Body.anc hb).trans hp.2.2.1

/-- Multiple-entry edges into `b` from earlier vertices. -/
@[expose] def meeA (g : Digraph) (J : Jungle) (b : Nat) : Nat :=
  ((List.range g.n).filter fun x => decide (g.IsMEE J x b ∧ J.pre x < J.pre b)).length

/-- Multiple-entry edges out of `b` into earlier vertices. -/
@[expose] def meeC (g : Digraph) (J : Jungle) (b : Nat) : Nat :=
  ((List.range g.n).filter fun y => decide (g.IsMEE J b y ∧ J.pre y < J.pre b)).length

theorem per_vertex (hv : J.Valid g r) {b : Nat} (hb : b < g.n) :
    meeA g J b + meeC g J b + (if b = r then 0 else 1) ≤ earlier J g.n b := by
  have hd : ∀ a ∈ List.range g.n, ¬ (decide (g.IsMEE J a b ∧ J.pre a < J.pre b) = true ∧
      decide (g.IsMEE J b a ∧ J.pre a < J.pre b) = true) := by
    intro a _ ⟨h1, h2⟩
    simp only [decide_eq_true_eq] at h1 h2
    exact hv.mee_excl h1.1 h2.1
  by_cases hbr : b = r
  · subst hbr
    have h1 := filter_len_add_le (l := List.range g.n) (p := fun x => decide (g.IsMEE J x b ∧ J.pre x < J.pre b))
      (q := fun y => decide (g.IsMEE J b y ∧ J.pre y < J.pre b)) (r := fun a => decide (J.pre a < J.pre b))
      (fun a _ h => by simp only [decide_eq_true_eq] at h ⊢; exact h.2)
      (fun a _ h => by simp only [decide_eq_true_eq] at h ⊢; exact h.2) hd
    unfold meeA meeC earlier
    simp only [↓reduceIte]
    omega
  · obtain ⟨p, hp, -⟩ := hv.parent b hb hbr
    have hpn : p < g.n := hp.1
    have hlt := hv.parent_nested hpn hb hp
    have h1 := filter_len_add_le (l := List.range g.n) (p := fun x => decide (g.IsMEE J x b ∧ J.pre x < J.pre b))
      (q := fun y => decide (g.IsMEE J b y ∧ J.pre y < J.pre b))
      (r := fun a => decide (J.pre a < J.pre b ∧ a ≠ p))
      (fun a _ h => by
        simp only [decide_eq_true_eq] at h ⊢
        refine ⟨h.2, fun e => ?_⟩
        subst e
        exact (Jungle.Valid.mee_not_parent h.1).1 hp)
      (fun a _ h => by
        simp only [decide_eq_true_eq] at h ⊢
        refine ⟨h.2, fun e => ?_⟩
        subst e
        exact (Jungle.Valid.mee_not_parent h.1).2 hp) hd
    have h2 := filter_len_lt (l := List.range g.n) (p := fun a => decide (J.pre a < J.pre b ∧ a ≠ p))
      (q := fun a => decide (J.pre a < J.pre b)) (v := p)
      (fun a h => by simp only [decide_eq_true_eq] at h ⊢; exact h.1) (List.mem_range.2 hpn)
      (by simp) (by simp only [decide_eq_true_eq]; exact hlt.1)
    unfold meeA meeC earlier
    simp only [hbr, ↓reduceIte]
    omega

theorem meeCount_decomp (hv : J.Valid g r) :
    g.meeCount J = ((List.range g.n).map fun b => meeA g J b + meeC g J b).sum := by
  unfold Digraph.meeCount
  have step1 : ∀ y ∈ List.range g.n, ((List.range g.n).filter fun x =>
      @decide (g.IsMEE J x y) (Classical.propDecidable _)).length =
      meeA g J y + ((List.range g.n).filter fun x => decide (g.IsMEE J x y ∧ J.pre y < J.pre x)).length := by
    intro y hy
    have hy := List.mem_range.1 hy
    refine Eq.trans (congrArg List.length (List.filter_congr (q := fun x => decide (g.IsMEE J x y)) ?_)) ?_
    · intro x _; simp only [decide_eq_decide]
    · apply filter_len_split
      intro x hx
      have hx := List.mem_range.1 hx
      by_cases hm : g.IsMEE J x y
      · have hne : x ≠ y := Digraph.IsMEE.ne hm
        have hp : J.pre x ≠ J.pre y := fun e => hne (hv.pre_inj x y hx hy e)
        by_cases hl : J.pre x < J.pre y
        · left; simp [hm, hl]; omega
        · right; left; simp [hm, hl]; omega
      · right; right; simp [hm]
  have step2 := swap_count g.n (fun x y => g.IsMEE J x y ∧ J.pre y < J.pre x)
  have e3 : ((List.range g.n).map fun y => ((List.range g.n).filter fun x =>
      @decide (g.IsMEE J x y ∧ J.pre y < J.pre x) (Classical.propDecidable _)).length) =
      (List.range g.n).map fun y => ((List.range g.n).filter fun x => decide (g.IsMEE J x y ∧ J.pre y < J.pre x)).length := by
    apply List.map_congr_left; intro y _
    exact congrArg List.length (List.filter_congr (fun x _ => by simp only [decide_eq_decide]))
  have e4 : ((List.range g.n).map fun x => ((List.range g.n).filter fun y =>
      @decide (g.IsMEE J x y ∧ J.pre y < J.pre x) (Classical.propDecidable _)).length) =
      (List.range g.n).map fun x => meeC g J x := by
    apply List.map_congr_left; intro x _
    exact congrArg List.length (List.filter_congr (fun y _ => by simp only [decide_eq_decide]))
  rw [e3, e4] at step2
  refine Eq.trans (congrArg List.sum (List.map_congr_left step1)) ?_
  rw [sum_map_add, sum_map_add]
  have e5 : ((List.range g.n).map fun y => ((List.range g.n).filter fun x => decide (g.IsMEE J x y ∧ J.pre y < J.pre x)).length) =
      ((List.range g.n).map fun y => ((List.range g.n).filter fun x => decide (g.IsMEE J x y ∧ J.pre y < J.pre x)).length) := rfl
  rw [step2]

theorem meeCount_bound (hcfg : g.IsCFG r) (hv : J.Valid g r) :
    2 * g.meeCount J + 2 * (g.n - 1) + g.n ≤ g.n * g.n := by
  rw [meeCount_decomp hv]
  have hsum : ((List.range g.n).map fun b => meeA g J b + meeC g J b + (if b = r then 0 else 1)).sum ≤
      ((List.range g.n).map fun b => earlier J g.n b).sum := by
    have : ∀ (l : List Nat), (∀ b ∈ l, b < g.n) →
        (l.map fun b => meeA g J b + meeC g J b + (if b = r then 0 else 1)).sum ≤ (l.map fun b => earlier J g.n b).sum := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons a l ih =>
        intro h
        simp only [List.map_cons, List.sum_cons]
        have := per_vertex hv (h a (List.mem_cons_self ..))
        have := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
        omega
    exact this _ (fun b hb => List.mem_range.1 hb)
  rw [sum_map_add] at hsum
  have hite : ((List.range g.n).map fun b => if b = r then 0 else 1).sum = g.n - 1 := by
    have := count_ne g.n r hcfg.1
    rw [count_eq_sum] at this
    rw [← this]
    apply congrArg List.sum; apply List.map_congr_left; intro b _
    by_cases h : b = r <;> simp [h]
  rw [hite] at hsum
  have hT := earlier_sum J g.n (fun a b ha hb => hv.pre_inj a b ha hb)
  have e : List.map (fun b => earlier J g.n b) (List.range g.n) = List.map (earlier J g.n) (List.range g.n) := rfl
  omega

/-- For every CFG and every depth-first jungle the number of multiple-entry edges is at most `(n−1)(n−2)/2` (stated as
twice the count): `K_n` attains the bound. -/
theorem meeCount_le (hcfg : g.IsCFG r) (hv : J.Valid g r) : 2 * g.meeCount J ≤ (g.n - 1) * (g.n - 2) := by
  have h := meeCount_bound hcfg hv
  have hr := hcfg.1
  generalize g.meeCount J = M at h ⊢
  generalize g.n = n at h hr ⊢
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e : m + 1 - 1 = m := by omega
  rw [e] at h ⊢
  rcases m with _ | m
  · simp at h ⊢; omega
  · have e2 : m + 1 + 1 - 2 = m := by omega
    rw [e2]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at h ⊢
    omega

end SmcIrred
