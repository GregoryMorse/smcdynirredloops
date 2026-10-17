module

public import SmcIrred.Graph.DfsStep

public section

namespace SmcIrred

variable {g : Digraph} {v : Nat} {s1 : DfsState} {done : List Nat} {sk : DfsState} {fuel : Nat}

theorem Loop.undisc_le (hL : Loop g v s1 done sk) : sk.undisc g ≤ s1.undisc g := by
  refine _root_.SmcIrred.undisc_le ?_
  intro x hx
  by_cases hn : s1.New sk x
  · exact absurd hn.1 hx
  · have := (hL.unchanged x hn).1
    rw [this]; exact hx

theorem foldl_loop (hvn : v < g.n) (hfuel : s1.undisc g ≤ fuel)
    (ih : ∀ w sc, w < g.n → sc.pre w = 0 → sc.Wf → sc.undisc g ≤ fuel → Done g w sc (dfsVisit g fuel w sc)) :
    ∀ (l done : List Nat) (sk : DfsState), (∀ w ∈ l, w ∈ g.succ v) → Loop g v s1 done sk →
      Loop g v s1 (done ++ l)
        (l.foldl (fun s w => if w < g.n ∧ s.pre w = 0 then dfsVisit g fuel w s else s) sk) := by
  intro l
  induction l with
  | nil => intro done sk _ hL; simpa using hL
  | cons a l ihl =>
    intro done sk hmem hL
    have h1 := hL.step (hmem a (List.mem_cons_self ..)) hvn (Nat.le_trans hL.undisc_le hfuel) ih
    have := ihl (done ++ [a]) _ (fun w hw => hmem w (List.mem_cons_of_mem _ hw)) h1
    simpa [List.foldl_cons, List.append_assoc] using this

theorem Wf.opening {s : DfsState} (h : s.Wf) {v : Nat} (h0 : s.pre v = 0) : (s.opening v).Wf where
  clock := by show 1 ≤ s.clock + 1; omega
  pre_lt := by
    intro x; have := h.pre_lt x; simp only [DfsState.opening]; split <;> omega
  post_lt := by
    intro x; have := h.post_lt x; simp only [DfsState.opening]; omega
  post_pre := by
    intro x hx
    simp only [DfsState.opening] at hx ⊢
    have := h.post_pre x hx
    by_cases hxv : x = v
    · subst hxv; omega
    · simp [hxv]; exact this

end SmcIrred
