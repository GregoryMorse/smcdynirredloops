module

public import SmcIrred.Tarjan.Finish

public section

namespace SmcIrred

variable {g : Digraph}

/-- What a run of the algorithm preserves: visited vertices keep their index, new vertices get larger indices, emitted
components stay. -/
structure TCore (s t : TState) : Prop where
  num_eq : ∀ w, s.num w ≠ 0 → t.num w = s.num w
  out_ext : ∃ R, t.out = s.out ++ R
  cnt_le : s.cnt ≤ t.cnt
  num_new : ∀ w, s.num w = 0 → t.num w ≠ 0 → s.cnt < t.num w

/-- `TCore` together with: the stack only grows on top. -/
structure TMono (s t : TState) : Prop extends TCore s t where
  stk_ext : ∃ N, t.stk = N ++ s.stk

theorem TCore.refl (s : TState) : TCore s s :=
  ⟨fun _ _ => rfl, ⟨[], by simp⟩, Nat.le_refl _, fun w h1 h2 => absurd h1 h2⟩

theorem TCore.trans {s t u : TState} (h1 : TCore s t) (h2 : TCore t u) : TCore s u where
  num_eq w hw := by
    rw [h2.num_eq w (by rw [h1.num_eq w hw]; exact hw), h1.num_eq w hw]
  out_ext := by
    obtain ⟨R1, e1⟩ := h1.out_ext
    obtain ⟨R2, e2⟩ := h2.out_ext
    exact ⟨R1 ++ R2, by rw [e2, e1, List.append_assoc]⟩
  cnt_le := Nat.le_trans h1.cnt_le h2.cnt_le
  num_new w hs hu := by
    by_cases ht : t.num w = 0
    · exact Nat.lt_of_le_of_lt h1.cnt_le (h2.num_new w ht hu)
    · have := h1.num_new w hs ht
      rw [h2.num_eq w ht] at hu ⊢
      exact this

theorem TMono.refl (s : TState) : TMono s s := ⟨TCore.refl s, ⟨[], by simp⟩⟩

theorem TMono.trans {s t u : TState} (h1 : TMono s t) (h2 : TMono t u) : TMono s u where
  toTCore := h1.toTCore.trans h2.toTCore
  stk_ext := by
    obtain ⟨N1, e1⟩ := h1.stk_ext
    obtain ⟨N2, e2⟩ := h2.stk_ext
    exact ⟨N2 ++ N1, by rw [e2, e1, List.append_assoc]⟩

theorem TMono.of_fields {s t : TState} (hn : t.num = s.num) (ho : t.out = s.out) (hs : t.stk = s.stk)
    (hc : t.cnt = s.cnt) : TMono s t where
  num_eq w _ := by rw [hn]
  out_ext := ⟨[], by simp [ho]⟩
  cnt_le := by rw [hc]; exact Nat.le_refl _
  num_new w h1 h2 := by rw [hn] at h2; exact absurd h1 h2
  stk_ext := ⟨[], by simp [hs]⟩

theorem TInv.tick {P : List Nat} {s : TState} (h : TInv g P s) (t : Nat) : TInv g P { s with ticks := t } :=
  ⟨h.stk_lt, h.done_lt, h.vis_iff, h.disj, h.stk_nodup, h.out_nodup, h.num_le, h.P_sub, h.P_sorted, h.reach_P,
    h.closed_out, h.scc_out, h.low_le, h.low_wit, h.fin_low, h.low_min, h.fin_edge, h.fin_vis⟩

/-- With an empty path the stack is empty. -/
theorem TInv.stk_nil {s : TState} (h : TInv g [] s) : s.stk = [] := by
  have key : ∀ m, ∀ w ∈ s.stk, s.num w = m → False := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro w hw hm
      have hl := h.fin_low w hw (by simp)
      obtain ⟨y, hy, hny, -⟩ := h.low_wit w hw hl
      exact ih (s.num y) (by omega) y hy rfl
  rw [List.eq_nil_iff_forall_not_mem]
  intro w hw
  exact key _ w hw rfl

/-- The number of unvisited vertices among `0 … k-1`. -/
@[expose] def tUn (s : TState) : Nat → Nat
  | 0 => 0
  | k + 1 => tUn s k + (if s.num k = 0 then 1 else 0)

theorem tUn_mono {s t : TState} (hm : ∀ w, s.num w ≠ 0 → t.num w ≠ 0) : ∀ k, tUn t k ≤ tUn s k := by
  intro k
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    show tUn t k + (if t.num k = 0 then 1 else 0) ≤ tUn s k + (if s.num k = 0 then 1 else 0)
    by_cases h1 : t.num k = 0
    · have h2 : s.num k = 0 := by
        by_cases h2 : s.num k = 0
        · exact h2
        · exact absurd h1 (hm k h2)
      simp [h1, h2]; omega
    · by_cases h2 : s.num k = 0 <;> simp [h1, h2] <;> omega

theorem tUn_lt {s t : TState} (hm : ∀ w, s.num w ≠ 0 → t.num w ≠ 0) {v : Nat} (hs : s.num v = 0) (ht : t.num v ≠ 0) :
    ∀ k, v < k → tUn t k < tUn s k := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hk
    show tUn t k + (if t.num k = 0 then 1 else 0) < tUn s k + (if s.num k = 0 then 1 else 0)
    by_cases e : v = k
    · subst e
      have := tUn_mono hm v
      simp [hs, ht]; omega
    · have := ih (by omega)
      by_cases h1 : t.num k = 0
      · have h2 : s.num k = 0 := by
          by_cases h2 : s.num k = 0
          · exact h2
          · exact absurd h1 (hm k h2)
        simp [h1, h2]; omega
      · by_cases h2 : s.num k = 0 <;> simp [h1, h2] <;> omega

theorem tUn_pos {s : TState} {v k : Nat} (hv : v < k) (hs : s.num v = 0) : 0 < tUn s k := by
  induction k with
  | zero => omega
  | succ k ih =>
    show 0 < tUn s k + (if s.num k = 0 then 1 else 0)
    by_cases e : v = k
    · subst e; simp [hs]
    · have := ih (by omega); omega

theorem tUn_le (s : TState) : ∀ k, tUn s k ≤ k := by
  intro k
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    show tUn s k + (if s.num k = 0 then 1 else 0) ≤ k + 1
    by_cases h : s.num k = 0 <;> simp [h] <;> omega

end SmcIrred
