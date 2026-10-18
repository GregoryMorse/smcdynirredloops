module

public import SmcIrred.LNF.HvOrder

public section

namespace SmcIrred

/-- The number of vertices with a smaller preorder number: a rank that bounds union-find chains. -/
@[expose] def pcnt (J : Jungle) (n x : Nat) : Nat := ((List.range n).filter fun u => decide (J.pre u < J.pre x)).length

theorem pcnt_le (J : Jungle) (n x : Nat) : pcnt J n x ≤ n := by
  unfold pcnt
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem pcnt_lt (J : Jungle) (n : Nat) {a b : Nat} (ha : a < n) (hab : J.pre a < J.pre b) : pcnt J n a < pcnt J n b := by
  unfold pcnt
  have hnd : ((List.range n).filter fun u => decide (J.pre u < J.pre a)).Nodup := List.Pairwise.filter _ List.nodup_range
  have hna : a ∉ ((List.range n).filter fun u => decide (J.pre u < J.pre a)) := by simp
  have hsub : (a :: ((List.range n).filter fun u => decide (J.pre u < J.pre a))) ⊆
      ((List.range n).filter fun u => decide (J.pre u < J.pre b)) := by
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · simp [ha, hab]
    · simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hu ⊢
      exact ⟨hu.1, by omega⟩
  have := List.Nodup.length_le_of_subset (List.nodup_cons.2 ⟨hna, hnd⟩) hsub
  simp only [List.length_cons] at this
  omega

/-- Pointers go to smaller preorder numbers. -/
@[expose] def UfChain (J : Jungle) (n : Nat) (uf : Nat → Nat) : Prop :=
  ∀ x, uf x ≠ x → uf x < n ∧ J.pre (uf x) < J.pre x

theorem find_zero (uf : Nat → Nat) (v : Nat) : ufFind uf 0 v = v := rfl

theorem find_of_root (uf : Nat → Nat) (v : Nat) (h : uf v = v) : ∀ f, ufFind uf f v = v := by
  intro f
  cases f with
  | zero => rfl
  | succ f => simp [ufFind, h]

theorem find_succ_ne (uf : Nat → Nat) (v f : Nat) (h : uf v ≠ v) : ufFind uf (f + 1) v = ufFind uf f (uf v) := by
  simp [ufFind, h]

theorem find_root {J : Jungle} {n : Nat} {uf : Nat → Nat} (hch : UfChain J n uf) :
    ∀ f x, x < n → pcnt J n x ≤ f → uf (ufFind uf f x) = ufFind uf f x ∧ ufFind uf f x < n := by
  intro f
  induction f with
  | zero =>
    intro x hx hc
    have hr : uf x = x := by
      apply Classical.byContradiction
      intro hne
      obtain ⟨h1, h2⟩ := hch x hne
      have := pcnt_lt J n h1 h2
      omega
    rw [find_zero]
    exact ⟨hr, hx⟩
  | succ f ih =>
    intro x hx hc
    by_cases hr : uf x = x
    · rw [find_of_root uf x hr]
      exact ⟨hr, hx⟩
    · obtain ⟨h1, h2⟩ := hch x hr
      have := pcnt_lt J n h1 h2
      rw [find_succ_ne uf x f hr]
      exact ih (uf x) h1 (by omega)

theorem find_root_n {J : Jungle} {n : Nat} {uf : Nat → Nat} (hch : UfChain J n uf) {x : Nat} (hx : x < n) :
    uf (ufFind uf n x) = ufFind uf n x ∧ ufFind uf n x < n := find_root hch n x hx (pcnt_le J n x)

/-- Updating the roots in `m` to point to the fresh root `w`. -/
theorem find_update {J : Jungle} {n : Nat} {uf : Nat → Nat} (hch : UfChain J n uf) (m : Nat → Bool) (w : Nat)
    (hw : w < n) (hwr : uf w = w) (hmw : m w = false) (hM : ∀ x, m x = true → uf x = x ∧ x < n ∧ J.pre w < J.pre x) :
    ∀ f x, x < n → pcnt J n x ≤ f →
      ufFind (fun x => if m x = true then w else uf x) f x = if m (ufFind uf f x) = true then w else ufFind uf f x := by
  intro f
  induction f with
  | zero =>
    intro x hx hc
    have hmx : m x = false := by
      cases hm : m x
      · rfl
      · obtain ⟨_, _, h3⟩ := hM x hm
        have := pcnt_lt J n hw h3
        omega
    rw [find_zero, find_zero, hmx]
    simp
  | succ f ih =>
    intro x hx hc
    by_cases hr : uf x = x
    · rw [find_of_root uf x hr]
      by_cases hm : m x = true
      · have e : (fun x => if m x = true then w else uf x) x = w := by simp [hm]
        have hne : w ≠ x := by
          obtain ⟨_, _, h3⟩ := hM x hm
          intro e; subst e; omega
        have hne' : (fun x => if m x = true then w else uf x) x ≠ x := by rw [e]; exact hne
        have h3 : ufFind (fun x => if m x = true then w else uf x) (f + 1) x =
            ufFind (fun x => if m x = true then w else uf x) f w := by
          rw [find_succ_ne _ x f hne']; simp [hm]
        have hwr' : (fun x => if m x = true then w else uf x) w = w := by simp [hmw, hwr]
        rw [h3, find_of_root _ w hwr']
        simp [hm]
      · have e : (fun x => if m x = true then w else uf x) x = x := by simp [hm, hr]
        rw [find_of_root _ x e]
        simp [hm]
    · obtain ⟨h1, h2⟩ := hch x hr
      have hm : ¬ m x = true := fun hm => hr (hM x hm).1
      have e : (fun x => if m x = true then w else uf x) x = uf x := by simp [hm]
      have hne' : (fun x => if m x = true then w else uf x) x ≠ x := by rw [e]; exact hr
      have := pcnt_lt J n h1 h2
      have h3 : ufFind (fun x => if m x = true then w else uf x) (f + 1) x =
          ufFind (fun x => if m x = true then w else uf x) f (uf x) := by
        rw [find_succ_ne _ x f hne']; simp [hm]
      rw [h3, find_succ_ne uf x f hr]
      exact ih (uf x) h1 (by omega)

end SmcIrred
