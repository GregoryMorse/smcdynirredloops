module

public import SmcIrred.LNF.Algo

public section

namespace SmcIrred

theorem insDesc_perm (key : Nat → Nat) (a : Nat) : ∀ l : List Nat, (insDesc key a l).Perm (a :: l) := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons b l ih =>
    unfold insDesc
    by_cases h : key b ≤ key a
    · simp only [h, ↓reduceIte]; exact List.Perm.refl _
    · simp only [h, ↓reduceIte]
      exact ((ih.cons b).trans (List.Perm.swap a b l))

theorem insDesc_sorted (key : Nat → Nat) (a : Nat) : ∀ l : List Nat, l.Pairwise (fun x y => key y ≤ key x) →
    (insDesc key a l).Pairwise (fun x y => key y ≤ key x) := by
  intro l
  induction l with
  | nil => intro _; simp [insDesc]
  | cons b l ih =>
    intro hl
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 hl
    unfold insDesc
    by_cases h : key b ≤ key a
    · simp only [h, ↓reduceIte]
      refine List.pairwise_cons.2 ⟨?_, hl⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact h
      · exact Nat.le_trans (h1 y hy) h
    · simp only [h, ↓reduceIte]
      have hs := ih h2
      refine List.pairwise_cons.2 ⟨?_, hs⟩
      intro y hy
      have : y ∈ a :: l := (insDesc_perm key a l).mem_iff.1 hy
      rcases List.mem_cons.1 this with rfl | hy
      · omega
      · exact h1 y hy

theorem byPreDesc_perm (J : Jungle) (n : Nat) : (byPreDesc J n).Perm (List.range n) := by
  unfold byPreDesc
  have key : ∀ l : List Nat, (l.foldr (insDesc J.pre) []).Perm l := by
    intro l
    induction l with
    | nil => exact List.Perm.refl _
    | cons a l ih => exact (insDesc_perm J.pre a _).trans (ih.cons a)
  exact key _

theorem byPreDesc_sorted (J : Jungle) (n : Nat) : (byPreDesc J n).Pairwise (fun x y => J.pre y ≤ J.pre x) := by
  unfold byPreDesc
  have key : ∀ l : List Nat, (l.foldr (insDesc J.pre) []).Pairwise (fun x y => J.pre y ≤ J.pre x) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => exact insDesc_sorted J.pre a _ ih
  exact key _

/-- The processing order: every vertex once, strictly decreasing preorder number (the preorder numbers of the
vertices are distinct). -/
theorem byPreDesc_strict (J : Jungle) (n : Nat) (hinj : ∀ a b, a < n → b < n → J.pre a = J.pre b → a = b) :
    (byPreDesc J n).Pairwise (fun x y => J.pre y < J.pre x) := by
  have hnd : (byPreDesc J n).Nodup := (byPreDesc_perm J n).nodup_iff.2 (List.nodup_range)
  have hmem : ∀ x ∈ byPreDesc J n, x < n := fun x hx => List.mem_range.1 ((byPreDesc_perm J n).mem_iff.1 hx)
  have h1 := byPreDesc_sorted J n
  have h2 := List.Pairwise.and hnd h1
  refine List.Pairwise.imp_of_mem ?_ h2
  intro a b ha hb ⟨hne, hle⟩
  have : J.pre b ≠ J.pre a := fun e => hne (hinj a b (hmem a ha) (hmem b hb) e.symm)
  omega

theorem mem_byPreDesc (J : Jungle) (n x : Nat) : x ∈ byPreDesc J n ↔ x < n := by
  rw [(byPreDesc_perm J n).mem_iff, List.mem_range]

end SmcIrred
