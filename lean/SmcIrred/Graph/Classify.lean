module

public import SmcIrred.Spec.DFS

public section

namespace SmcIrred

variable {g : Digraph} {r : Nat} {J : Jungle}

theorem Jungle.Valid.anc_antisymm (h : J.Valid g r) {a b : Nat} (ha : a < g.n) (hb : b < g.n)
    (hab : J.Anc a b) (hba : J.Anc b a) : a = b :=
  h.pre_inj a b ha hb (by unfold Jungle.Anc at hab hba; omega)

theorem Jungle.Valid.isParent_anc {u v : Nat} (hp : J.IsParent g u v) : J.Anc u v ∧ u ≠ v := ⟨hp.2.2.1, hp.2.1⟩

/-- A tree edge goes to a strict descendant: its timestamps nest strictly. -/
theorem Jungle.Valid.parent_nested (h : J.Valid g r) {u v : Nat} (hu : u < g.n) (hv : v < g.n)
    (hp : J.IsParent g u v) : J.pre u < J.pre v ∧ J.post v < J.post u := by
  have hne := hp.2.1
  have hanc := hp.2.2.1
  unfold Jungle.Anc at hanc
  have h1 : J.pre u ≠ J.pre v := fun e => hne (h.pre_inj u v hu hv e)
  have h2 : J.post u ≠ J.post v := fun e => hne (h.post_inj u v hu hv e)
  omega

/-- Class of a tree-or-forward edge by timestamps (C27). -/
theorem cls_tree_or_forward_iff (h : J.Valid g r) {a b : Nat} (he : g.edge a b) :
    (J.cls g a b = .tree ∨ J.cls g a b = .forward) ↔ J.pre a < J.pre b ∧ J.post b < J.post a := by
  obtain ⟨ha, hb, -⟩ := he
  constructor
  · intro hc
    by_cases hp : J.IsParent g a b
    · exact h.parent_nested ha hb hp
    · by_cases hf : J.pre a < J.pre b ∧ J.post b < J.post a
      · exact hf
      · by_cases hk : J.pre b ≤ J.pre a ∧ J.post a ≤ J.post b
        · simp [Jungle.cls, hp, hf, hk] at hc
        · simp [Jungle.cls, hp, hf, hk] at hc
  · intro hf
    by_cases hp : J.IsParent g a b
    · left; simp [Jungle.cls, hp]
    · right; simp [Jungle.cls, hp, hf]

/-- Class of a back edge by timestamps (C27). -/
theorem cls_back_iff (h : J.Valid g r) {a b : Nat} (he : g.edge a b) :
    J.cls g a b = .back ↔ J.pre b ≤ J.pre a ∧ J.post a ≤ J.post b := by
  obtain ⟨ha, hb, -⟩ := he
  constructor
  · intro hc
    by_cases hp : J.IsParent g a b
    · simp [Jungle.cls, hp] at hc
    · by_cases hf : J.pre a < J.pre b ∧ J.post b < J.post a
      · simp [Jungle.cls, hp, hf] at hc
      · by_cases hk : J.pre b ≤ J.pre a ∧ J.post a ≤ J.post b
        · exact hk
        · simp [Jungle.cls, hp, hf, hk] at hc
  · intro hk
    have hnp : ¬ J.IsParent g a b := by
      intro hp
      have := h.parent_nested ha hb hp
      omega
    have hnf : ¬ (J.pre a < J.pre b ∧ J.post b < J.post a) := by omega
    simp [Jungle.cls, hnp, hnf, hk]

/-- Class of a cross edge by timestamps: it goes to a vertex that finished earlier, right to left (C27). -/
theorem cls_cross_iff (h : J.Valid g r) {a b : Nat} (he : g.edge a b) :
    J.cls g a b = .cross ↔ J.post b < J.pre a := by
  have hnr := h.no_rightward a b he
  obtain ⟨ha, hb, -⟩ := he
  have hab := h.interval a ha
  have hbb := h.interval b hb
  have hlam := h.laminar a b ha hb
  constructor
  · intro hc
    by_cases hp : J.IsParent g a b
    · simp [Jungle.cls, hp] at hc
    · by_cases hf : J.pre a < J.pre b ∧ J.post b < J.post a
      · simp [Jungle.cls, hp, hf] at hc
      · by_cases hk : J.pre b ≤ J.pre a ∧ J.post a ≤ J.post b
        · simp [Jungle.cls, hp, hf, hk] at hc
        · unfold Jungle.Anc at hlam
          rcases hlam with hl | hl | hl | hl
          · -- `a` encloses `b`, not strictly: then `a = b` and `b` encloses `a`
            by_cases hne : a = b
            · subst hne; exact absurd ⟨Nat.le_refl _, Nat.le_refl _⟩ hk
            · have h1 : J.pre a ≠ J.pre b := fun e => hne (h.pre_inj a b ha hb e)
              have h2 : J.post a ≠ J.post b := fun e => hne (h.post_inj a b ha hb e)
              exact absurd ⟨by omega, by omega⟩ hf
          · exact absurd hl hk
          · exact absurd hl hnr
          · exact hl
  · intro hc
    have hnp : ¬ J.IsParent g a b := by
      intro hp
      have := h.parent_nested ha hb hp
      omega
    have hnf : ¬ (J.pre a < J.pre b ∧ J.post b < J.post a) := by omega
    have hnk : ¬ (J.pre b ≤ J.pre a ∧ J.post a ≤ J.post b) := by omega
    simp [Jungle.cls, hnp, hnf, hnk]

end SmcIrred
