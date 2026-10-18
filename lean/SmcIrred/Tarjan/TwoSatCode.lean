module

public import SmcIrred.Spec.TarjanCode

public section

namespace SmcIrred

/-- Two `twosat` states agree: same `unsat` flag, same set `sol`. -/
@[expose] def TsE (st st' : Bool × List Nat) : Prop := st.1 = st'.1 ∧ ∀ v, v ∈ st.2 ↔ v ∈ st'.2

/-- Either unsatisfiability was found, or every vertex of `vs` or its negation is in `sol`. -/
@[expose] def TsClosed (vs : List Nat) (st : Bool × List Nat) : Prop :=
  st.1 = true ∨ ∀ r ∈ vs, r ∈ st.2 ∨ nneg r ∈ st.2

theorem tsComp_true (v : Nat) (vs u : List Nat) (sol : List Nat) : tsComp (v :: vs) u (true, sol) = (true, sol) := by
  simp [tsComp]

theorem tsComp_clash {v : Nat} (vs u : List Nat) (sol : List Nat) (hu : nneg v ∈ u) :
    tsComp (v :: vs) u (false, sol) = (true, sol) := by
  simp [tsComp, hu]

theorem tsComp_step {v : Nat} (vs u : List Nat) (sol : List Nat) (hu : ¬ nneg v ∈ u) :
    tsComp (v :: vs) u (false, sol) = tsComp vs (v :: u) (false, if nneg v ∈ sol then sol else v :: sol) := by
  simp [tsComp, hu]

theorem tsComp_cong : ∀ (C u : List Nat) (st st' : Bool × List Nat), TsE st st' →
    TsE (tsComp C u st) (tsComp C u st') := by
  intro C
  induction C with
  | nil => intro u st st' h; exact h
  | cons v vs ih =>
    intro u st st' h
    obtain ⟨b, sol⟩ := st
    obtain ⟨b', sol'⟩ := st'
    obtain ⟨h1, h2⟩ := h
    have h1 : b = b' := h1
    have h2 : ∀ x, x ∈ sol ↔ x ∈ sol' := h2
    subst h1
    cases b
    · by_cases hu : nneg v ∈ u
      · rw [tsComp_clash vs u sol hu, tsComp_clash vs u sol' hu]; exact ⟨rfl, h2⟩
      · rw [tsComp_step vs u sol hu, tsComp_step vs u sol' hu]
        refine ih (v :: u) _ _ ⟨rfl, ?_⟩
        intro x
        have hn : nneg v ∈ sol ↔ nneg v ∈ sol' := h2 _
        by_cases hq : nneg v ∈ sol
        · have hq' := hn.1 hq
          simp only [hq, hq', ite_true]; exact h2 x
        · have hq' : ¬ nneg v ∈ sol' := fun h => hq (hn.2 h)
          simp only [hq, hq', ite_false, List.mem_cons]
          constructor <;> intro hx <;> rcases hx with hx | hx
          · exact Or.inl hx
          · exact Or.inr ((h2 x).1 hx)
          · exact Or.inl hx
          · exact Or.inr ((h2 x).2 hx)
    · rw [tsComp_true, tsComp_true]; exact ⟨rfl, h2⟩

theorem tsComp_mono : ∀ (C u : List Nat) (st : Bool × List Nat),
    (st.1 = true → (tsComp C u st).1 = true) ∧ (∀ x, x ∈ st.2 → x ∈ (tsComp C u st).2) := by
  intro C
  induction C with
  | nil => intro u st; exact ⟨fun h => h, fun x h => h⟩
  | cons v vs ih =>
    intro u st
    obtain ⟨b, sol⟩ := st
    cases b
    · by_cases hu : nneg v ∈ u
      · rw [tsComp_clash vs u sol hu]; exact ⟨fun h => by simp at h, fun x h => h⟩
      · rw [tsComp_step vs u sol hu]
        obtain ⟨-, h2⟩ := ih (v :: u) (false, if nneg v ∈ sol then sol else v :: sol)
        refine ⟨fun h => by simp at h, fun x hx => h2 x ?_⟩
        by_cases hq : nneg v ∈ sol <;> simp [hq, hx]
    · rw [tsComp_true]; exact ⟨fun h => h, fun x h => h⟩

theorem tsComp_closed : ∀ (C u : List Nat) (st : Bool × List Nat),
    (tsComp C u st).1 = true ∨ ∀ v ∈ C, v ∈ (tsComp C u st).2 ∨ nneg v ∈ (tsComp C u st).2 := by
  intro C
  induction C with
  | nil => intro u st; exact Or.inr (by simp)
  | cons v vs ih =>
    intro u st
    obtain ⟨b, sol⟩ := st
    cases b
    · by_cases hu : nneg v ∈ u
      · rw [tsComp_clash vs u sol hu]; exact Or.inl rfl
      · rw [tsComp_step vs u sol hu]
        rcases ih (v :: u) (false, if nneg v ∈ sol then sol else v :: sol) with h | h
        · exact Or.inl h
        · refine Or.inr ?_
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · obtain ⟨-, hm⟩ := tsComp_mono vs (x :: u) (false, if nneg x ∈ sol then sol else x :: sol)
            by_cases hq : nneg x ∈ sol
            · exact Or.inr (hm _ (by simp [hq]))
            · exact Or.inl (hm _ (by simp [hq]))
          · exact h x hx
    · rw [tsComp_true]; exact Or.inl rfl

theorem tsComp_single (r : Nat) (st : Bool × List Nat) (h : TsClosed [r] st) : TsE (tsComp [r] [] st) st := by
  obtain ⟨b, sol⟩ := st
  cases b
  · have hr : r ∈ sol ∨ nneg r ∈ sol := by
      rcases h with h | h
      · exact absurd h (by simp)
      · exact h r (by simp)
    rw [tsComp_step [] [] sol (by simp)]
    refine ⟨rfl, fun x => ?_⟩
    show x ∈ (if nneg r ∈ sol then sol else r :: sol) ↔ x ∈ sol
    by_cases hq : nneg r ∈ sol
    · simp [hq]
    · have : r ∈ sol := hr.resolve_right hq
      simp only [hq, ite_false, List.mem_cons]
      constructor
      · intro hx; rcases hx with rfl | hx; exact this; exact hx
      · intro hx; exact Or.inr hx
  · rw [tsComp_true]; exact ⟨rfl, fun _ => Iff.rfl⟩

theorem tsClosed_mono {vs : List Nat} {st st' : Bool × List Nat} (h : TsClosed vs st) (h1 : st.1 = true → st'.1 = true)
    (h2 : ∀ x, x ∈ st.2 → x ∈ st'.2) : TsClosed vs st' := by
  rcases h with h | h
  · exact Or.inl (h1 h)
  · exact Or.inr (fun r hr => by
      rcases h r hr with h | h
      · exact Or.inl (h2 _ h)
      · exact Or.inr (h2 _ h))

theorem tsClosed_of_E {vs : List Nat} {st st' : Bool × List Nat} (h : TsClosed vs st) (e : TsE st st') :
    TsClosed vs st' :=
  tsClosed_mono h (fun h => by rw [← e.1]; exact h) (fun x hx => (e.2 x).1 hx)

/-- The loop of `twosat` ignores the duplicate singleton components: on `out` it ends in the same state (same `unsat`
flag, same set `sol`) as on `comps`. -/
theorem tsFold_dup {l l' : List (List Nat)} (h : DupOf l l') : TsE (tsFold l) (tsFold l') ∧ TsClosed l.flatten (tsFold l') := by
  induction h with
  | nil => exact ⟨⟨rfl, fun _ => Iff.rfl⟩, Or.inr (by simp)⟩
  | @keep l l' C _ ih =>
    obtain ⟨he, hc⟩ := ih
    have e1 : tsFold (l ++ [C]) = tsComp C [] (tsFold l) := by simp [tsFold, List.foldl_append]
    have e2 : tsFold (l' ++ [C]) = tsComp C [] (tsFold l') := by simp [tsFold, List.foldl_append]
    rw [e1, e2]
    refine ⟨tsComp_cong C [] _ _ he, ?_⟩
    obtain ⟨hm1, hm2⟩ := tsComp_mono C [] (tsFold l')
    have hc' := tsClosed_mono hc hm1 hm2
    rcases hc' with h' | h'
    · exact Or.inl h'
    rcases tsComp_closed C [] (tsFold l') with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      intro r hr
      rcases List.mem_append.1 (by simpa using hr : r ∈ l.flatten ++ C) with hr | hr
      · exact h' r hr
      · exact h r hr
  | @dup l l' r C _ hC hr ih =>
    obtain ⟨he, hc⟩ := ih
    have e2 : tsFold (l' ++ [[r]]) = tsComp [r] [] (tsFold l') := by simp [tsFold, List.foldl_append]
    rw [e2]
    have hcr : TsClosed [r] (tsFold l') := by
      rcases hc with h | h
      · exact Or.inl h
      · exact Or.inr (fun r' hr' => by
          rw [List.mem_singleton] at hr'; subst hr'
          exact h r' (List.mem_flatten.2 ⟨C, hC, hr⟩))
    have es := tsComp_single r _ hcr
    refine ⟨⟨he.1.trans es.1.symm, fun x => (he.2 x).trans (es.2 x).symm⟩, tsClosed_of_E hc ?_⟩
    exact ⟨es.1.symm, fun x => (es.2 x).symm⟩

end SmcIrred
