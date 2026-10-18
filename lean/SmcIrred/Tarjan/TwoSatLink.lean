module

public import SmcIrred.Tarjan.TwoSatCode
public import SmcIrred.Spec.TwoSatSolve

public section

namespace SmcIrred

theorem nneg_nneg (v : Nat) : nneg (nneg v) = v := by
  by_cases h : v % 2 = 0
  · have h1 : nneg v = v + 1 := by simp [nneg, h]
    have h3 : ¬ (v + 1) % 2 = 0 := by omega
    rw [h1]; simp [nneg, h3]
  · have h1 : nneg v = v - 1 := by simp [nneg, h]
    have h3 : (v - 1) % 2 = 0 := by omega
    rw [h1]; simp [nneg, h3]; omega

theorem nneg_ne (v : Nat) : nneg v ≠ v := by
  unfold nneg; by_cases h : v % 2 = 0 <;> simp [h] <;> omega

theorem nneg_even (x : Nat) : nneg (2 * x) = 2 * x + 1 := by unfold nneg; simp

theorem nneg_odd (x : Nat) : nneg (2 * x + 1) = 2 * x := by unfold nneg; simp <;> omega

theorem nneg_lt {v n : Nat} (h : v < 2 * n) : nneg v < 2 * n := by
  unfold nneg; by_cases hv : v % 2 = 0
  · simp only [hv, ↓reduceIte]; omega
  · simp only [hv, ↓reduceIte]; omega

/-- No literal of the list is in the list together with its negation. -/
@[expose] def NFree (l : List Nat) : Prop := ∀ v ∈ l, nneg v ∉ l

/-- A clash-free component leaves `unsat` off and adds exactly its literals whose negation is not in `sol`. -/
theorem tsComp_free : ∀ (C u : List Nat) (sol : List Nat), (∀ v, (v ∈ u ∨ v ∈ C) → ¬ (nneg v ∈ u ∨ nneg v ∈ C)) →
    (tsComp C u (false, sol)).1 = false ∧
    ∀ x, x ∈ (tsComp C u (false, sol)).2 ↔ x ∈ sol ∨ (x ∈ C ∧ nneg x ∉ sol) := by
  intro C
  induction C with
  | nil => intro u sol _; exact ⟨rfl, fun x => by simp [tsComp]⟩
  | cons v vs ih =>
    intro u sol hfree
    have hu : ¬ nneg v ∈ u := fun h => hfree v (Or.inr List.mem_cons_self) (Or.inl h)
    have hvs : ¬ nneg v ∈ vs := fun h => hfree v (Or.inr List.mem_cons_self) (Or.inr (List.mem_cons_of_mem _ h))
    rw [tsComp_step vs u sol hu]
    have hfree' : ∀ w, (w ∈ v :: u ∨ w ∈ vs) → ¬ (nneg w ∈ v :: u ∨ nneg w ∈ vs) := by
      intro w hw hn
      refine hfree w ?_ ?_
      · rcases hw with hw | hw
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact Or.inr List.mem_cons_self
          · exact Or.inl hw
        · exact Or.inr (List.mem_cons_of_mem _ hw)
      · rcases hn with hn | hn
        · rcases List.mem_cons.1 hn with hn | hn
          · exact Or.inr (by rw [hn]; exact List.mem_cons_self)
          · exact Or.inl hn
        · exact Or.inr (List.mem_cons_of_mem _ hn)
    obtain ⟨h1, h2⟩ := ih (v :: u) (if nneg v ∈ sol then sol else v :: sol) hfree'
    refine ⟨h1, fun x => ?_⟩
    rw [h2 x]
    have hxv : x ∈ vs → nneg x ≠ v := by
      intro hx e
      apply hvs
      have : nneg v = x := by rw [← e, nneg_nneg]
      rw [this]; exact hx
    by_cases hq : nneg v ∈ sol
    · simp only [hq, ite_true]
      constructor
      · rintro (h | ⟨h3, h4⟩)
        · exact Or.inl h
        · exact Or.inr ⟨List.mem_cons_of_mem _ h3, h4⟩
      · rintro (h | ⟨h3, h4⟩)
        · exact Or.inl h
        · rcases List.mem_cons.1 h3 with rfl | h3
          · exact absurd hq h4
          · exact Or.inr ⟨h3, h4⟩
    · simp only [hq, ite_false, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨h3, h4⟩)
        · exact Or.inr ⟨Or.inl h, by rw [h]; exact hq⟩
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr h3, fun h => h4 (Or.inr h)⟩
      · rintro (h | ⟨h3, h4⟩)
        · exact Or.inl (Or.inr h)
        · rcases h3 with rfl | h3
          · exact Or.inl (Or.inl rfl)
          · refine Or.inr ⟨h3, ?_⟩
            intro h
            rcases h with h | h
            · exact hxv h3 h
            · exact h4 h

/-- A clash within the component (or against `u`) turns `unsat` on. -/
theorem tsComp_clash_u : ∀ (C u : List Nat) (st : Bool × List Nat),
    ((∃ v ∈ C, nneg v ∈ u) ∨ ∃ v ∈ C, nneg v ∈ C) → (tsComp C u st).1 = true := by
  intro C
  induction C with
  | nil => intro u st h; rcases h with ⟨v, hv, _⟩ | ⟨v, hv, _⟩ <;> simp at hv
  | cons v vs ih =>
    intro u st h
    obtain ⟨b, sol⟩ := st
    cases b
    · by_cases hu : nneg v ∈ u
      · rw [tsComp_clash vs u sol hu]
      · rw [tsComp_step vs u sol hu]
        apply ih
        rcases h with ⟨w, hw, hn⟩ | ⟨w, hw, hn⟩
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact absurd hn hu
          · exact Or.inl ⟨w, hw, List.mem_cons_of_mem _ hn⟩
        · rcases List.mem_cons.1 hw with rfl | hw
          · rcases List.mem_cons.1 hn with hn | hn
            · exact (nneg_ne w hn).elim
            · exact Or.inl ⟨nneg w, hn, by rw [nneg_nneg]; exact List.mem_cons_self⟩
          · rcases List.mem_cons.1 hn with hn | hn
            · exact Or.inl ⟨w, hw, by rw [hn]; exact List.mem_cons_self⟩
            · exact Or.inr ⟨w, hw, hn⟩
    · rw [tsComp_true]

/-- Induction on a list from the right. -/
theorem snoc_ind {α : Type} {motive : List α → Prop} (nil : motive []) (snoc : ∀ l a, motive l → motive (l ++ [a])) :
    ∀ l, motive l := by
  have key : ∀ n, ∀ l : List α, l.length = n → motive l := by
    intro n
    induction n with
    | zero => intro l h; rw [List.eq_nil_of_length_eq_zero h]; exact nil
    | succ n ih =>
      intro l h
      rcases List.eq_nil_or_concat l with rfl | ⟨l', b, rfl⟩
      · simp at h
      · have : l'.length = n := by simpa using h
        rw [List.concat_eq_append]
        exact snoc l' b (ih l' this)
  intro l
  exact key _ l rfl

theorem compIdx_lt : ∀ (pre : List (List Nat)) (y : Nat), y ∈ pre.flatten → compIdx pre y < pre.length := by
  intro pre
  induction pre with
  | nil => intro y h; simp at h
  | cons C cs ih =>
    intro y h
    by_cases hy : y ∈ C
    · simp [compIdx, hy]
    · have : y ∈ cs.flatten := by
        rcases List.mem_append.1 (by simpa using h : y ∈ C ++ cs.flatten) with h | h
        · exact absurd h hy
        · exact h
      have := ih y this
      simp [compIdx, hy]; omega

theorem compIdx_snoc_old (C : List Nat) : ∀ (pre : List (List Nat)) (y : Nat), y ∈ pre.flatten →
    compIdx (pre ++ [C]) y = compIdx pre y := by
  intro pre
  induction pre with
  | nil => intro y h; simp at h
  | cons C0 cs ih =>
    intro y h
    by_cases hy : y ∈ C0
    · simp [compIdx, hy]
    · have : y ∈ cs.flatten := by
        rcases List.mem_append.1 (by simpa using h : y ∈ C0 ++ cs.flatten) with h | h
        · exact absurd h hy
        · exact h
      simp [compIdx, hy, ih y this]

theorem compIdx_snoc_new (C : List Nat) : ∀ (pre : List (List Nat)) (y : Nat), y ∉ pre.flatten → y ∈ C →
    compIdx (pre ++ [C]) y = pre.length := by
  intro pre
  induction pre with
  | nil => intro y _ hC; simp [compIdx, hC]
  | cons C0 cs ih =>
    intro y h hC
    have hy : y ∉ C0 := fun hh => h (by simp [hh])
    have : y ∉ cs.flatten := fun hh => h (by simp [hh])
    simp [compIdx, hy, ih y this hC]

theorem compIdx_split : ∀ (comps : List (List Nat)) (y : Nat), y ∈ comps.flatten →
    ∃ L C R, comps = L ++ C :: R ∧ y ∈ C ∧ (∀ C' ∈ L, y ∉ C') ∧ compIdx comps y = L.length := by
  intro comps
  induction comps with
  | nil => intro y h; simp at h
  | cons C0 cs ih =>
    intro y h
    by_cases hy : y ∈ C0
    · exact ⟨[], C0, cs, rfl, hy, by simp, by simp [compIdx, hy]⟩
    · have : y ∈ cs.flatten := by
        rcases List.mem_append.1 (by simpa using h : y ∈ C0 ++ cs.flatten) with h | h
        · exact absurd h hy
        · exact h
      obtain ⟨L, C, R, e, h1, h2, h3⟩ := ih y this
      refine ⟨C0 :: L, C, R, by rw [e]; rfl, h1, ?_, by simp [compIdx, hy, h3]⟩
      intro C' hC'
      rcases List.mem_cons.1 hC' with rfl | hC'
      · exact hy
      · exact h2 C' hC'

theorem tsFold_snoc (l : List (List Nat)) (C : List Nat) : tsFold (l ++ [C]) = tsComp C [] (tsFold l) := by
  simp [tsFold, List.foldl_append]

/-- `twosat` reports unsatisfiable exactly when some component contains a literal and its negation. -/
theorem tsFold_unsat (pre : List (List Nat)) :
    (tsFold pre).1 = true ↔ ∃ C ∈ pre, ∃ v ∈ C, nneg v ∈ C := by
  induction pre using snoc_ind with
  | nil => simp [tsFold]
  | snoc l C ih =>
    rw [tsFold_snoc]
    constructor
    · intro h
      by_cases hl : (tsFold l).1 = true
      · obtain ⟨C0, h0, hv⟩ := ih.1 hl
        exact ⟨C0, List.mem_append_left _ h0, hv⟩
      · have hl' : (tsFold l).1 = false := by simpa using hl
        by_cases hcl : ∃ v ∈ C, nneg v ∈ C
        · exact ⟨C, by simp, hcl⟩
        · exfalso
          have hfree : ∀ v, (v ∈ ([] : List Nat) ∨ v ∈ C) → ¬ (nneg v ∈ ([] : List Nat) ∨ nneg v ∈ C) := by
            intro v hv hn
            rcases hv with hv | hv
            · simp at hv
            · rcases hn with hn | hn
              · simp at hn
              · exact hcl ⟨v, hv, hn⟩
          have e : tsFold l = (false, (tsFold l).2) := Prod.ext hl' rfl
          have h2 := (tsComp_free C [] (tsFold l).2 hfree).1
          rw [e] at h
          rw [h2] at h
          exact Bool.noConfusion h
    · rintro ⟨C0, h0, hv⟩
      rcases List.mem_append.1 h0 with h0 | h0
      · have := ih.2 ⟨C0, h0, hv⟩
        exact (tsComp_mono C [] (tsFold l)).1 this
      · rw [List.mem_singleton] at h0; subst h0
        exact tsComp_clash_u C0 [] _ (Or.inr hv)

theorem tsFold_nfree {l : List (List Nat)} {C : List Nat} (h : (tsFold (l ++ [C])).1 = false) :
    (tsFold l).1 = false ∧ ∀ v ∈ C, nneg v ∉ C := by
  have hl : (tsFold l).1 = false := by
    cases hb : (tsFold l).1
    · rfl
    · rw [tsFold_snoc] at h
      have := (tsComp_mono C [] (tsFold l)).1 hb
      rw [this] at h; exact Bool.noConfusion h
  refine ⟨hl, fun v hv hn => ?_⟩
  have := (tsFold_unsat (l ++ [C])).2 ⟨C, by simp, v, hv, hn⟩
  rw [h] at this; exact Bool.noConfusion this

/-- The set `sol` built by `twosat`: a literal is in it iff its component does not come after the component of its
negation. -/
theorem tsFold_sol : ∀ pre : List (List Nat), pre.flatten.Nodup → (tsFold pre).1 = false → ∀ x,
    x ∈ (tsFold pre).2 ↔ x ∈ pre.flatten ∧ ¬ (nneg x ∈ pre.flatten ∧ compIdx pre (nneg x) < compIdx pre x) := by
  intro pre
  induction pre using snoc_ind with
  | nil => intro _ _ x; simp [tsFold]
  | snoc l C ih =>
    intro hnd hun x
    obtain ⟨hl, hfreeC⟩ := tsFold_nfree hun
    have hnd' : (l.flatten ++ C).Nodup := by simpa using hnd
    have hdisj : ∀ y, y ∈ l.flatten → y ∈ C → False := fun y h1 h2 =>
      (List.nodup_append.1 hnd').2.2 y h1 y h2 rfl
    have ihl := ih (by have := List.nodup_append.1 hnd'; simpa using this.1) hl
    have e : tsFold l = (false, (tsFold l).2) := Prod.ext hl rfl
    have hfree : ∀ v, (v ∈ ([] : List Nat) ∨ v ∈ C) → ¬ (nneg v ∈ ([] : List Nat) ∨ nneg v ∈ C) := by
      intro v hv hn
      rcases hv with hv | hv
      · simp at hv
      · rcases hn with hn | hn
        · simp at hn
        · exact hfreeC v hv hn
    have hs := (tsComp_free C [] (tsFold l).2 hfree).2 x
    rw [tsFold_snoc, e]
    rw [e] at hs
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_append]
    rw [hs]
    generalize hsol : (tsFold l).2 = sol at *
    have hsub : ∀ y, y ∈ sol → y ∈ l.flatten := fun y hy => ((ihl y).1 hy).1
    have hlt : ∀ y, y ∈ l.flatten → compIdx l y < l.length := fun y hy => compIdx_lt l y hy
    have hold : ∀ y, y ∈ l.flatten → compIdx (l ++ [C]) y = compIdx l y := fun y hy => compIdx_snoc_old C l y hy
    have hnew : ∀ y, y ∉ l.flatten → y ∈ C → compIdx (l ++ [C]) y = l.length := fun y h1 h2 => compIdx_snoc_new C l y h1 h2
    by_cases hxf : x ∈ l.flatten
    · have hxc : x ∉ C := fun h => hdisj x hxf h
      have hix := hlt x hxf
      rw [hold x hxf]
      by_cases hyf : nneg x ∈ l.flatten
      · rw [hold _ hyf]
        constructor
        · rintro (h | ⟨h, _⟩)
          · have := (ihl x).1 h
            exact ⟨Or.inl hxf, fun ⟨_, hh⟩ => this.2 ⟨hyf, hh⟩⟩
          · exact absurd h hxc
        · rintro ⟨_, hh⟩
          exact Or.inl ((ihl x).2 ⟨hxf, fun ⟨_, h2⟩ => hh ⟨Or.inl hyf, h2⟩⟩)
      · by_cases hyc : nneg x ∈ C
        · have hyn := hnew _ hyf hyc
          rw [hyn]
          constructor
          · rintro (h | ⟨h, _⟩)
            · exact ⟨Or.inl hxf, fun ⟨_, hh⟩ => by omega⟩
            · exact absurd h hxc
          · rintro ⟨_, _⟩
            exact Or.inl ((ihl x).2 ⟨hxf, fun ⟨h1, _⟩ => hyf h1⟩)
        · constructor
          · rintro (h | ⟨h, _⟩)
            · refine ⟨Or.inl hxf, fun ⟨hh, _⟩ => ?_⟩
              rcases hh with hh | hh
              · exact hyf hh
              · exact hyc hh
            · exact absurd h hxc
          · rintro ⟨_, _⟩
            exact Or.inl ((ihl x).2 ⟨hxf, fun ⟨h1, _⟩ => hyf h1⟩)
    · by_cases hxc : x ∈ C
      · have hxs : x ∉ sol := fun h => hxf (hsub x h)
        have hyc : nneg x ∉ C := hfreeC x hxc
        rw [hnew x hxf hxc]
        have hys : nneg x ∈ sol ↔ nneg x ∈ l.flatten := by
          constructor
          · intro h; exact hsub _ h
          · intro h
            refine (ihl _).2 ⟨h, fun ⟨h1, _⟩ => ?_⟩
            rw [nneg_nneg] at h1
            exact hxf h1
        constructor
        · rintro (h | ⟨_, h⟩)
          · exact absurd h hxs
          · refine ⟨Or.inr hxc, fun ⟨hh, hlt2⟩ => ?_⟩
            rcases hh with hh | hh
            · exact h (hys.2 hh)
            · exact hyc hh
        · rintro ⟨_, hh⟩
          refine Or.inr ⟨hxc, fun h => ?_⟩
          have hyf := hys.1 h
          exact hh ⟨Or.inl hyf, by rw [hold _ hyf]; exact hlt _ hyf⟩
      · constructor
        · rintro (h | ⟨h, _⟩)
          · exact absurd (hsub x h) hxf
          · exact absurd h hxc
        · rintro ⟨h, _⟩
          rcases h with h | h
          · exact absurd h hxf
          · exact absurd h hxc

theorem compIdx_of_split : ∀ (L : List (List Nat)) (C : List Nat) (R : List (List Nat)) (y : Nat), y ∈ C →
    (∀ C' ∈ L, y ∉ C') → compIdx (L ++ C :: R) y = L.length := by
  intro L
  induction L with
  | nil => intro C R y hy _; simp [compIdx, hy]
  | cons C0 L ih =>
    intro C R y hy h
    have h0 : y ∉ C0 := h C0 List.mem_cons_self
    simp [compIdx, h0, ih C R y hy (fun C' hC' => h C' (List.mem_cons_of_mem _ hC'))]

/-- `twosat` against the component indices: `unsat` iff a variable shares its component with its negation, and
otherwise the literal `2x` is in `sol` iff its component comes first. -/
theorem tsFold_link (n : Nat) (comps : List (List Nat)) (hnd : comps.flatten.Nodup)
    (hcov : ∀ v, v < 2 * n → v ∈ comps.flatten) (hrng : ∀ C ∈ comps, ∀ w ∈ C, w < 2 * n) :
    ((tsFold comps).1 = true ↔ ∃ x, x < n ∧ compIdx comps (2 * x) = compIdx comps (2 * x + 1)) ∧
    ((tsFold comps).1 = false → ∀ x, x < n →
      (2 * x ∈ (tsFold comps).2 ↔ compIdx comps (2 * x) < compIdx comps (2 * x + 1))) := by
  have ha : (tsFold comps).1 = true ↔ ∃ x, x < n ∧ compIdx comps (2 * x) = compIdx comps (2 * x + 1) := by
    rw [tsFold_unsat]
    constructor
    · rintro ⟨C, hC, v, hv, hn⟩
      obtain ⟨L, R, e⟩ := List.append_of_mem hC
      have hdis : ∀ y ∈ C, ∀ C' ∈ L, y ∉ C' := by
        intro y hy C' hC' hyC'
        have hnd' : (L.flatten ++ (C ++ R.flatten)).Nodup := by
          have : comps.flatten = L.flatten ++ (C ++ R.flatten) := by rw [e]; simp
          rw [← this]; exact hnd
        exact (List.nodup_append.1 hnd').2.2 y (List.mem_flatten.2 ⟨C', hC', hyC'⟩) y (List.mem_append_left _ hy) rfl
      have hid : ∀ y ∈ C, compIdx comps y = L.length := by
        intro y hy; rw [e]; exact compIdx_of_split L C R y hy (hdis y hy)
      have hv2 : v < 2 * n := hrng C hC v hv
      have hn2 : nneg v < 2 * n := nneg_lt hv2
      by_cases hp : v % 2 = 0
      · obtain ⟨x, hx⟩ : ∃ x, v = 2 * x := ⟨v / 2, by omega⟩
        subst hx
        rw [nneg_even] at hn
        exact ⟨x, by omega, by rw [hid _ hv, hid _ hn]⟩
      · obtain ⟨x, hx⟩ : ∃ x, v = 2 * x + 1 := ⟨v / 2, by omega⟩
        subst hx
        rw [nneg_odd] at hn
        exact ⟨x, by omega, by rw [hid _ hv, hid _ hn]⟩
    · rintro ⟨x, hx, he⟩
      obtain ⟨L, C, R, e, h1, h2, h3⟩ := compIdx_split comps (2 * x) (hcov _ (by omega))
      obtain ⟨L2, C2, R2, e2, h1', h2', h3'⟩ := compIdx_split comps (2 * x + 1) (hcov _ (by omega))
      have hlen : L.length = L2.length := by rw [← h3, ← h3']; exact he
      have := List.append_inj (e.symm.trans e2) hlen
      obtain ⟨-, hc⟩ := this
      have hCC : C = C2 := (List.cons.inj hc).1
      exact ⟨C, by rw [e]; simp, 2 * x, h1, by rw [nneg_even, hCC]; exact h1'⟩
  refine ⟨ha, fun hf x hx => ?_⟩
  have hsol := tsFold_sol comps hnd hf (2 * x)
  rw [hsol, nneg_even]
  have hne : compIdx comps (2 * x) ≠ compIdx comps (2 * x + 1) := fun he => by
    have := ha.2 ⟨x, hx, he⟩
    rw [hf] at this; exact Bool.noConfusion this
  have h1 : 2 * x ∈ comps.flatten := hcov _ (by omega)
  have h2 : 2 * x + 1 ∈ comps.flatten := hcov _ (by omega)
  constructor
  · rintro ⟨_, hh⟩
    have : ¬ (compIdx comps (2 * x + 1) < compIdx comps (2 * x)) := fun h => hh ⟨h2, h⟩
    omega
  · intro hlt
    exact ⟨h1, fun ⟨_, hh⟩ => by omega⟩

end SmcIrred
