module

public import SmcIrred.Graph.DfsVisit

public section

namespace SmcIrred

variable {g : Digraph} {v : Nat} {s1 : DfsState} {done : List Nat} {sk : DfsState} {fuel w : Nat}

variable {sk' : DfsState}

/-- The successor `w` was visited from `sk` to `sk'` (summary `D`): the loop invariant is preserved. -/
theorem Loop.step_visit (hL : Loop g v s1 done sk) (hw : w ∈ g.succ v) (hvn : v < g.n) (hwn : w < g.n)
    (D : Done g w sk sk') : Loop g v s1 (done ++ [w]) sk' := by
  have hold : ∀ x, sk.pre x ≠ 0 → sk'.pre x = sk.pre x ∧ sk'.post x = sk.post x :=
    fun x h => D.unchanged x (fun hn => h hn.1)
  have hsplit : ∀ x, s1.New sk' x ↔ s1.New sk x ∨ sk.New sk' x := by
    intro x
    constructor
    · rintro ⟨h0, h1⟩
      by_cases hx : sk.pre x = 0
      · exact Or.inr ⟨hx, h1⟩
      · exact Or.inl ⟨h0, hx⟩
    · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
      · exact ⟨h0, by rw [(hold x h1).1]; exact h1⟩
      · refine ⟨?_, h1⟩
        by_cases hs : s1.pre x = 0
        · exact hs
        · exfalso
          have := (hL.unchanged x (fun hn => hs hn.1)).1
          omega
  have hbk := hL.wf.pre_lt
  have hbp := hL.wf.post_lt
  have hclk := hL.clock
  have hDc := D.clock
  have hv1 : sk'.pre w = sk.clock := D.vroot.1
  have hv2 : sk'.post w + 1 = sk'.clock := D.vroot.2
  -- an old new vertex is not an ancestor of anything new from this call, nor of `w`
  have noanc : ∀ a b, s1.New sk a → sk.New sk' b → ¬ sk'.Anc a b := by
    intro a b ha hb hanc
    have ⟨_, _, h3, h4⟩ := hL.new a ha
    have ⟨_, h5, h6, _⟩ := D.new b hb
    have e := hold a (by omega)
    unfold DfsState.Anc at hanc
    omega
  refine ⟨?_, D.wf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · intro x hx
    have h1 : ¬ s1.New sk x := fun h => hx ((hsplit x).2 (Or.inl h))
    have h2 : ¬ sk.New sk' x := fun h => hx ((hsplit x).2 (Or.inr h))
    have a := D.unchanged x h2
    have b := hL.unchanged x h1
    exact ⟨a.1.trans b.1, a.2.trans b.2⟩
  · intro x hx
    rcases (hsplit x).1 hx with hx | hx
    · have ⟨h1, h2, h3, h4⟩ := hL.new x hx
      have e := hold x (by omega)
      rw [e.1, e.2]
      exact ⟨h1, h2, h3, by omega⟩
    · have ⟨h1, h2, h3, h4⟩ := D.new x hx
      exact ⟨h1, by omega, h3, h4⟩
  · -- distinct
    intro x y hx hy
    rcases (hsplit x).1 hx with hx | hx <;> rcases (hsplit y).1 hy with hy | hy
    · have ex := hold x hx.2
      have ey := hold y hy.2
      rw [ex.1, ex.2, ey.1, ey.2]
      exact hL.distinct x y hx hy
    · obtain ⟨_, _, _, _⟩ := hL.new x hx
      obtain ⟨_, _, _, _⟩ := D.new y hy
      have ex := hold x hx.2
      rw [ex.1, ex.2]
      refine ⟨fun h => ?_, fun h => ?_, ?_⟩ <;> omega
    · obtain ⟨_, _, _, _⟩ := hL.new y hy
      obtain ⟨_, _, _, _⟩ := D.new x hx
      have ey := hold y hy.2
      rw [ey.1, ey.2]
      refine ⟨fun h => ?_, fun h => ?_, ?_⟩ <;> omega
    · exact D.distinct x y hx hy
  · -- laminar
    intro x y hx hy
    rcases (hsplit x).1 hx with hx | hx <;> rcases (hsplit y).1 hy with hy | hy
    · have l := hL.laminar x y hx hy
      have ex := hold x hx.2
      have ey := hold y hy.2
      unfold DfsState.Anc at l ⊢
      rw [ex.1, ex.2, ey.1, ey.2]
      exact l
    · obtain ⟨_, _, _, _⟩ := hL.new x hx
      obtain ⟨_, _, _, _⟩ := D.new y hy
      have ex := hold x hx.2
      rw [ex.2]
      exact Or.inr (Or.inr (Or.inl (by omega)))
    · obtain ⟨_, _, _, _⟩ := hL.new y hy
      obtain ⟨_, _, _, _⟩ := D.new x hx
      have ey := hold y hy.2
      rw [ey.2]
      exact Or.inr (Or.inr (Or.inr (by omega)))
    · exact D.laminar x y hx hy
  · -- parent
    have ancOld : ∀ a b, s1.New sk a → s1.New sk b → (sk'.Anc a b ↔ sk.Anc a b) := by
      intro a b ha hb
      have ea := hold a ha.2
      have eb := hold b hb.2
      unfold DfsState.Anc
      rw [ea.1, ea.2, eb.1, eb.2]
    have noanc2 : ∀ a b, sk.New sk' a → s1.New sk b → ¬ sk'.Anc a b := by
      intro a b ha hb hanc
      obtain ⟨_, _, _, _⟩ := hL.new b hb
      obtain ⟨_, _, _, _⟩ := D.new a ha
      have eb := hold b hb.2
      unfold DfsState.Anc at hanc
      omega
    intro x hx
    rcases (hsplit x).1 hx with hx | hx
    · rcases hL.parent x hx with ⟨u, hu, he, hne, hanc, hall⟩ | ⟨he, hall⟩
      · refine Or.inl ⟨u, (hsplit u).2 (Or.inl hu), he, hne, (ancOld u x hu hx).2 hanc, ?_⟩
        intro w hw hwx hwa
        rcases (hsplit w).1 hw with hw | hw
        · exact (ancOld w u hw hu).2 (hall w hw hwx ((ancOld w x hw hx).1 hwa))
        · exact absurd hwa (noanc2 w x hw hx)
      · refine Or.inr ⟨he, ?_⟩
        intro w hw hwx hwa
        rcases (hsplit w).1 hw with hw | hw
        · exact hall w hw hwx ((ancOld w x hw hx).1 hwa)
        · exact noanc2 w x hw hx hwa
    · by_cases hxw : x = w
      · subst hxw
        refine Or.inr ⟨⟨hvn, hwn, hw⟩, ?_⟩
        intro w' hw' hne hanc
        rcases (hsplit w').1 hw' with h | h
        · exact noanc w' x h hx hanc
        · obtain ⟨_, _, _, _⟩ := D.new w' h
          unfold DfsState.Anc at hanc
          exact hne ((D.distinct w' x h hx).1 (by omega))
      · obtain ⟨u, hu, he, hne, hanc, hall⟩ := D.parent x hx hxw
        refine Or.inl ⟨u, (hsplit u).2 (Or.inr hu), he, hne, hanc, ?_⟩
        intro w' hw' hne' hanc'
        rcases (hsplit w').1 hw' with h | h
        · exact absurd hanc' (noanc w' x h hx)
        · exact hall w' h hne' hanc'
  · -- closure
    intro x hx y he
    rcases (hsplit x).1 hx with hx | hx
    · obtain ⟨h1, h2⟩ := hL.closure x hx y he
      have ex := hold x hx.2
      have ey := hold y h1
      rw [ey.1, ex.2]
      exact ⟨h1, h2⟩
    · exact D.closure x hx y he
  · -- proc
    intro w' hw' hwn'
    rcases List.mem_append.1 hw' with h | h
    · have := hL.proc w' h hwn'
      rw [(hold w' this).1]
      exact this
    · have e : w' = w := by simpa using h
      rw [e, hv1]
      have := hL.wf.clock
      omega

/-- The loop invariant after one more successor of `v`: either `w` is skipped (undiscovered test fails) or visited. -/
theorem Loop.step (hL : Loop g v s1 done sk) (hw : w ∈ g.succ v) (hvn : v < g.n)
    (hfuel : sk.undisc g ≤ fuel)
    (ih : ∀ w sc, w < g.n → sc.pre w = 0 → sc.Wf → sc.undisc g ≤ fuel → Done g w sc (dfsVisit g fuel w sc)) :
    Loop g v s1 (done ++ [w]) (if w < g.n ∧ sk.pre w = 0 then dfsVisit g fuel w sk else sk) := by
  by_cases hc : w < g.n ∧ sk.pre w = 0
  · simp only [hc, and_self, ↓reduceIte]
    exact hL.step_visit hw hvn hc.1 (ih w sk hc.1 hc.2 hL.wf hfuel)
  · simp only [hc, ↓reduceIte]
    refine ⟨hL.clock, hL.wf, hL.unchanged, hL.new, hL.distinct, hL.laminar, hL.parent, hL.closure, ?_⟩
    intro w' hw' hwn
    rcases List.mem_append.1 hw' with h | h
    · exact hL.proc w' h hwn
    · have : w' = w := by simpa using h
      subst this
      by_cases h0 : sk.pre w' = 0
      · exact absurd ⟨hwn, h0⟩ hc
      · exact h0

end SmcIrred
