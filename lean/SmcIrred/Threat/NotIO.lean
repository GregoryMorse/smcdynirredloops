module

public import SmcIrred.Spec.Threat
public import SmcIrred.Lang.Congr

public section

namespace SmcIrred.Threat

open Lang

/-- Padding with never-executed conditionals: `k` copies of `if (false) { block 9 }` after `p`. -/
@[expose] def padS (p : Stmt) : Nat → Stmt
  | 0 => p
  | k + 1 => .seq (padS p k) (.ite1 .falseC (.blk 9))

/-- Two programs that halt within the same fuel with the same result have the same terminating runs. -/
theorem equiv_of_halt {p q : Stmt} (h : ∀ c v, ∃ r0, exec 100 (compile p) (fun _ => false) c 0 v [] = some r0 ∧
    exec 100 (compile q) (fun _ => false) c 0 v [] = some r0) : Equiv p q := by
  intro c v r
  obtain ⟨r0, hp, hq⟩ := h c v
  constructor
  · rintro ⟨f, hf⟩
    obtain rfl := exec_det f 100 _ _ _ hf hp
    exact ⟨100, hq⟩
  · rintro ⟨f, hf⟩
    obtain rfl := exec_det f 100 _ _ _ hf hq
    exact ⟨100, hp⟩

theorem fig5a_pad_equiv : Equiv fig5a (padS fig5a 5) :=
  equiv_of_halt fun c v => by cases c <;> cases v <;> exact ⟨_, rfl, rfl⟩

theorem vcount_fig5a : vcount fig5a = 1 := by decide
theorem vcount_pad : vcount (padS fig5a 5) = 11 := by decide

/-- The vertex overhead of the programs of Figures 5 and 6 is between 0 and 4. -/
theorem scheme_overhead :
    (vcount fig5a ≤ vcount fig5bS ∧ vcount fig5bS ≤ vcount fig5a + 4) ∧
    (vcount fig5a ≤ vcount fig5cS ∧ vcount fig5cS ≤ vcount fig5a + 4) ∧
    (vcount fig6a ≤ vcount fig6bS ∧ vcount fig6bS ≤ vcount fig6a + 4) ∧
    (vcount fig6a ≤ vcount fig6cS ∧ vcount fig6cS ≤ vcount fig6a + 4) := by
  decide

/-- T7 (no indistinguishability). An obfuscator whose output size is within four vertices of its input's, in either direction
(the static scheme adds between 0 and 4, `scheme_overhead`), gives equivalent programs obfuscations that differ in the
observable number of vertices; so it is not an indistinguishability obfuscator for the size observable, and no
black-box-simulation property is claimed (Barak et al. rule out the general notion). -/
theorem not_size_indist (O : Stmt → Stmt) (hb : ∀ s, vcount (O s) ≤ vcount s + 4 ∧ vcount s ≤ vcount (O s) + 4) :
    ¬ SizeIndist O := by
  intro h
  have e := h _ _ fig5a_pad_equiv
  have h1 := (hb fig5a).1
  have h2 := (hb (padS fig5a 5)).2
  rw [vcount_fig5a] at h1
  rw [vcount_pad] at h2
  omega

end SmcIrred.Threat
