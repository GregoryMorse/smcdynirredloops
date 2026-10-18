module

public import SmcIrred.Spec.Threat

public section

namespace SmcIrred.Threat

open Lang

/-- Padding with never-executed conditionals: `k` copies of `if (false) { block 9 }` after `p`. -/
@[expose] def padS (p : Stmt) : Nat → Stmt
  | 0 => p
  | k + 1 => .seq (padS p k) (.ite1 .falseC (.blk 9))

theorem fig5a_pad_equiv : Equiv fig5a (padS fig5a 3) := by
  intro c v; cases c <;> cases v <;> decide

theorem vcount_fig5a : vcount fig5a = 1 := by decide
theorem vcount_pad : vcount (padS fig5a 3) = 7 := by decide

/-- The vertex overhead of the static scheme of Figures 5 and 6 is between 0 and 4. -/
theorem scheme_overhead {p q : Stmt} (h : Obfuscates p q) : vcount p ≤ vcount q ∧ vcount q ≤ vcount p + 4 := by
  cases h <;> decide

/-- T7 (no indistinguishability). An obfuscator whose output has at least as many vertices as its input and at most four more
(as the static scheme does, `scheme_overhead`) gives equivalent programs obfuscations that differ in the observable number of
vertices; so it is not an indistinguishability obfuscator for the size observable, and no black-box-simulation property is
claimed (Barak et al. rule out the general notion). -/
theorem not_size_indist (O : Stmt → Stmt) (hlo : ∀ s, vcount s ≤ vcount (O s)) (hhi : ∀ s, vcount (O s) ≤ vcount s + 4) :
    ¬ SizeIndist O := by
  intro h
  have e := h _ _ fig5a_pad_equiv
  have h1 := hhi fig5a
  have h2 := hlo (padS fig5a 3)
  rw [vcount_fig5a] at h1
  rw [vcount_pad] at h2
  omega

end SmcIrred.Threat
