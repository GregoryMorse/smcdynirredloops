module

public import SmcIrred.Spec.Lang
public import SmcIrred.LNF.Decide
public import SmcIrred.Graph.DfsValid

public section

namespace SmcIrred.Lang

/-- Bounded reachability test. -/
@[expose] def reachB (g : Digraph) : Nat → Nat → Nat → Bool
  | 0, a, b => a == b
  | f + 1, a, b => a == b || (a < g.n && (g.succ a).any fun c => c < g.n && reachB g f c b)

theorem reachB_sound (g : Digraph) : ∀ f a b, reachB g f a b = true → g.Reach a b := by
  intro f
  induction f with
  | zero =>
    intro a b h
    have : a = b := by simpa [reachB] using h
    subst this; exact .refl a
  | succ f ih =>
    intro a b h
    simp only [reachB, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
    rcases h with h | ⟨ha, c, hc, hc2⟩
    · subst h; exact .refl a
    · exact .step ⟨ha, hc2.1, hc⟩ (ih c b hc2.2)

/-- A graph all of whose vertices pass the bounded reachability test from `r` is a CFG with root `r`. -/
theorem isCFG_of_reachB (g : Digraph) (r : Nat) (hr : r < g.n)
    (h : (List.range g.n).all (fun v => reachB g g.n r v) = true) : g.IsCFG r := by
  refine ⟨hr, fun v hv => reachB_sound g g.n r v ?_⟩
  simp only [List.all_eq_true, List.mem_range] at h
  exact h v hv

end SmcIrred.Lang
