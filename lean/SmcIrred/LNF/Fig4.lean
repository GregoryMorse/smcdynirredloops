module

public import SmcIrred.LNF.Decide
public import SmcIrred.Graph.Fig4

public section

namespace SmcIrred

/-- Figure 4(c): the loop headers of Figure 4 are u, w, x (paper labels 2, 4, 5). -/
theorem fig4_headers : ∀ w, w < 6 → (fig4.IsHeader fig4Jungle w ↔ (w = 1 ∨ w = 3 ∨ w = 4)) := by decide

/-- Figure 4(c): the loop bodies. L(x) = {x, v}, L(w) = {w, x, v}, L(u) = {u, w, x, v}. -/
theorem fig4_bodies : ∀ w, w < 6 → ∀ x, x < 6 → (fig4.Body fig4Jungle w x ↔
    ((w = 4 ∧ (x = 4 ∨ x = 2)) ∨ (w = 3 ∧ (x = 3 ∨ x = 4 ∨ x = 2)) ∨
      (w = 1 ∧ (x = 1 ∨ x = 3 ∨ x = 4 ∨ x = 2)))) := by
  set_option synthInstance.maxSize 2048 in decide

/-- Figure 4(c): all three loops are irreducible. -/
theorem fig4_irreducible : ∀ w, w < 6 → (fig4.Irreducible fig4Jungle w ↔ (w = 1 ∨ w = 3 ∨ w = 4)) := by decide

/-- Figure 4(c): the loop nesting forest has the edges u → w, w → x, x → v (paper: 2 → 4, 4 → 5, 5 → 3); the
vertices entry and exit (paper 1, 6) are top-level non-headers. -/
theorem fig4_lnf : ∀ h, h < 6 → ∀ x, x < 6 → (fig4.LnfParent fig4Jungle h x ↔
    ((h = 1 ∧ x = 3) ∨ (h = 3 ∧ x = 4) ∨ (h = 4 ∧ x = 2))) := by decide

/-- The only multiple-entry edge of Figure 4 is the edge from the entry into v (paper: 1 → 3, "{3: {1}}"). -/
theorem fig4_mee : ∀ x, x < 6 → ∀ y, y < 6 → (fig4.IsMEE fig4Jungle x y ↔ (x = 0 ∧ y = 2)) := by decide

end SmcIrred
