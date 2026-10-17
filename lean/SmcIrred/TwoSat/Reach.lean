module

public import SmcIrred.LNF.Decide
public import SmcIrred.Graph.DfsInv

public section

namespace SmcIrred

variable {g : Digraph}

theorem Digraph.Reach.trans {a b c : Nat} (h1 : g.Reach a b) (h2 : g.Reach b c) : g.Reach a c := by
  induction h1 with
  | refl _ => exact h2
  | step he _ ih => exact .step he (ih h2)

theorem Digraph.SameSCC.refl (a : Nat) : g.SameSCC a a := ⟨.refl a, .refl a⟩

theorem Digraph.SameSCC.symm {a b : Nat} (h : g.SameSCC a b) : g.SameSCC b a := ⟨h.2, h.1⟩

theorem Digraph.SameSCC.trans {a b c : Nat} (h1 : g.SameSCC a b) (h2 : g.SameSCC b c) : g.SameSCC a c :=
  ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩

theorem reach_iff_pathIn {a b : Nat} (ha : a < g.n) : g.Reach a b ↔ PathIn g (fun _ => True) a b := by
  constructor
  · intro h
    induction h with
    | refl _ => exact .refl ha trivial
    | @step x y z he _ ih => exact .step trivial he (ih he.2.1)
  · intro h
    clear ha
    induction h with
    | refl _ _ => exact .refl _
    | step _ he _ ih => exact .step he ih

theorem reach_of_ge {a b : Nat} (ha : ¬ a < g.n) : g.Reach a b ↔ a = b := by
  constructor
  · intro h
    cases h with
    | refl _ => rfl
    | step he _ => exact absurd he.1 ha
  · rintro rfl; exact .refl _

instance (g : Digraph) (a b : Nat) : Decidable (g.Reach a b) :=
  if ha : a < g.n then decidable_of_iff _ (reach_iff_pathIn ha).symm
  else decidable_of_iff _ (reach_of_ge ha).symm

instance (g : Digraph) (a b : Nat) : Decidable (g.SameSCC a b) := inferInstanceAs (Decidable (g.Reach a b ∧ g.Reach b a))

/-- The least vertex of the strongly connected component of `u`. -/
@[expose] def sccRep (g : Digraph) (u : Nat) : Nat := ((List.range g.n).find? fun w => decide (g.SameSCC u w)).getD u

/-- A reverse-topological SCC label: the size of the reachable set, then the component representative. -/
@[expose] def sccLabel (g : Digraph) (u : Nat) : Nat :=
  ((List.range g.n).filter fun w => decide (g.Reach u w)).length * (g.n + 1) + sccRep g u

theorem sccRep_spec {u : Nat} (hu : u < g.n) : sccRep g u < g.n ∧ g.SameSCC u (sccRep g u) := by
  unfold sccRep
  have : ((List.range g.n).find? fun w => decide (g.SameSCC u w)).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨u, List.mem_range.2 hu, by simpa using Digraph.SameSCC.refl u⟩
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 this
  rw [hw]
  have h1 := List.find?_some hw
  have h2 := List.mem_of_find?_eq_some hw
  exact ⟨List.mem_range.1 h2, by simpa using h1⟩

theorem sccRep_congr {u w : Nat} (hu : u < g.n) (h : g.SameSCC u w) : sccRep g u = sccRep g w := by
  unfold sccRep
  have e : (fun x => decide (g.SameSCC u x)) = fun x => decide (g.SameSCC w x) := by
    funext x
    simp only [decide_eq_decide]
    exact ⟨fun h2 => h.symm.trans h2, fun h2 => h.trans h2⟩
  rw [e]
  have : ((List.range g.n).find? fun x => decide (g.SameSCC w x)).isSome = true := by
    rw [List.find?_isSome]
    refine ⟨u, List.mem_range.2 hu, ?_⟩
    simpa using h.symm
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 this
  rw [hx]; rfl

/-- A reverse-topological SCC labelling exists for every finite digraph: labels are equal exactly inside a strongly
connected component and never increase along an edge. -/
theorem sccLabel_spec : (∀ u w, u < g.n → w < g.n → sccLabel g u = sccLabel g w → g.SameSCC u w) ∧
    ∀ u w, g.edge u w → sccLabel g w ≤ sccLabel g u := by
  constructor
  · intro u w hu hw h
    unfold sccLabel at h
    obtain ⟨hr1, hs1⟩ := sccRep_spec hu
    obtain ⟨hr2, hs2⟩ := sccRep_spec hw
    have hm : sccRep g u = sccRep g w := by
      have := congrArg (· % (g.n + 1)) h
      simp only [Nat.add_comm _ (sccRep g _), Nat.add_mul_mod_self_right] at this
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact hs1.trans (hm ▸ hs2.symm)
  · intro u w he
    have hu := he.1
    have hw := he.2.1
    by_cases hs : g.SameSCC u w
    · have hrep := sccRep_congr hu hs
      have hset : ((List.range g.n).filter fun x => decide (g.Reach w x)) =
          (List.range g.n).filter fun x => decide (g.Reach u x) := by
        apply List.filter_congr; intro x _
        simp only [decide_eq_decide]
        exact ⟨fun h => hs.1.trans h, fun h => hs.2.trans h⟩
      unfold sccLabel
      rw [hset, hrep]; exact Nat.le_refl _
    · have hnr : ¬ g.Reach w u := fun h => hs ⟨.step he (.refl _), h⟩
      have hlt : ((List.range g.n).filter fun x => decide (g.Reach w x)).length <
          ((List.range g.n).filter fun x => decide (g.Reach u x)).length := by
        refine filter_len_lt (v := u) ?_ (List.mem_range.2 hu) (by simpa using hnr) (by simpa using Digraph.Reach.refl (g := g) u)
        intro x hx
        simp only [decide_eq_true_eq] at hx ⊢
        exact (Digraph.Reach.step he (.refl _)).trans hx
      unfold sccLabel
      have hr := (sccRep_spec hw).1
      have := Nat.mul_le_mul_right (g.n + 1) hlt
      rw [Nat.succ_mul] at this
      omega

end SmcIrred
