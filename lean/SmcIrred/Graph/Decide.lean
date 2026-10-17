module

public import SmcIrred.Spec.DFS

public section

namespace SmcIrred

instance (g : Digraph) (a b : Nat) : Decidable (g.edge a b) :=
  inferInstanceAs (Decidable (a < g.n ∧ b < g.n ∧ b ∈ g.succ a))

instance (J : Jungle) (a b : Nat) : Decidable (J.Anc a b) :=
  inferInstanceAs (Decidable (J.pre a ≤ J.pre b ∧ J.post b ≤ J.post a))

instance (g : Digraph) (J : Jungle) (u v : Nat) : Decidable (J.IsParent g u v) :=
  inferInstanceAs (Decidable (u < g.n ∧ u ≠ v ∧ J.Anc u v ∧ ∀ w, w < g.n → w ≠ v → J.Anc w v → J.Anc w u))

end SmcIrred
