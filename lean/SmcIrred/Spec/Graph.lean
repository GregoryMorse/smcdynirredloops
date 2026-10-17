module

public section

namespace SmcIrred

/-- A finite directed graph on vertices `0 … n-1`, given by its edge relation. -/
structure Digraph where
  n : Nat
  edge : Nat → Nat → Bool

/-- Reachability in at most `k` edges. -/
@[expose] def Digraph.reachIn (g : Digraph) : Nat → Nat → Nat → Bool
  | 0, a, b => a == b
  | k + 1, a, b => a == b || (List.range g.n).any fun c => g.edge a c && g.reachIn k c b

end SmcIrred
