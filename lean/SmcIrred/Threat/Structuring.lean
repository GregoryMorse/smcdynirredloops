module

public import SmcIrred.Spec.Threat
public import SmcIrred.Struct.Flatten
public import SmcIrred.Extremal.Kn

public section

namespace SmcIrred.Threat

open Struct

/-- T4a (the class `Struct`: state variables). For every well-formed control-flow graph one variable `state` with the
`|V| + 1` values `0 … |V|` reproduces the run of the graph, so flattening to a single dispatch loop is always possible, with
no code duplication. -/
theorem one_variable_suffices (g : Digraph) (hwf : WFg g) (lab : Nat → List Nat) (ch : Nat → Nat) :
    (∀ v k t, v < g.n → (Walk g lab ch v k t ↔ FRun g lab ch v k t)) ∧
    (∀ s k, s < g.n → nextState g ch s k < g.n + 1) :=
  ⟨fun _ _ _ hv => flatten_iff hwf hv, fun _ _ hs => state_range hwf hs _⟩

/-- T4b (what "quadratic" counts). In the complete graph on `n` vertices with its chain jungle the number of multi-entry
edges satisfies `2 · MEE = (n − 1)(n − 2)`: the quadratic quantity is that count of edges, not a cost of any restructuring
algorithm. No lower bound on node splitting is claimed (G33). -/
theorem quadratic_is_edge_count (n : Nat) : 2 * (Kn n).meeCount (chainJungle n) = (n - 1) * (n - 2) :=
  Kn_meeCount n

end SmcIrred.Threat
