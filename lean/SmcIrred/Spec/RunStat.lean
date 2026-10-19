module

public import SmcIrred.Spec.Circuit

public section

namespace SmcIrred

/-! # The statistic of `do_run_virtual` (`python/virt.py`, G29)

`edgecount` of one run adds `len(pred[x])` for every vertex `x` of the dependency order, and `pred[x]` contains the start token
`0` for every active input `x` (`for x in inp: pred[x].add(0)`): `pyEdges` is that number. A call stores the statistic of its
subgraph run in a dictionary keyed by the subgraph: the statistic of the first run and the number of runs (`dictAdd`); `show_stats`
reports `own + sum over keys of statistic * count` (`dictTotal`). -/

/-- The edges counted by one run: the predecessors of every vertex plus one start-token edge per active input. -/
@[expose] def pyEdges (c : Circ) (inp : Nat → Bool) : Nat :=
  ((List.range c.n).map fun x => (c.pred x).length + (if inp x then 1 else 0)).sum

/-- The statistic of one run: (vertices, edges). -/
@[expose] def pyOwn (c : Circ) (inp : Nat → Bool) : Nat × Nat := (c.n, pyEdges c inp)

/-- The statistics dictionary: key, statistic of the first run, number of runs. -/
abbrev StatDict := List (Nat × (Nat × Nat) × Nat)

/-- Record one more run of the subgraph `sid` with statistic `st`: the count grows, the statistic of the first run stays. -/
@[expose] def dictAdd (d : StatDict) (sid : Nat) (st : Nat × Nat) : StatDict :=
  if d.any (fun e => e.1 == sid) then d.map (fun e => if e.1 == sid then (e.1, e.2.1, e.2.2 + 1) else e)
  else d ++ [(sid, st, 1)]

/-- The dictionary after the runs `(sid, statistic)` in order. -/
@[expose] def dictOf (runs : List (Nat × (Nat × Nat))) : StatDict := runs.foldl (fun d r => dictAdd d r.1 r.2) []

/-- The weighted sum of the statistic component `f` over the dictionary entries (`f = Prod.fst`: vertices, `Prod.snd`: edges). -/
@[expose] def dW (f : Nat × Nat → Nat) (d : StatDict) : Nat := (d.map fun e => f e.2.1 * e.2.2).sum

/-- The sum of the statistic component `f` over the runs. -/
@[expose] def runsW (f : Nat × Nat → Nat) (runs : List (Nat × (Nat × Nat))) : Nat := (runs.map fun r => f r.2).sum

/-- `show_stats`: vertices and edges of the dictionary entries weighted by their counts. -/
@[expose] def dictTotal (d : StatDict) : Nat × Nat := (dW Prod.fst d, dW Prod.snd d)

/-- The sums of the statistics over the runs. -/
@[expose] def runsTotal (runs : List (Nat × (Nat × Nat))) : Nat × Nat := (runsW Prod.fst runs, runsW Prod.snd runs)

end SmcIrred
