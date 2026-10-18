module

public import SmcIrred.Smc.Solve

public section

namespace SmcIrred

theorem restamp_init (n : Nat) (s : SState) (h : s.stk = []) : restamp n s = SState.init n := by
  cases s
  simp_all [restamp, SState.init]

/-- A finished run leaves the machine stack empty. -/
theorem sRun_stk_nil (g : Digraph) :
    (sRun g (g.n - 1) (List.range g.n) (SState.init g.n)).stk = [] := by
  have hR := sRun_sim g (g.n - 1) rfl (List.range g.n) TState.init (SState.init g.n) (SRel.init g)
    (by intro v hv; simpa using hv)
  obtain ⟨hI, -, -⟩ := tRun_spec (revG g) (List.range g.n) TState.init (TInv.init (revG g))
    (by intro v hv; simpa [revG] using hv)
  have h1 : (tRun (revG g) (List.range g.n) TState.init).stk = [] := hI.stk_nil
  have h2 := hR.stk
  simp only [StkRel] at h2
  rw [h2, h1]
  rfl

/-- Reuse by restamping (C39): after a run the restamped image is the stamped image again, so `k` successive queries
give `k` copies of the single answer. -/
theorem smcRound_restamp (f : TwoSat) :
    smcRound f (SState.init f.graph.n) = (smcSolve f, SState.init f.graph.n) := by
  unfold smcRound smcSolve
  simp only
  rw [restamp_init _ _ (sRun_stk_nil f.graph)]

theorem smcRounds_replicate (f : TwoSat) : ∀ k, smcRounds f k (SState.init f.graph.n) = List.replicate k (smcSolve f) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [smcRounds, smcRound_restamp, ih]
    rfl

end SmcIrred
