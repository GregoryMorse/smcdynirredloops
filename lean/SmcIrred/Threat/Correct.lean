module

public import SmcIrred.Spec.Threat
public import SmcIrred.Dynamic.StaticScheme
public import SmcIrred.Dynamic.FinalExec

public section

namespace SmcIrred.Threat

open Lang Dyn

/-- Under S1 the run-time value of a required variable is its intended value (the solver's output on a planted formula). -/
theorem rtVal_planted {d : Design} (hA : Assumptions d) {k : Nat} (hk : k < d.n) (hr : d.req k) :
    rtVal d.img k = d.σ k := by
  obtain ⟨sol, hsol, hout⟩ := planted_smc (extra := d.extra) hA.planted hA.extra_respects hA.extra_wf
  unfold rtVal
  rw [hA.stamped, hsol]
  exact hout k hk hr

/-- Under S1 the solver succeeds on the stamped formula (S1 is what makes the formula satisfiable). -/
theorem solver_succeeds {d : Design} (hA : Assumptions d) : smcSolve d.img.formula ≠ none := by
  obtain ⟨sol, hsol, _⟩ := planted_smc (extra := d.extra) hA.planted hA.extra_respects hA.extra_wf
  rw [hA.stamped, hsol]; simp

theorem trace_obfuscated {orig prog : Stmt} (h : Obfuscates orig prog) (c : Bool) :
    trace prog c true = trace orig c true := by
  cases h <;> cases c <;> decide

/-- T1 (correctness). Under S1 and S2 the obfuscated image executes exactly the blocks of the original program, for both
values of its condition (so it computes the same function whatever the blocks do); under S3 the final values of the
dynamic scheme's schedule are the values of the circuit, from every initial state. -/
theorem correct {d : Design} (hA : Assumptions d) (ho : Obfuscates d.orig d.img.prog) :
    (∀ c, d.img.run c = trace d.orig c true) ∧
    (∀ σ0 τ : Nat → Bool, ∀ v, v < d.circ.n → runA d.circ σ0 d.acts v = valOf d.circ τ v) := by
  refine ⟨fun c => ?_, fun σ0 τ v hv => final_exec_eq_val d.circ hA.schedule_topo hA.schedule_ordered σ0 τ v hv⟩
  unfold Image.run
  rw [traceS_of_reads_false d.img.prog ?_ c true, trace_obfuscated ho c]
  intro i hi
  obtain ⟨hn, hr, hs⟩ := hA.cells_planted i hi
  rw [rtVal_planted hA hn hr, hs]

end SmcIrred.Threat
