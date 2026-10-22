module

public import SmcIrred.Spec.Threat
public import SmcIrred.Dynamic.StaticScheme
public import SmcIrred.Dynamic.FinalExec
public import SmcIrred.Lang.ProtectW
public import SmcIrred.Lang.Congr

public section

namespace SmcIrred.Threat

open Lang Dyn

/-- Under S1 the run-time value of a required variable is its intended value (the solver's output on a planted formula). -/
theorem rtVal_planted {d : Design} (hA : Assumptions d) {k : Nat} (hk : k < d.n) (hr : d.req k) :
    rtVal d.img k = d.σ k := by
  obtain ⟨sol, hsol, hout⟩ := planted_smc (extra := d.extra) hA.planted hA.extra_respects d.extra_wf
  unfold rtVal
  rw [hA.stamped, hsol]
  exact hout k hk hr

/-- Under S1 the solver succeeds on the stamped formula (S1 is what makes the formula satisfiable). -/
theorem solver_succeeds {d : Design} (hA : Assumptions d) : smcSolve d.img.formula ≠ none := by
  obtain ⟨sol, hsol, _⟩ := planted_smc (extra := d.extra) hA.planted hA.extra_respects d.extra_wf
  rw [hA.stamped, hsol]; simp

/-- Without any generator output (all false), the obfuscated program halts with the same results as the original program. -/
theorem obf_runs {orig prog : Stmt} (ho : Obfuscates orig prog) (c : Bool) (r : List Nat × Bool) :
    Runs (fun _ => false) prog c r ↔ Runs (fun _ => false) orig c r := by
  cases ho with
  | b5 hS hT => exact (prot5_equiv hS hT rfl rfl c true r).symm
  | c5 hS hT hp => exact (protC_equiv hS hT (hp c).1 (hp c).2 (by simp [Cond.eval]) r).symm
  | b6 hS hT => exact (prot6_equiv hS hT _ rfl c true r).symm
  | c6 hS hT hp => exact (protC6_equiv hS hT (hp c).1 (hp c).2.1 (hp c).2.2 (by simp [Cond.eval]) r).symm

/-- T1 (correctness). Under S1 and S2 the obfuscated image behaves as the original program, for both values of its condition
(so it computes the same function whatever the goto-free blocks do); under S3 the final values of the dynamic scheme's
schedule are the values of the circuit, from every initial state. -/
theorem correct {d : Design} (hA : Assumptions d) (ho : Obfuscates d.orig d.img.prog) :
    d.img.Behaves d.orig ∧
    (∀ σ0 τ : Nat → Bool, ∀ v, v < d.circ.n → runA d.circ σ0 d.acts v = valOf d.circ τ v) := by
  refine ⟨fun c r => ?_, fun σ0 τ v hv => final_exec_eq_val d.circ hA.schedule_topo hA.schedule_ordered σ0 τ v hv⟩
  have hs : ∀ i ∈ codeReads (compile d.img.prog), rtVal d.img i = (fun _ => false) i := by
    intro i hi
    obtain ⟨hn, hr, hs⟩ := hA.cells_planted i hi
    rw [rtVal_planted hA hn hr, hs]
  have hc : ∀ f, exec f (compile d.img.prog) (rtVal d.img) c 0 true [] =
      exec f (compile d.img.prog) (fun _ => false) c 0 true [] := fun f => exec_congr hs c f 0 true []
  have : Runs (rtVal d.img) d.img.prog c r ↔ Runs (fun _ => false) d.img.prog c r := by
    unfold Runs; simp only [hc]
  exact this.trans (obf_runs ho c r)

end SmcIrred.Threat
