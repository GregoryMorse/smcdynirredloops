module

public import SmcIrred.Lang.ProtIrred
public import SmcIrred.Dynamic.StaticScheme

public section

namespace SmcIrred

open Lang

/-- C15, C76, C65 for arbitrary goto-free code (the general form of `static_scheme`): for a planted formula whose desired
assignment makes the variables `1` and `2` false the self-modifying-code solver returns a solution whose outputs `1` and `2`
are false; for every goto-free `S` (at least one instruction) and `T` the protected code `prot5 S T`, whose opaque conditions
are these two outputs, returns the same trace and state as `S; T` (for every environment and state of the toggled variable),
the original has a reducible control-flow graph, and every valid depth-first jungle of the protected one has an irreducible
loop. -/
theorem static_scheme_general {n : Nat} {σ : Nat → Bool} {req : Nat → Prop} {forest extra : List (Lit × Lit)}
    (hp : Planted n σ req forest) (hx : ∀ e ∈ extra, Respecting σ e) (hwx : ∀ e ∈ extra, e.1.var < n ∧ e.2.var < n)
    (h1n : 1 < n) (h2n : 2 < n) (hr1 : req 1) (hr2 : req 2) (hs1 : σ 1 = false) (hs2 : σ 2 = false)
    {S T : Stmt} (hS : Structured S) (hT : Structured T) (hS1 : 1 ≤ S.size) :
    ∃ sol, smcSolve (impFormula n (forest ++ extra)) = some sol ∧
      (let o : Nat → Bool := fun k => decide (2 * k ∈ sol)
       o 1 = false ∧ o 2 = false ∧
       ∀ (env v : Bool) (r : List Nat × Bool),
         ((∃ f, exec f (compile (.seq S T)) o env 0 v [] = some r) ↔
           ∃ f, exec f (compile (prot5 S T)) o env 0 v [] = some r)) ∧
      (cfgOf (compile (.seq S T))).Reducible 0 ∧
      (∀ {J : Jungle}, J.Valid (cfgOf (compile (prot5 S T))) 0 → ∃ w, (cfgOf (compile (prot5 S T))).Irreducible J w) := by
  obtain ⟨sol, hsol, hout⟩ := planted_smc (extra := extra) hp hx hwx
  have e1 := hout 1 h1n hr1
  have e2 := hout 2 h2n hr2
  rw [hs1] at e1
  rw [hs2] at e2
  have hpr := protection5 hS hT hS1
  refine ⟨sol, hsol, ⟨e1, e2, fun env v r => hpr.2.2.2.2 e1 e2 env v r⟩, hpr.1, hpr.2.2.1⟩

/-- The same for Figure 6(b): `if (c) S; T` against its protected form with the single opaque condition `1`. -/
theorem static_scheme_general6 {n : Nat} {σ : Nat → Bool} {req : Nat → Prop} {forest extra : List (Lit × Lit)}
    (hp : Planted n σ req forest) (hx : ∀ e ∈ extra, Respecting σ e) (hwx : ∀ e ∈ extra, e.1.var < n ∧ e.2.var < n)
    (h1n : 1 < n) (hr1 : req 1) (hs1 : σ 1 = false)
    {S T : Stmt} (hS : Structured S) (hT : Structured T) (hS1 : 1 ≤ S.size) (cd : Cond) :
    ∃ sol, smcSolve (impFormula n (forest ++ extra)) = some sol ∧
      (let o : Nat → Bool := fun k => decide (2 * k ∈ sol)
       o 1 = false ∧
       ∀ (env v : Bool) (r : List Nat × Bool),
         ((∃ f, exec f (compile (.seq (.ite1 cd S) T)) o env 0 v [] = some r) ↔
           ∃ f, exec f (compile (prot6 cd S T)) o env 0 v [] = some r)) ∧
      (cfgOf (compile (.seq (.ite1 cd S) T))).Reducible 0 ∧
      (∀ {J : Jungle}, J.Valid (cfgOf (compile (prot6 cd S T))) 0 → ∃ w, (cfgOf (compile (prot6 cd S T))).Irreducible J w) := by
  obtain ⟨sol, hsol, hout⟩ := planted_smc (extra := extra) hp hx hwx
  have e1 := hout 1 h1n hr1
  rw [hs1] at e1
  have hpr := protection6 hS hT hS1 cd
  refine ⟨sol, hsol, ⟨e1, fun env v r => hpr.2.2.2.2 e1 env v r⟩, hpr.1, hpr.2.2.1⟩

end SmcIrred
