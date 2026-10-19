module

public import SmcIrred.Spec.ProtectedProgs
public import SmcIrred.Lang.ProtectMany
public import SmcIrred.Lang.ProtectClose

public section

namespace SmcIrred.Lang

/-- **Protected AES-128** (`aes_protected` of `native/protected.c`): the three protections `PROT5` (the pairs SubBytes/ShiftRows
and MixColumns/AddRoundKey of the round loop and SubBytes/ShiftRows of the last round) on the control-flow model of
`aes_plain`. The plain program has a reducible control-flow graph without irreducible loops in any valid jungle; the protected
code has an irreducible loop in every valid jungle (and valid jungles exist); and when the solver's outputs `1` and `2` are
false the protected code returns what the plain code returns. -/
theorem aes_protected :
    let Q := protectMany (compile aesPlain)
      [⟨7, 8, 9, .out 1, .out 2⟩, ⟨4, 5, 6, .out 1, .out 2⟩, ⟨2, 3, 4, .out 1, .out 2⟩]
    (cfgOf (compile aesPlain)).Reducible 0 ∧
    (∀ {J : Jungle}, J.Valid (cfgOf (compile aesPlain)) 0 → ∀ w, ¬ (cfgOf (compile aesPlain)).Irreducible J w) ∧
    (∀ {J : Jungle}, J.Valid (cfgOf Q) 0 → ∃ w, (cfgOf Q).Irreducible J w) ∧
    (∃ J : Jungle, J.Valid (cfgOf Q) 0) ∧
    (∀ {sol : Nat → Bool} {env : Bool}, sol 1 = false → sol 2 = false → ∀ (v : Bool) (res : List Nat × Bool),
      ((∃ f, exec f (compile aesPlain) sol env 0 v [] = some res) ↔ ∃ f, exec f Q sol env 0 v [] = some res)) := by
  have hs : Structured aesPlain := by simp [aesPlain, Structured]
  have hsub : Sub (.seq (.blk 1) (.blk 2)) 2 aesPlain 0 :=
    Sub.seqR (Sub.seqL (Sub.whl (Sub.seqL Sub.refl)))
  have hok : RegsOk (compile aesPlain).length
      ([⟨7, 8, 9, .out 1, .out 2⟩, ⟨4, 5, 6, .out 1, .out 2⟩] ++
        [⟨2, 2 + (Stmt.blk 1).size, 2 + (Stmt.blk 1).size + (Stmt.blk 2).size, .out 1, .out 2⟩]) := by
    simp [RegsOk, compile_length, aesPlain, Stmt.size]
  have := protect_many_structured hs hsub (by simp [Stmt.size]) (by simp [Stmt.size]) (.out 1) (.out 2)
    [⟨7, 8, 9, .out 1, .out 2⟩, ⟨4, 5, 6, .out 1, .out 2⟩] hok
  obtain ⟨h1, h2, h3, h4, h5⟩ := this
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · intro J hv; exact h3 hv
  · exact h4
  · intro sol env e1 e2 v res
    apply h5
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl <;> exact ⟨fun v => by simp [Cond.eval, e1], fun v => by simp [Cond.eval, e2]⟩

/-- **Protected modular exponentiation** (`modexp_protected`): `PROT6` (Figure 6(b)) around the conditional multiplication and the
squaring in the exponent loop. -/
theorem modexp_protected :
    let Q := protectClose (compile modexpPlain) 2 5 (.out 1)
    (cfgOf (compile modexpPlain)).Reducible 0 ∧
    (∀ {J : Jungle}, J.Valid (cfgOf (compile modexpPlain)) 0 → ∀ w, ¬ (cfgOf (compile modexpPlain)).Irreducible J w) ∧
    (∀ {J : Jungle}, J.Valid (cfgOf Q) 0 → ∃ w, (cfgOf Q).Irreducible J w) ∧
    (∃ J : Jungle, J.Valid (cfgOf Q) 0) ∧
    (∀ {sol : Nat → Bool} {env : Bool}, sol 1 = false → ∀ (v : Bool) (res : List Nat × Bool),
      ((∃ f, exec f (compile modexpPlain) sol env 0 v [] = some res) ↔ ∃ f, exec f Q sol env 0 v [] = some res)) := by
  have hs : Structured modexpPlain := by simp [modexpPlain, Structured]
  have hsub : Sub (.seq (.ite1 (.out 4) (.blk 1)) (.blk 2)) 2 modexpPlain 0 :=
    Sub.seqR (Sub.seqL (Sub.whl Sub.refl))
  have := protect6_structured hs hsub (by simp [Stmt.size]) (by simp [Stmt.size]) (.out 1)
  obtain ⟨h1, h2, h3, h4, h5⟩ := this
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · intro J hv; exact h3 hv
  · exact h4
  · intro sol env e1 v res
    exact h5 (fun v => by simp [Cond.eval, e1]) v res

end SmcIrred.Lang
