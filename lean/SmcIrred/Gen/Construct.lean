module

public import SmcIrred.Gen.Planted
public import SmcIrred.Dynamic.StaticSchemeGeneral

public section

namespace SmcIrred

/-! # The planted generator as an algorithm (R19b, Section 3.1)

`native/protected.c` builds the forest of a planted formula by giving every required variable `x` a forcing chain
`(x, ¬σ x) ⇒ (m₁, σ m₁) ⇒ … ⇒ (x, σ x)` through intermediate variables `mᵢ` (chosen by a pseudo-random generator, a black box
here) and adds random implications that respect `σ`. `genForest` is that construction with the random choices as parameters;
`genForest_planted` proves that whatever the choices are, the result is a planted forest. -/

/-- The chain from the literal `cur` through the variables `ms` (each reached at its `σ`-true literal) to `(x, σ x)`. -/
@[expose] def chainFrom (σ : Nat → Bool) : Lit → List Nat → Nat → List (Lit × Lit)
  | cur, [], x => [(cur, ⟨x, σ x⟩)]
  | cur, m :: ms, x => (cur, ⟨m, σ m⟩) :: chainFrom σ ⟨m, σ m⟩ ms x

/-- The forcing chain of the required variable `x`. -/
@[expose] def chain (σ : Nat → Bool) (x : Nat) (ms : List Nat) : List (Lit × Lit) := chainFrom σ ⟨x, !σ x⟩ ms x

/-- The forest of the chains of the specification `(x, intermediate variables)`. -/
@[expose] def genForest (σ : Nat → Bool) (specs : List (Nat × List Nat)) : List (Lit × Lit) :=
  specs.flatMap fun s => chain σ s.1 s.2

/-- The random implications kept by the generator: those that respect `σ` and stay among the `n` variables. -/
@[expose] def genExtra (n : Nat) (σ : Nat → Bool) (cands : List (Lit × Lit)) : List (Lit × Lit) :=
  cands.filter fun e => !(σ e.1.var == e.1.pos && σ e.2.var != e.2.pos) && decide (e.1.var < n) && decide (e.2.var < n)

theorem ImpPath.mono {l l' : List (Lit × Lit)} (h : ∀ e ∈ l, e ∈ l') {a b : Lit} (p : ImpPath l a b) : ImpPath l' a b := by
  induction p with
  | refl _ => exact .refl _
  | step he _ ih => exact .step (h _ he) ih

theorem chainFrom_path (σ : Nat → Bool) (x : Nat) : ∀ (ms : List Nat) (cur : Lit),
    ImpPath (chainFrom σ cur ms x) cur ⟨x, σ x⟩ := by
  intro ms
  induction ms with
  | nil => intro cur; exact .step (by simp [chainFrom]) (.refl _)
  | cons m ms ih =>
    intro cur
    refine .step (b := ⟨m, σ m⟩) (by simp [chainFrom]) ?_
    exact (ih ⟨m, σ m⟩).mono (fun e he => by simp [chainFrom, he])

theorem chainFrom_target (σ : Nat → Bool) (x : Nat) : ∀ (ms : List Nat) (cur : Lit), ∀ e ∈ chainFrom σ cur ms x,
    e.2.Holds σ := by
  intro ms
  induction ms with
  | nil => intro cur e he; simp [chainFrom] at he; subst he; rfl
  | cons m ms ih =>
    intro cur e he
    simp only [chainFrom, List.mem_cons] at he
    rcases he with rfl | he
    · rfl
    · exact ih _ e he

theorem chainFrom_wf (σ : Nat → Bool) {n x : Nat} (hx : x < n) : ∀ (ms : List Nat) (cur : Lit), cur.var < n →
    (∀ m ∈ ms, m < n) → ∀ e ∈ chainFrom σ cur ms x, e.1.var < n ∧ e.2.var < n := by
  intro ms
  induction ms with
  | nil => intro cur hc _ e he; simp [chainFrom] at he; subst he; exact ⟨hc, hx⟩
  | cons m ms ih =>
    intro cur hc hm e he
    simp only [chainFrom, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨hc, hm m (by simp)⟩
    · exact ih ⟨m, σ m⟩ (hm m (by simp)) (fun m' h' => hm m' (by simp [h'])) e he

/-- The generator is correct for every choice of intermediate variables: a specification that covers every required variable
below `n` and stays among the `n` variables generates a planted forest. -/
theorem genForest_planted {n : Nat} {σ : Nat → Bool} {req : Nat → Prop} {specs : List (Nat × List Nat)}
    (hs : ∀ s ∈ specs, s.1 < n ∧ ∀ m ∈ s.2, m < n)
    (hc : ∀ x, x < n → req x → ∃ ms, (x, ms) ∈ specs) : Planted n σ req (genForest σ specs) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    simp only [genForest, List.mem_flatMap] at he
    obtain ⟨s, hsm, he⟩ := he
    obtain ⟨h1, h2⟩ := hs s hsm
    exact chainFrom_wf σ h1 s.2 ⟨s.1, !σ s.1⟩ h1 h2 e he
  · intro e he
    simp only [genForest, List.mem_flatMap] at he
    obtain ⟨s, _, he⟩ := he
    have := chainFrom_target σ s.1 s.2 ⟨s.1, !σ s.1⟩ e he
    exact fun h => h.2 this
  · intro x hx hr
    obtain ⟨ms, hm⟩ := hc x hx hr
    exact (chainFrom_path σ x ms ⟨x, !σ x⟩).mono (fun e he => by
      simp only [genForest, List.mem_flatMap]
      exact ⟨(x, ms), hm, he⟩)

theorem genExtra_respects {n : Nat} {σ : Nat → Bool} {cands : List (Lit × Lit)} :
    ∀ e ∈ genExtra n σ cands, Respecting σ e := by
  intro e he
  simp only [genExtra, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at he
  obtain ⟨_, ⟨h1, _⟩, _⟩ := he
  intro ⟨ha, hb⟩
  simp only [Lit.Holds] at ha hb
  simp [ha, hb] at h1

theorem genExtra_wf {n : Nat} {σ : Nat → Bool} {cands : List (Lit × Lit)} :
    ∀ e ∈ genExtra n σ cands, e.1.var < n ∧ e.2.var < n := by
  intro e he
  simp only [genExtra, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at he
  exact ⟨he.2.1.2, he.2.2⟩

/-- The static scheme for arbitrary goto-free code with a generated planted formula: for every choice of the generator's random
choices (the specification of the forcing chains and the candidate implications), the solver on the generated formula gives
the outputs `1` and `2` the planted value false, the protected code `prot5 S T` returns the trace and state of `S; T`, and every
valid jungle of its flow graph has an irreducible loop. The specification must cover the required variables `1` and `2`. -/
theorem generated_scheme {n : Nat} {σ : Nat → Bool} {specs : List (Nat × List Nat)} {cands : List (Lit × Lit)}
    (hs : ∀ s ∈ specs, s.1 < n ∧ ∀ m ∈ s.2, m < n) (h1n : 1 < n) (h2n : 2 < n)
    (hc1 : ∃ ms, (1, ms) ∈ specs) (hc2 : ∃ ms, (2, ms) ∈ specs) (hs1 : σ 1 = false) (hs2 : σ 2 = false)
    {S T : Lang.Stmt} (hS : Lang.Structured S) (hT : Lang.Structured T) (hS1 : 1 ≤ S.size) :
    ∃ sol, smcSolve (impFormula n (genForest σ specs ++ genExtra n σ cands)) = some sol ∧
      (let o : Nat → Bool := fun k => decide (2 * k ∈ sol)
       o 1 = false ∧ o 2 = false ∧
       ∀ (env v : Bool) (r : List Nat × Bool),
         ((∃ f, Lang.exec f (Lang.compile (.seq S T)) o env 0 v [] = some r) ↔
           ∃ f, Lang.exec f (Lang.compile (Lang.prot5 S T)) o env 0 v [] = some r)) ∧
      (Lang.cfgOf (Lang.compile (.seq S T))).Reducible 0 ∧
      (∀ {J : Jungle}, J.Valid (Lang.cfgOf (Lang.compile (Lang.prot5 S T))) 0 →
        ∃ w, (Lang.cfgOf (Lang.compile (Lang.prot5 S T))).Irreducible J w) := by
  have hp : Planted n σ (fun x => x = 1 ∨ x = 2) (genForest σ specs) := by
    refine genForest_planted hs ?_
    intro x _ hx
    rcases hx with rfl | rfl
    · exact hc1
    · exact hc2
  exact static_scheme_general hp genExtra_respects genExtra_wf h1n h2n (Or.inl rfl) (Or.inr rfl) hs1 hs2 hS hT hS1

end SmcIrred
