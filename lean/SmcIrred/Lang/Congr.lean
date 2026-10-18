module

public import SmcIrred.Spec.LangFigs

public section

namespace SmcIrred.Lang

theorem Cond.eval_congr {sol sol' : Nat → Bool} (env v : Bool) :
    ∀ k : Cond, (∀ i ∈ k.reads, sol i = sol' i) → k.eval sol env v = k.eval sol' env v := by
  intro k
  induction k generalizing v with
  | falseC => intro _; rfl
  | ttf => intro _; rfl
  | c => intro _; rfl
  | out k => intro h; simp only [Cond.eval]; rw [h k (by simp [Cond.reads])]
  | neg k ih => intro h; simp only [Cond.eval]; rw [ih v h]
  | and a b iha ihb =>
    intro h
    have ha : ∀ i ∈ a.reads, sol i = sol' i := fun i hi => h i (by simp [Cond.reads, hi])
    have hb : ∀ i ∈ b.reads, sol i = sol' i := fun i hi => h i (by simp [Cond.reads, hi])
    simp only [Cond.eval]
    rw [iha v ha, ihb (a.eval sol' env v).2 hb]

theorem getD_halt_mem (code : List Instr) (pc : Nat) : code.getD pc .halt = .halt ∨ code.getD pc .halt ∈ code := by
  by_cases h : pc < code.length
  · right
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    exact List.getElem_mem h
  · left
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

/-- The result of running a program depends on the generator outputs only through those it reads. -/
theorem exec_congr {code : List Instr} {sol sol' : Nat → Bool} (h : ∀ i ∈ codeReads code, sol i = sol' i) (env : Bool) :
    ∀ f pc v tr, exec f code sol env pc v tr = exec f code sol' env pc v tr := by
  intro f
  induction f with
  | zero => intro _ _ _; rfl
  | succ f ih =>
    intro pc v tr
    unfold exec
    cases hi : code.getD pc .halt with
    | blk a => simp only []; exact ih _ _ _
    | jmp t => simp only []; exact ih _ _ _
    | halt => rfl
    | jmpIf k t =>
      have hk : ∀ i ∈ k.reads, sol i = sol' i := by
        intro i hi'
        apply h i
        rcases getD_halt_mem code pc with h0 | h0
        · rw [hi] at h0; cases h0
        · rw [hi] at h0
          unfold codeReads
          simp only [List.mem_flatMap]
          exact ⟨_, h0, by simpa [Instr.reads] using hi'⟩
      simp only []
      rw [Cond.eval_congr env v k hk]
      exact ih _ _ _

/-- A program whose generator outputs it reads are all false runs as with the constant-false outputs. -/
theorem traceS_of_reads_false {sol : Nat → Bool} (p : Stmt) (h : ∀ i ∈ codeReads (compile p), sol i = false) (c v : Bool) :
    traceS sol p c v = trace p c v := by
  unfold trace traceS
  apply exec_congr _ c
  intro i hi
  exact h i hi

end SmcIrred.Lang
