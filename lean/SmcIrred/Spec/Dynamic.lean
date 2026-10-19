module

public section

namespace SmcIrred.Dyn

/-! The dynamic scheme (Section 5): a circuit is a DAG of vertices; a schedule is a finite sequence of vertex executions
(a vertex may repeat); an execution of `v` reads the *current* values of the predecessors of `v` and writes the value of `v`.
A fault replaces the value written by an execution by an arbitrary value. -/

structure DCirc (α : Type) where
  n : Nat
  ps : Nat → List Nat
  f : Nat → List α → α

/-- The vertices are numbered topologically: every predecessor of `v` is smaller. -/
@[expose] def DCirc.Topo {α : Type} (c : DCirc α) : Prop := ∀ v, v < c.n → ∀ u ∈ c.ps v, u < v

/-- An action: execute `v` (`none`) or write the arbitrary value `d` into `v` (`some d`, a faulty execution of `v`). -/
abbrev Act (α : Type) := Nat × Option α

@[expose] def stepA {α : Type} (c : DCirc α) (σ : Nat → α) : Act α → (Nat → α)
  | (v, none) => fun w => if w = v then c.f v ((c.ps v).map σ) else σ w
  | (v, some d) => fun w => if w = v then d else σ w

/-- The values after running the actions from the initial values `σ`. -/
@[expose] def runA {α : Type} (c : DCirc α) (σ : Nat → α) (acts : List (Act α)) : Nat → α := acts.foldl (stepA c) σ

/-- A schedule without faults. -/
@[expose] def execs {α : Type} (s : List Nat) : List (Act α) := s.map fun v => (v, none)

/-- The values satisfy the equations of the circuit. -/
@[expose] def IsVal {α : Type} (c : DCirc α) (x : Nat → α) : Prop :=
  ∀ v, v < c.n → x v = c.f v ((c.ps v).map x)

/-- The final executions are in order: every vertex `v` is executed (not faultily) at its last write, and after that last
execution no predecessor of `v` is written. -/
@[expose] def FinalOrdered {α : Type} (c : DCirc α) (acts : List (Act α)) : Prop :=
  ∀ v, v < c.n → ∃ pre post, acts = pre ++ (v, none) :: post ∧ (∀ a ∈ post, a.1 ≠ v) ∧
    ∀ u ∈ c.ps v, ∀ a ∈ post, a.1 ≠ u

/-- The values of the circuit: the result of executing every vertex once in the topological order. -/
@[expose] def valOf {α : Type} (c : DCirc α) (σ : Nat → α) : Nat → α := runA c σ (execs (List.range c.n))

/-- The position of the last execution of `v` in a schedule. -/
@[expose] def lastIdx (s : List Nat) (v : Nat) : Option Nat :=
  ((List.range s.length).filter fun i => s.getD i 0 = v).getLast?

/-- The number of extra executions of the vertex `v` fixed by the condition outputs `o`: one for each of its condition variables
that is true. -/
@[expose] def condReps (cs : Nat → List Nat) (o : Nat → Bool) (v : Nat) : Nat := ((cs v).filter fun i => o i).length

/-- The schedule fixed by the condition outputs `o` for a circuit with `n` vertices: the vertices in numbering order, vertex `v`
executed `1 + condReps cs o v` times in a row. -/
@[expose] def condSchedule (cs : Nat → List Nat) (o : Nat → Bool) (n : Nat) : List Nat :=
  (List.range n).flatMap fun v => List.replicate (condReps cs o v + 1) v

end SmcIrred.Dyn
