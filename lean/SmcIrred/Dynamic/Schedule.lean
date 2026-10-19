module

public import SmcIrred.Dynamic.FinalExec

public section

namespace SmcIrred.Dyn

/-! # The schedule fixed by the solver's condition outputs (C77, G34 a)

Every vertex has a list of condition variables; the outputs `o` of the solver decide how many of them are true, and the vertex
is executed once more for each. The final executions are in dependency order whatever `o` is, the final values are the circuit's
values, and the length is at most `(k + 1) |V|` when every vertex has at most `k` conditions: the bound on the repetitions
follows from the structure (a list of at most `k` condition variables per vertex), not from the solver's behaviour. -/

theorem condSchedule_succ (cs : Nat → List Nat) (o : Nat → Bool) (n : Nat) :
    condSchedule cs o (n + 1) = condSchedule cs o n ++ List.replicate (condReps cs o n + 1) n := by
  unfold condSchedule
  rw [List.range_succ, List.flatMap_append]
  simp

theorem condSchedule_mem (cs : Nat → List Nat) (o : Nat → Bool) (n : Nat) : ∀ x ∈ condSchedule cs o n, x < n := by
  induction n with
  | zero => intro x hx; simp [condSchedule] at hx
  | succ n ih =>
    intro x hx
    rw [condSchedule_succ] at hx
    rcases List.mem_append.1 hx with h | h
    · have := ih x h; omega
    · have := List.eq_of_mem_replicate h; omega

theorem condSchedule_length (cs : Nat → List Nat) (o : Nat → Bool) (k : Nat) (hk : ∀ v, (cs v).length ≤ k) :
    ∀ n, (condSchedule cs o n).length ≤ (k + 1) * n := by
  intro n
  induction n with
  | zero => simp [condSchedule]
  | succ n ih =>
    rw [condSchedule_succ, List.length_append, List.length_replicate]
    have h1 : condReps cs o n ≤ k := by
      unfold condReps
      exact Nat.le_trans (List.length_filter_le _ _) (hk n)
    rw [Nat.mul_succ]
    omega

theorem condSchedule_ordered (c : DCirc Bool) (hT : c.Topo) (cs : Nat → List Nat) (o : Nat → Bool) :
    FinalOrdered c (execs (condSchedule cs o c.n) : List (Act Bool)) := by
  intro v hv
  obtain ⟨post, hp, hx⟩ := range_split c.n v hv
  have e : condSchedule cs o c.n = (condSchedule cs o v ++ List.replicate (condReps cs o v) v) ++ v ::
      (post.flatMap fun x => List.replicate (condReps cs o x + 1) x) := by
    unfold condSchedule
    rw [hp, List.flatMap_append, List.flatMap_cons, List.replicate_succ']
    simp
  refine ⟨execs (condSchedule cs o v ++ List.replicate (condReps cs o v) v),
    execs (post.flatMap fun x => List.replicate (condReps cs o x + 1) x), ?_, ?_, ?_⟩
  · rw [execs, e]; simp [execs]
  · intro a ha
    simp only [execs, List.mem_map] at ha
    obtain ⟨x, hxm, rfl⟩ := ha
    obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.1 hxm
    have := List.eq_of_mem_replicate hxy
    have := hx y hy
    simp; omega
  · intro u hu a ha
    simp only [execs, List.mem_map] at ha
    obtain ⟨x, hxm, rfl⟩ := ha
    obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.1 hxm
    have h0 := List.eq_of_mem_replicate hxy
    have h1 := hx y hy
    have h2 := hT v hv u hu
    simp; omega

/-- **The dynamic scheme with the schedule fixed by the condition outputs**: for every circuit numbered topologically, every
assignment of the condition variables (whatever the solver returned), every initial state: the final values are the circuit's
values, and the schedule has at most `(k + 1) |V|` executions when every vertex has at most `k` condition variables. -/
theorem condSchedule_correct (c : DCirc Bool) (hT : c.Topo) (cs : Nat → List Nat) (k : Nat)
    (hk : ∀ v, (cs v).length ≤ k) (o : Nat → Bool) (σ τ : Nat → Bool) :
    (∀ v, v < c.n → runA c σ (execs (condSchedule cs o c.n)) v = valOf c τ v) ∧
      (condSchedule cs o c.n).length ≤ (k + 1) * c.n :=
  ⟨fun v hv => final_exec_eq_val c hT (condSchedule_ordered c hT cs o) σ τ v hv, condSchedule_length cs o k hk c.n⟩

/-- Without conditions the schedule is the plain numbering order. -/
theorem condSchedule_nil (o : Nat → Bool) (n : Nat) : condSchedule (fun _ => []) o n = List.range n := by
  induction n with
  | zero => simp [condSchedule]
  | succ n ih =>
    rw [condSchedule_succ, ih, List.range_succ]
    simp [condReps]

end SmcIrred.Dyn
