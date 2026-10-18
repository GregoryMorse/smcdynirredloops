module

public import SmcIrred.Spec.Dynamic

public section

namespace SmcIrred.Dyn

variable {α : Type} (c : DCirc α)

theorem runA_append (σ : Nat → α) (a b : List (Act α)) : runA c σ (a ++ b) = runA c (runA c σ a) b := by
  simp [runA, List.foldl_append]

theorem runA_not_mem (σ : Nat → α) (w : Nat) : ∀ acts : List (Act α), (∀ a ∈ acts, a.1 ≠ w) → runA c σ acts w = σ w := by
  intro acts
  induction acts generalizing σ with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    have h1 : a.1 ≠ w := h a (by simp)
    have h2 : ∀ b ∈ t, b.1 ≠ w := fun b hb => h b (by simp [hb])
    show runA c (stepA c σ a) t w = σ w
    rw [ih (stepA c σ a) h2]
    obtain ⟨v, o⟩ := a
    cases o <;> simp [stepA, Ne.symm h1]

/-- C77: when the final executions are in dependency order, the final values satisfy the equations of the circuit, from any
initial values and for every schedule (also one chosen by the input). Faulty actions are allowed in the list. -/
theorem final_isVal (hT : c.Topo) {acts : List (Act α)} (h : FinalOrdered c acts) (σ : Nat → α) :
    IsVal c (runA c σ acts) := by
  intro v hv
  obtain ⟨pre, post, hs, hv1, hv2⟩ := h v hv
  have e : runA c σ acts = runA c (stepA c (runA c σ pre) (v, none)) post := by
    rw [hs, runA_append]; rfl
  have hx : ∀ u, (∀ a ∈ post, a.1 ≠ u) → u ≠ v → runA c σ acts u = runA c σ pre u := by
    intro u hu huv
    rw [e, runA_not_mem c _ u post hu]
    simp [stepA, huv]
  have hmap : (c.ps v).map (runA c σ acts) = (c.ps v).map (runA c σ pre) := by
    apply List.map_congr_left
    intro u hu
    have huv : u ≠ v := by have := hT v hv u hu; omega
    exact hx u (hv2 u hu) huv
  rw [hmap, e, runA_not_mem c _ v post hv1]
  simp [stepA]

/-- The equations of a topologically numbered circuit have exactly one solution. -/
theorem isVal_unique (hT : c.Topo) {x y : Nat → α} (hx : IsVal c x) (hy : IsVal c y) :
    ∀ v, v < c.n → x v = y v := by
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih =>
    intro hv
    rw [hx v hv, hy v hv]
    congr 1
    apply List.map_congr_left
    intro u hu
    have hu' := hT v hv u hu
    exact ih u hu' (by omega)

theorem range_split : ∀ (n v : Nat), v < n →
    ∃ post, List.range n = List.range v ++ v :: post ∧ ∀ x ∈ post, v < x := by
  intro n
  induction n with
  | zero => intro v hv; omega
  | succ n ih =>
    intro v hv
    by_cases h : v = n
    · subst h
      exact ⟨[], by simp [List.range_succ], by simp⟩
    · obtain ⟨post, hp, hx⟩ := ih v (by omega)
      refine ⟨post ++ [n], ?_, ?_⟩
      · rw [List.range_succ, hp]; simp
      · intro x hx'
        rcases List.mem_append.1 hx' with h1 | h1
        · exact hx x h1
        · simp at h1; omega

theorem execs_ordered (hT : c.Topo) : FinalOrdered c (execs (List.range c.n) : List (Act α)) := by
  intro v hv
  obtain ⟨post, hp, hx⟩ := range_split c.n v hv
  refine ⟨execs (List.range v), execs post, ?_, ?_, ?_⟩
  · rw [execs, hp]; simp [execs]
  · intro a ha
    simp only [execs, List.mem_map] at ha
    obtain ⟨x, hxm, rfl⟩ := ha
    have := hx x hxm
    simp; omega
  · intro u hu a ha
    simp only [execs, List.mem_map] at ha
    obtain ⟨x, hxm, rfl⟩ := ha
    have h1 := hx x hxm
    have h2 := hT v hv u hu
    simp; omega

/-- The values of the circuit satisfy its equations. -/
theorem valOf_isVal (hT : c.Topo) (σ : Nat → α) : IsVal c (valOf c σ) := final_isVal c hT (execs_ordered c hT) σ

/-- C77: for every schedule whose final executions are in dependency order (every vertex executed at least once, each
vertex's last execution after the last executions of its predecessors), the final values are the values of the circuit,
whatever the initial values and the repetitions in between. -/
theorem final_exec_eq_val (hT : c.Topo) {acts : List (Act α)} (h : FinalOrdered c acts) (σ τ : Nat → α) :
    ∀ v, v < c.n → runA c σ acts v = valOf c τ v :=
  isVal_unique c hT (final_isVal c hT h σ) (valOf_isVal c hT τ)

/-- The same for a schedule chosen by the input: for a family of circuits (the input fixes the input vertices) and a
schedule depending on the input. -/
theorem final_exec_input_tied {ι : Type} (cir : ι → DCirc α) (hT : ∀ i, (cir i).Topo) (sched : ι → List Nat)
    (hs : ∀ i, FinalOrdered (cir i) (execs (sched i) : List (Act α))) (i : ι) (σ τ : Nat → α) :
    ∀ v, v < (cir i).n → runA (cir i) σ (execs (sched i)) v = valOf (cir i) τ v :=
  final_exec_eq_val (cir i) (hT i) (hs i) σ τ

/-- Bounded duplication: if every vertex is executed at most `k` times the schedule has at most `k · |V|` executions. -/
theorem schedule_length_le (k : Nat) : ∀ (m : Nat) (s : List Nat), (∀ x ∈ s, x < m) → (∀ v, v < m → s.count v ≤ k) →
    s.length ≤ k * m := by
  intro m
  induction m with
  | zero => intro s hs _; cases s with | nil => simp | cons a t => exact absurd (hs a (by simp)) (by omega)
  | succ m ih =>
    intro s hs hc
    have h1 := List.length_eq_countP_add_countP (fun x => x == m) (l := s)
    rw [List.countP_eq_length_filter, List.countP_eq_length_filter, ← List.count_eq_length_filter] at h1
    have h2 : (s.filter (fun a => decide ¬(a == m) = true)).length ≤ k * m := by
      apply ih
      · intro x hx
        simp only [List.mem_filter, beq_iff_eq, decide_eq_true_eq] at hx
        have := hs x hx.1
        omega
      · intro v hv
        have e := List.count_filter (p := fun a => decide ¬(a == m) = true) (a := v) (l := s)
          (by simp; omega)
        rw [e]
        exact hc v (by omega)
    have h3 := hc m (by omega)
    rw [Nat.mul_succ]
    omega

end SmcIrred.Dyn
