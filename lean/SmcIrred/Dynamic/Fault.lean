module

public import SmcIrred.Dynamic.FinalExec

public section

namespace SmcIrred.Dyn

variable {α : Type} (c : DCirc α)

/-- A fault in a non-final execution does not break the order of the final executions: if the executed vertex `x` is executed
again later (`x ∈ b`), replacing this execution by the arbitrary write `δ` leaves the schedule final-ordered. -/
theorem fault_nonfinal_ordered {a b : List Nat} {x : Nat} (hord : FinalOrdered c (execs (a ++ x :: b) : List (Act α)))
    (hx : x ∈ b) (δ : α) : FinalOrdered c ((execs a ++ (x, some δ) :: execs b : List (Act α))) := by
  intro v hv
  obtain ⟨pre, post, hs, hv1, hv2⟩ := hord v hv
  have hxB : ((x, none) : Act α) ∈ (execs b : List (Act α)) := by
    simp only [execs, List.mem_map]; exact ⟨x, hx, rfl⟩
  have hs' : (execs a : List (Act α)) ++ (x, none) :: execs b = pre ++ (v, none) :: post := by
    simpa [execs] using hs
  rcases List.append_eq_append_iff.1 hs' with ⟨a', hpre, h⟩ | ⟨c', ha, h⟩
  · cases a' with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq, and_true] at h
      obtain ⟨hxv, hB⟩ := h
      exact (hv1 _ (hB ▸ hxB) hxv).elim
    | cons y a'' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨hy, hB⟩ := h
      refine ⟨execs a ++ (x, some δ) :: a'', post, ?_, hv1, hv2⟩
      rw [hB]; simp
  · cases c' with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq, and_true] at h
      obtain ⟨hvx, hp⟩ := h
      exact (hv1 _ (hp ▸ hxB) hvx.symm).elim
    | cons y c'' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨hy, hp⟩ := h
      refine ⟨pre, c'' ++ (x, some δ) :: execs b, ?_, ?_, ?_⟩
      · rw [ha, ← hy]; simp
      · intro e he
        have hmem : e.1 ∈ post.map Prod.fst := by
          rw [hp]
          simp only [List.mem_append, List.mem_cons] at he
          simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
          rcases he with he | he | he
          · exact Or.inl (List.mem_map.2 ⟨e, he, rfl⟩)
          · subst he; exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (List.mem_map.2 ⟨e, he, rfl⟩))
        obtain ⟨e', he', hee⟩ := List.mem_map.1 hmem
        rw [← hee]; exact hv1 e' he'
      · intro u hu e he
        have hmem : e.1 ∈ post.map Prod.fst := by
          rw [hp]
          simp only [List.mem_append, List.mem_cons] at he
          simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
          rcases he with he | he | he
          · exact Or.inl (List.mem_map.2 ⟨e, he, rfl⟩)
          · subst he; exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (List.mem_map.2 ⟨e, he, rfl⟩))
        obtain ⟨e', he', hee⟩ := List.mem_map.1 hmem
        rw [← hee]; exact hv2 u hu e' he'

/-- T5, first half: a single fault in a non-final execution of a vertex does not change the output (the final values still
are the values of the circuit), for every initial state. -/
theorem fault_nonfinal (hT : c.Topo) {a b : List Nat} {x : Nat}
    (hord : FinalOrdered c (execs (a ++ x :: b) : List (Act α))) (hx : x ∈ b) (δ : α) (σ τ : Nat → α) :
    ∀ v, v < c.n → runA c σ (execs a ++ (x, some δ) :: execs b) v = valOf c τ v :=
  final_exec_eq_val c hT (fault_nonfinal_ordered c hord hx δ) σ τ

/-- T5, second half: a fault in the final execution of `x` sets the final value of `x` to the arbitrary value. -/
theorem fault_final_overwrites {a b : List Nat} {x : Nat} (hx : x ∉ b) (δ : α) (σ : Nat → α) :
    runA c σ (execs a ++ (x, some δ) :: execs b) x = δ := by
  rw [runA_append]
  show runA c (stepA c (runA c σ (execs a)) (x, some δ)) (execs b) x = δ
  rw [runA_not_mem c _ x (execs b) (by
    intro e he
    simp only [execs, List.mem_map] at he
    obtain ⟨y, hy, rfl⟩ := he
    intro hyx; exact hx (hyx ▸ hy))]
  simp [stepA]

/-- A faulty final execution of an output vertex changes the output whenever the written value differs from the circuit's. -/
theorem fault_final_changes {a b : List Nat} {x : Nat} (hx : x ∉ b) (δ : α) (σ τ : Nat → α)
    (hne : δ ≠ valOf c τ x) : runA c σ (execs a ++ (x, some δ) :: execs b) x ≠ valOf c τ x := by
  rw [fault_final_overwrites c hx δ σ]; exact hne

/-! ### Witnesses -/

/-- Two vertices: the input `0` (value true) and `1 = not 0`. -/
@[expose] def wcirc : DCirc Bool where
  n := 2
  ps v := if v = 1 then [0] else []
  f v l := if v = 1 then !(l.getD 0 true) else true

theorem wcirc_topo : wcirc.Topo := by
  intro v hv u hu
  change v < 2 at hv
  have : v = 0 ∨ v = 1 := by omega
  rcases this with rfl | rfl
  · simp [wcirc] at hu
  · simp [wcirc] at hu; omega

/-- Necessity of the order: executing `1` last-but-one and `0` last gives a wrong value of `1`. -/
theorem wcirc_bad_order : runA wcirc (fun _ => false) (execs [1, 0]) 1 ≠ valOf wcirc (fun _ => false) 1 := by decide

theorem wcirc_bad_not_ordered : ¬ FinalOrdered wcirc (execs [1, 0] : List (Act Bool)) := by
  intro h
  have := final_exec_eq_val wcirc wcirc_topo h (fun _ => false) (fun _ => false) 1 (by decide)
  exact wcirc_bad_order this

theorem wcirc_ordered_01 : FinalOrdered wcirc (execs [0, 1] : List (Act Bool)) := by
  intro v hv
  change v < 2 at hv
  have : v = 0 ∨ v = 1 := by omega
  rcases this with rfl | rfl
  · exact ⟨[], [(1, none)], rfl, by simp, by simp [wcirc]⟩
  · exact ⟨[(0, none)], [], rfl, by simp, by simp [wcirc]⟩

theorem wcirc_ordered_011 : FinalOrdered wcirc (execs [0, 1, 1] : List (Act Bool)) := by
  intro v hv
  change v < 2 at hv
  have : v = 0 ∨ v = 1 := by omega
  rcases this with rfl | rfl
  · exact ⟨[], [(1, none), (1, none)], rfl, by simp, by simp [wcirc]⟩
  · exact ⟨[(0, none), (1, none)], [], rfl, by simp, by simp [wcirc]⟩

/-- The position of the final execution of vertex `1` depends on the schedule (so on the input when the schedule is tied to
it): the same fault position hits a final execution in one schedule and a non-final one in the other. -/
theorem final_index_depends : lastIdx [0, 1] 1 = some 1 ∧ lastIdx [0, 1, 1] 1 = some 2 := by decide

/-- Same fault position, input-dependent effect: in the schedule `[0, 1]` the fault at position 1 is in the final execution
of the output `1` and corrupts it; in `[0, 1, 1]` it is not final and the output is unaffected. -/
theorem fault_input_dependent :
    runA wcirc (fun _ => false) (execs [0] ++ (1, some true) :: execs []) 1 ≠ valOf wcirc (fun _ => false) 1 ∧
    runA wcirc (fun _ => false) (execs [0] ++ (1, some true) :: execs [1]) 1 = valOf wcirc (fun _ => false) 1 := by decide

end SmcIrred.Dyn
