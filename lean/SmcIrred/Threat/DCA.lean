module

public import SmcIrred.Spec.Threat
public import SmcIrred.Dynamic.Fault

public section

namespace SmcIrred.Threat

open Dyn

variable {α : Type} (c : DCirc α)

/-- T5 (the class `Fault`, restated from the dynamic scheme): a single replaced write in a non-final execution leaves the
final values unchanged (a fault in a final execution fixes the value written: `Dyn.fault_final_changes`). -/
theorem fault_class (hT : c.Topo) {a b : List Nat} {x : Nat}
    (hord : FinalOrdered c (execs (a ++ x :: b) : List (Act α))) (hx : x ∈ b) (δ : α) (σ τ : Nat → α) :
    ∀ v, v < c.n → runA c σ (execs a ++ (x, some δ) :: execs b) v = valOf c τ v :=
  fault_nonfinal c hT hord hx δ σ τ

theorem obs_addresses (σ : Nat → α) : ∀ acts : List (Act α), (obs c σ acts).map (·.1) = acts.map (·.1) := by
  intro acts
  induction acts generalizing σ with
  | nil => rfl
  | cons a t ih => simp [obs, ih]

/-- The last observation at an address is the final value of the vertex. -/
theorem obs_last (σ : Nat → α) (v : Nat) : ∀ acts : List (Act α), v ∈ acts.map (·.1) →
    ((obs c σ acts).filter (·.1 = v)).getLast? = some (v, runA c σ acts v) := by
  intro acts
  induction acts generalizing σ with
  | nil => intro h; simp at h
  | cons a t ih =>
    intro h
    by_cases hv : v ∈ t.map (·.1)
    · have := ih (stepA c σ a) hv
      by_cases ha : a.1 = v
      · simp only [obs, List.filter_cons, ha, decide_true, ite_true, List.getLast?_cons]
        rw [this]; rfl
      · simp only [obs, List.filter_cons, ha, decide_false, Bool.false_eq_true, ite_false]
        rw [this]; rfl
    · have ha : a.1 = v := by
        simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact h.symm
        · exact absurd h hv
      have hnot : ∀ x ∈ t, x.1 ≠ v := by
        intro x hx hxv; exact hv (List.mem_map.2 ⟨x, hx, hxv⟩)
      have hf : ((obs c (stepA c σ a) t).filter (·.1 = v)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        have : y.1 ∈ (obs c (stepA c σ a) t).map (·.1) := List.mem_map.2 ⟨y, hy, rfl⟩
        rw [obs_addresses] at this
        obtain ⟨x, hx, hxy⟩ := List.mem_map.1 this
        simp only [decide_eq_true_eq]
        rw [← hxy]; exact hnot x hx
      simp only [obs, List.filter_cons, ha, decide_true, ite_true, hf, List.getLast?_cons]
      show some (([] : List (Nat × α)).getLast?.getD (v, stepA c σ a v)) = some (v, runA c (stepA c σ a) t v)
      rw [runA_not_mem c _ v t hnot]
      rfl

theorem mem_of_final {acts : List (Act α)} (h : FinalOrdered c acts) {v : Nat} (hv : v < c.n) :
    v ∈ acts.map (·.1) := by
  obtain ⟨pre, post, rfl, _⟩ := h v hv
  simp

/-- T6 (the class `Dca`, address-aligned traces). For every dependency-respecting schedule, the last observation at the address
of vertex `v` is `(v, value of v in the circuit)`: whatever the order and the repetitions, the (address, final value) pairs a
trace gives are those of the static scheme. -/
theorem dca_last (hT : c.Topo) {acts : List (Act α)} (h : FinalOrdered c acts) (σ τ : Nat → α) {v : Nat} (hv : v < c.n) :
    ((obs c σ acts).filter (·.1 = v)).getLast? = some (v, valOf c τ v) := by
  rw [obs_last c σ v acts (mem_of_final c h hv), final_exec_eq_val c hT h σ τ v hv]

theorem dca_final_obs (hT : c.Topo) {a b : List (Act α)} (ha : FinalOrdered c a) (hb : FinalOrdered c b) (σ σ' : Nat → α) :
    finalObs c σ a = finalObs c σ' b := by
  unfold finalObs
  apply List.map_congr_left
  intro v hv
  have hv' : v < c.n := List.mem_range.1 hv
  rw [final_exec_eq_val c hT ha σ σ v hv', final_exec_eq_val c hT hb σ' σ v hv']

/-- The repeats are visible: the address sequence of the trace is the schedule's, so a vertex executed twice appears twice. -/
theorem dca_repeats_visible (σ : Nat → α) (acts : List (Act α)) (v : Nat) :
    ((obs c σ acts).map (·.1)).count v = (acts.map (·.1)).count v := by
  rw [obs_addresses]

/-- Witness: two dependency-respecting schedules with the same (vertex, final value) pairs and different address traces (the
repeated vertex is visible). -/
theorem dca_witness :
    finalObs wcirc (fun _ => false) (execs [0, 1] : List (Act Bool)) = finalObs wcirc (fun _ => false) (execs [0, 1, 1]) ∧
    (obs wcirc (fun _ => false) (execs [0, 1] : List (Act Bool))).map (·.1) ≠
      (obs wcirc (fun _ => false) (execs [0, 1, 1] : List (Act Bool))).map (·.1) := by decide

end SmcIrred.Threat
