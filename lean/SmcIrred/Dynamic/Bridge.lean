module

public import SmcIrred.Spec.DynBridge
public import SmcIrred.Dynamic.FinalExec

public section

namespace SmcIrred

open Dyn

theorem lookup_map {r : List Nat} {x : Nat → Bool} {u : Nat} (h : u ∈ r) : lookupAcc r (r.map x) u = x u := by
  induction r with
  | nil => simp at h
  | cons a t ih =>
    unfold lookupAcc at *
    by_cases ha : a = u
    · subst ha; simp
    · have hu : u ∈ t := by simpa [Ne.symm ha] using h
      have := ih hu
      simp [List.zip_cons_cons, ha, this]

theorem baseVal_congr (c : Circ) (inp : Nat → Bool) {acc acc' : Nat → Bool} (v : Nat)
    (h : ∀ u ∈ c.reads v, acc u = acc' u) : baseVal c inp acc v = baseVal c inp acc' v := by
  have hp : ∀ u ∈ c.pred v, acc u = acc' u := fun u hu => h u (by simp [Circ.reads, hu])
  have hc : cnt acc (c.pred v) = cnt acc' (c.pred v) := by
    unfold cnt
    rw [List.filter_congr (fun u hu => by rw [hp u hu])]
  unfold baseVal
  generalize hk : c.kind v = k
  cases k with
  | flow => simp [hc]
  | any => simp [hc]
  | add => simp [hc]
  | addneg => simp [hc]
  | call sid ins outs reps => rfl
  | tbl sel tab =>
    have hs : ∀ u ∈ sel, acc u = acc' u := fun u hu => h u (by simp [Circ.reads, hk, hu])
    have : ((sel.zip tab).any fun p => acc p.1 && p.2) = ((sel.zip tab).any fun p => acc' p.1 && p.2) := by
      apply Bool.eq_iff_iff.2
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨p, hp', hq⟩
        exact ⟨p, hp', by rw [← hs p.1 (List.of_mem_zip hp').1]; exact hq⟩
      · rintro ⟨p, hp', hq⟩
        exact ⟨p, hp', by rw [hs p.1 (List.of_mem_zip hp').1]; exact hq⟩
    simp only [hc, this]

/-- The evaluator's values of a call-free, topologically numbered circuit are the values of its dynamic-scheme circuit. -/
theorem valAt_eq_valOf (lib : Lib) (V : Circ → (Nat → Bool) → Nat → Nat → Bool) (c : Circ) (inp : Nat → Bool)
    (hf : c.Flat) (ht : c.TopoR) (τ : Nat → Bool) : ∀ f v, v < c.n → v < f → valAt lib V c inp f v = valOf (c.toD inp) τ v := by
  have hT : (c.toD inp).Topo := fun v hv u hu => ht v hv u hu
  have hval := valOf_isVal (c.toD inp) hT τ
  intro f
  induction f with
  | zero => intro v _ h; omega
  | succ f ih =>
    intro v hv hvf
    have hnc : ∀ u ∈ c.pred v, writtenBy lib V (valAt lib V c inp f) c u v = false := by
      intro u hu
      unfold writtenBy
      generalize hk : c.kind u = k
      cases k with
      | call sid ins outs reps =>
        exfalso
        have hun : u < c.n := by
          have := ht v hv u (by simp [Circ.reads, hu]); omega
        exact hf u hun sid ins outs reps hk
      | _ => rfl
    show (baseVal c inp (valAt lib V c inp f) v || (c.pred v).any fun u => writtenBy lib V (valAt lib V c inp f) c u v) = _
    have hany : ((c.pred v).any fun u => writtenBy lib V (valAt lib V c inp f) c u v) = false := by
      simp only [List.any_eq_false]
      intro u hu
      simp [hnc u hu]
    rw [hany, Bool.or_false]
    have := hval v hv
    rw [this]
    show baseVal c inp (valAt lib V c inp f) v = baseVal c inp (lookupAcc (c.reads v) (((c.toD inp).ps v).map (valOf (c.toD inp) τ))) v
    apply baseVal_congr
    intro u hu
    have hlt := ht v hv u hu
    have hun : u < c.n := by omega
    rw [ih u hun (by omega)]
    exact (lookup_map (r := c.reads v) hu).symm

/-- The evaluator's value of a call-free topologically numbered circuit, at every nesting depth, is the value the dynamic
scheme computes: every schedule whose final executions respect the dependencies (repetitions and faulty writes in non-final
positions allowed) leaves exactly the evaluator's values. -/
theorem dynamic_eq_evaluator (lib : Lib) (d : Nat) (c : Circ) (inp : Nat → Bool) (hf : c.Flat) (ht : c.TopoR)
    {acts : List (Act Bool)} (h : FinalOrdered (c.toD inp) acts) (σ0 τ : Nat → Bool) (v : Nat) (hv : v < c.n) :
    runA (c.toD inp) σ0 acts v = Circ.val lib d c inp v := by
  have hT : (c.toD inp).Topo := fun v hv u hu => ht v hv u hu
  rw [final_exec_eq_val (c.toD inp) hT h σ0 τ v hv]
  unfold Circ.val
  have key : ∀ (V : Circ → (Nat → Bool) → Nat → Nat → Bool), valAt lib V c inp c.n v = valOf (c.toD inp) τ v :=
    fun V => valAt_eq_valOf lib V c inp hf ht τ c.n v hv hv
  cases d with
  | zero => exact (key _).symm
  | succ d => exact (key _).symm

/-- The hypotheses are satisfiable for every such circuit: the schedule that executes each vertex once in numbering order has the
final executions in dependency order, so it computes the evaluator's values. -/
theorem range_schedule_eq_evaluator (lib : Lib) (d : Nat) (c : Circ) (inp : Nat → Bool) (hf : c.Flat) (ht : c.TopoR)
    (σ0 τ : Nat → Bool) (v : Nat) (hv : v < c.n) :
    runA (c.toD inp) σ0 (execs (List.range c.n)) v = Circ.val lib d c inp v :=
  dynamic_eq_evaluator lib d c inp hf ht (execs_ordered (c.toD inp) (fun v hv u hu => ht v hv u hu)) σ0 τ v hv

end SmcIrred
