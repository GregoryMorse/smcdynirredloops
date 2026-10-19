module

public import SmcIrred.Dynamic.Bridge

public section

namespace SmcIrred

open Dyn

theorem writtenBy_local (lib : Lib) (V : Circ → (Nat → Bool) → Nat → Nat → Bool) (c : Circ) {acc acc' : Nat → Bool}
    (u v : Nat) (hp : ∀ w ∈ c.pred u, acc w = acc' w)
    (hi : ∀ sid ins outs reps, c.kind u = .call sid ins outs reps → ∀ w ∈ ins, acc w = acc' w) :
    writtenBy lib V acc c u v = writtenBy lib V acc' c u v := by
  unfold writtenBy
  generalize hk : c.kind u = k
  cases k with
  | call sid ins outs reps =>
    have hc : cnt acc (c.pred u) = cnt acc' (c.pred u) := by
      unfold cnt
      rw [List.filter_congr (fun w hw => by rw [hp w hw])]
    have key : ∀ x, (((lib sid).ins.zip ins).any fun p => p.1 == x && acc p.2) =
        (((lib sid).ins.zip ins).any fun p => p.1 == x && acc' p.2) := by
      intro x
      apply Bool.eq_iff_iff.2
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨p, hp', hq⟩
        exact ⟨p, hp', by rw [← hi sid ins outs reps hk p.2 (List.of_mem_zip hp').2]; exact hq⟩
      · rintro ⟨p, hp', hq⟩
        exact ⟨p, hp', by rw [hi sid ins outs reps hk p.2 (List.of_mem_zip hp').2]; exact hq⟩
    simp only [hc, callOf, key]
  | _ => rfl

theorem reads2_mem_reads {c : Circ} {v u : Nat} (h : u ∈ c.reads v) : u ∈ c.reads2 v := by
  simp [Circ.reads2, h]

theorem reads2_call {c : Circ} {v u : Nat} (hu : u ∈ c.pred v) {sid : Nat} {ins outs : List Nat} {reps : Nat}
    (hk : c.kind u = .call sid ins outs reps) : ∀ w, (w ∈ c.pred u ∨ w ∈ ins) → w ∈ c.reads2 v := by
  intro w hw
  simp only [Circ.reads2, Circ.callReads, List.mem_append, List.mem_flatMap]
  right
  exact ⟨u, hu, by rw [hk]; simpa using hw⟩

/-- The evaluator's values of any circuit whose reads (with the calls' reads) are smaller than the vertex are the values of
its dynamic-scheme circuit. -/
theorem valAt_eq_valOf2 (lib : Lib) (V : Circ → (Nat → Bool) → Nat → Nat → Bool) (c : Circ) (inp : Nat → Bool)
    (ht : c.TopoR2) (τ : Nat → Bool) :
    ∀ f v, v < c.n → v < f → valAt lib V c inp f v = valOf (c.toDV lib V inp) τ v := by
  have hT : (c.toDV lib V inp).Topo := fun v hv u hu => ht v hv u hu
  have hval := valOf_isVal (c.toDV lib V inp) hT τ
  intro f
  induction f with
  | zero => intro v _ h; omega
  | succ f ih =>
    intro v hv hvf
    have hag : ∀ u ∈ c.reads2 v, valAt lib V c inp f u = valOf (c.toDV lib V inp) τ u := by
      intro u hu
      have hlt := ht v hv u hu
      exact ih u (by omega) (by omega)
    have hlk : ∀ u ∈ c.reads2 v, lookupAcc (c.reads2 v) ((c.reads2 v).map (valOf (c.toDV lib V inp) τ)) u =
        valOf (c.toDV lib V inp) τ u := fun u hu => lookup_map hu
    have hacc : ∀ u ∈ c.reads2 v, valAt lib V c inp f u =
        lookupAcc (c.reads2 v) ((c.reads2 v).map (valOf (c.toDV lib V inp) τ)) u := by
      intro u hu; rw [hlk u hu]; exact hag u hu
    show (baseVal c inp (valAt lib V c inp f) v || (c.pred v).any fun u => writtenBy lib V (valAt lib V c inp f) c u v) = _
    rw [hval v hv]
    show _ = (baseVal c inp (lookupAcc (c.reads2 v) (((c.reads2 v)).map (valOf (c.toDV lib V inp) τ))) v ||
      (c.pred v).any fun u => writtenBy lib V (lookupAcc (c.reads2 v) ((c.reads2 v).map (valOf (c.toDV lib V inp) τ))) c u v)
    have h1 : baseVal c inp (valAt lib V c inp f) v =
        baseVal c inp (lookupAcc (c.reads2 v) ((c.reads2 v).map (valOf (c.toDV lib V inp) τ))) v :=
      baseVal_congr c inp v (fun u hu => hacc u (reads2_mem_reads hu))
    have h2 : ((c.pred v).any fun u => writtenBy lib V (valAt lib V c inp f) c u v) =
        ((c.pred v).any fun u => writtenBy lib V
          (lookupAcc (c.reads2 v) ((c.reads2 v).map (valOf (c.toDV lib V inp) τ))) c u v) := by
      apply Bool.eq_iff_iff.2
      simp only [List.any_eq_true]
      have hw : ∀ u ∈ c.pred v, writtenBy lib V (valAt lib V c inp f) c u v =
          writtenBy lib V (lookupAcc (c.reads2 v) ((c.reads2 v).map (valOf (c.toDV lib V inp) τ))) c u v := by
        intro u hu
        cases hk : c.kind u with
        | call sid ins outs reps =>
          apply writtenBy_local
          · intro w hw
            exact hacc w (reads2_call hu hk w (Or.inl hw))
          · intro sid' ins' outs' reps' hk' w hw
            rw [hk] at hk'
            injection hk' with e1 e2 e3 e4
            subst e2
            exact hacc w (reads2_call hu hk w (Or.inr hw))
        | _ => unfold writtenBy; rw [hk]
      constructor
      · rintro ⟨u, hu, hq⟩; exact ⟨u, hu, by rw [← hw u hu]; exact hq⟩
      · rintro ⟨u, hu, hq⟩; exact ⟨u, hu, by rw [hw u hu]; exact hq⟩
    rw [h1, h2]

/-- **The bridge for circuits with calls**: every schedule of the dynamic scheme whose final executions respect the
dependencies (repetitions and faulty writes before the last executions allowed) leaves exactly the evaluator's values,
for circuits with reusable-subgraph calls (the subgraphs are evaluated by the evaluator one nesting level lower). -/
theorem dynamic_eq_evaluator_calls (lib : Lib) (d : Nat) (c : Circ) (inp : Nat → Bool) (ht : c.TopoR2)
    {acts : List (Act Bool)} (h : FinalOrdered (c.toDV lib (level lib d).val inp) acts) (σ0 τ : Nat → Bool) (v : Nat)
    (hv : v < c.n) :
    runA (c.toDV lib (level lib d).val inp) σ0 acts v = Circ.val lib (d + 1) c inp v := by
  have hT : (c.toDV lib (level lib d).val inp).Topo := fun v hv u hu => ht v hv u hu
  rw [final_exec_eq_val _ hT h σ0 τ v hv]
  exact (valAt_eq_valOf2 lib (level lib d).val c inp ht τ c.n v hv hv).symm

/-- The hypotheses are satisfiable: executing every vertex once in numbering order is such a schedule. -/
theorem range_schedule_eq_evaluator_calls (lib : Lib) (d : Nat) (c : Circ) (inp : Nat → Bool) (ht : c.TopoR2)
    (σ0 τ : Nat → Bool) (v : Nat) (hv : v < c.n) :
    runA (c.toDV lib (level lib d).val inp) σ0 (execs (List.range c.n)) v = Circ.val lib (d + 1) c inp v :=
  dynamic_eq_evaluator_calls lib d c inp ht
    (execs_ordered (c.toDV lib (level lib d).val inp) (fun v hv u hu => ht v hv u hu)) σ0 τ v hv

end SmcIrred
