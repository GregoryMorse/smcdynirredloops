module

public import SmcIrred.Spec.Dnf

public section

namespace SmcIrred

/-- Flip the value of variable `i`. -/
@[expose] def flipAt (a : Nat → Bool) (i : Nat) : Nat → Bool := fun j => if j = i then !a j else a j

theorem parity_flip : ∀ (n : Nat) (a : Nat → Bool) (i : Nat), i < n → parity n (flipAt a i) = !parity n a := by
  intro n
  induction n with
  | zero => intro a i h; omega
  | succ n ih =>
    intro a i h
    cases i with
    | zero =>
      have : (fun j => flipAt a 0 (j + 1)) = (fun j => a (j + 1)) := by
        funext j; simp [flipAt]
      simp only [parity, this]
      simp [flipAt]
    | succ i =>
      have : (fun j => flipAt a (i + 1) (j + 1)) = flipAt (fun j => a (j + 1)) i := by
        funext j; simp [flipAt]
      simp only [parity, this]
      rw [ih _ i (by omega)]
      have h0 : flipAt a (i + 1) 0 = a 0 := by simp [flipAt]
      rw [h0]
      cases a 0 <;> cases parity n (fun j => a (j + 1)) <;> rfl

/-- An assignment of a list of values to the variables `0, 1, …`. -/
@[expose] def asg : List Bool → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: L, j + 1 => asg L j

@[expose] def parL : List Bool → Bool
  | [] => false
  | b :: L => xor b (parL L)

theorem parity_asg : ∀ L : List Bool, parity L.length (asg L) = parL L := by
  intro L
  induction L with
  | nil => rfl
  | cons b L ih => simp only [List.length_cons, parity, asg, parL]; exact congrArg _ ih

/-- All lists of Booleans of length `n`. -/
@[expose] def allL : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allL n).map (false :: ·) ++ (allL n).map (true :: ·)

theorem allL_length (n : Nat) : ∀ L ∈ allL n, L.length = n := by
  induction n with
  | zero => intro L h; simp [allL] at h; subst h; rfl
  | succ n ih =>
    intro L h
    simp only [allL, List.mem_append, List.mem_map] at h
    rcases h with ⟨L', h, rfl⟩ | ⟨L', h, rfl⟩ <;> simp [ih L' h]

theorem allL_nodup (n : Nat) : (allL n).Nodup := by
  induction n with
  | zero => simp [allL]
  | succ n ih =>
    simp only [allL]
    rw [List.nodup_append]
    refine ⟨List.Pairwise.map _ (fun a b hab h => hab (List.cons.inj h).2) ih, List.Pairwise.map _ (fun a b hab h => hab (List.cons.inj h).2) ih, ?_⟩
    intro x hx y hy hxy
    simp only [List.mem_map] at hx hy
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, rfl⟩ := hy
    have := (List.cons.inj hxy).1
    simp at this

/-- The lists of length `n` with parity `b`. -/
@[expose] def parLs (n : Nat) (b : Bool) : List (List Bool) := (allL n).filter (fun L => parL L == b)

theorem parLs_succ (n : Nat) (b : Bool) :
    (parLs (n + 1) b).length = (parLs n b).length + (parLs n (!b)).length := by
  simp only [parLs, allL, List.filter_append, List.length_append, List.filter_map, List.length_map]
  have h1 : ((fun L => parL L == b) ∘ (false :: ·)) = fun L => parL L == b := by
    funext L; simp [parL]
  have h2 : ((fun L => parL L == b) ∘ (true :: ·)) = fun L => parL L == !b := by
    funext L; cases b <;> cases hp : parL L <;> simp [parL, hp]
  rw [h1, h2]

theorem parLs_count : ∀ (n : Nat) (b : Bool), (parLs (n + 1) b).length = 2 ^ n := by
  intro n
  induction n with
  | zero => intro b; cases b <;> simp [parLs, allL, parL]
  | succ n ih =>
    intro b
    rw [parLs_succ, ih, ih]; omega

/-- **C18** (parity needs exponentially many terms). Every DNF over the variables `0 … n-1` that computes the parity of
those variables has at least `2^(n-1)` terms. -/
theorem dnf_parity_terms (n : Nat) (hn : 1 ≤ n) (D : List (List Lit)) (hD : ∀ t ∈ D, ∀ l ∈ t, l.var < n)
    (hc : ∀ a : Nat → Bool, DnfSat D a ↔ parity n a = true) : 2 ^ (n - 1) ≤ D.length := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hodd : ∀ L ∈ parLs (k + 1) true, ∃ t ∈ D, TermSat t (asg L) := by
    intro L hL
    simp only [parLs, List.mem_filter, beq_iff_eq] at hL
    have hlen := allL_length _ L hL.1
    have : parity (k + 1) (asg L) = true := by
      have := parity_asg L; rw [hlen] at this; rw [this]; exact hL.2
    exact (hc _).2 this
  -- a satisfied term of an odd assignment mentions every variable
  have hall : ∀ L ∈ parLs (k + 1) true, ∀ t ∈ D, TermSat t (asg L) → ∀ i, i < k + 1 → ∃ l ∈ t, l.var = i := by
    intro L hL t ht hsat i hi
    apply Classical.byContradiction
    intro hno
    have hnm : ∀ l ∈ t, l.var ≠ i := fun l hl e => hno ⟨l, hl, e⟩
    have hsat' : TermSat t (flipAt (asg L) i) := by
      intro l hl
      have := hsat l hl
      simp [flipAt, hnm l hl, this]
    have hd : DnfSat D (flipAt (asg L) i) := ⟨t, ht, hsat'⟩
    have h1 := (hc _).1 hd
    simp only [parLs, List.mem_filter, beq_iff_eq] at hL
    have hlen := allL_length _ L hL.1
    have hp : parity (k + 1) (asg L) = true := by
      have := parity_asg L; rw [hlen] at this; rw [this]; exact hL.2
    rw [parity_flip _ _ i hi, hp] at h1
    simp at h1
  have hf : ∀ L : List Bool, ∃ t : List Lit, L ∈ parLs (k + 1) true → t ∈ D ∧ TermSat t (asg L) := by
    intro L
    by_cases hL : L ∈ parLs (k + 1) true
    · obtain ⟨t, ht, hs⟩ := hodd L hL
      exact ⟨t, fun _ => ⟨ht, hs⟩⟩
    · exact ⟨[], fun h => absurd h hL⟩
  obtain ⟨f, hf⟩ : ∃ f : List Bool → List Lit, ∀ L, L ∈ parLs (k + 1) true → f L ∈ D ∧ TermSat (f L) (asg L) :=
    ⟨fun L => Classical.choose (hf L), fun L => Classical.choose_spec (hf L)⟩
  have hinj : ∀ L1 ∈ parLs (k + 1) true, ∀ L2 ∈ parLs (k + 1) true, f L1 = f L2 → L1 = L2 := by
    intro L1 h1 L2 h2 he
    have l1 := allL_length _ L1 (List.mem_filter.1 h1).1
    have l2 := allL_length _ L2 (List.mem_filter.1 h2).1
    obtain ⟨hD1, hs1⟩ := hf L1 h1
    obtain ⟨hD2, hs2⟩ := hf L2 h2
    rw [he] at hs1 hD1
    have hs1' : TermSat (f L2) (asg L1) := hs1
    have hpt : ∀ j, j < k + 1 → asg L1 j = asg L2 j := by
      intro j hj
      obtain ⟨l, hl, hlj⟩ := hall L1 h1 _ hD1 hs1' j hj
      have e1 := hs1 l hl
      have e2 := hs2 l hl
      rw [hlj] at e1 e2
      rw [e1, e2]
    have key : ∀ (A B : List Bool), A.length = B.length → (∀ j, j < A.length → asg A j = asg B j) → A = B := by
      intro A
      induction A with
      | nil => intro B h _; cases B with | nil => rfl | cons _ _ => simp at h
      | cons x A ih =>
        intro B h hp
        cases B with
        | nil => simp at h
        | cons y B =>
          have h0 := hp 0 (by simp)
          simp only [asg] at h0
          have : A = B := ih B (by simpa using h) (fun j hj => hp (j + 1) (by simpa using hj))
          rw [h0, this]
    exact key L1 L2 (by rw [l1, l2]) (fun j hj => hpt j (by rw [l1] at hj; exact hj))
  have hnd : ((parLs (k + 1) true).map f).Nodup :=
    List.pairwise_map.2 (List.Pairwise.imp_of_mem (fun {a b} ha hb hne he => hne (hinj a ha b hb he))
      (List.Pairwise.filter _ (allL_nodup _)))
  have hsub : ∀ t ∈ (parLs (k + 1) true).map f, t ∈ D := by
    intro t ht
    obtain ⟨L, hL, rfl⟩ := List.mem_map.1 ht
    exact (hf L hL).1
  have := hnd.length_le_of_subset hsub
  rw [List.length_map, parLs_count] at this
  simpa using this

end SmcIrred
