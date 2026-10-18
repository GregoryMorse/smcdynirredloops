module

public import SmcIrred.Prims.Cost

public section

namespace SmcIrred

theorem sum_const_map {α : Type} (l : List α) (k : Nat) : (l.map fun _ => k).sum = l.length * k := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; rw [Nat.add_mul]; omega

/-- A list of `andV [w, g]` over distinct non-constant wires `w ≠ g` creates one node and two edges each. -/
theorem mapG_and_fresh (g : Wire) (hg : g.isc = false) (num : List Wire) (gb : GB)
    (hnum : ∀ w ∈ num, w.isc = false ∧ w ≠ g) :
    (mapG (fun x w => andV x [w, g]) gb num).2.n = gb.n + num.length ∧
    (mapG (fun x w => andV x [w, g]) gb num).2.e = gb.e + 2 * num.length ∧
    (mapG (fun x w => andV x [w, g]) gb num).1 = (List.range num.length).map fun t => Wire.nd (gb.n + t) := by
  have hf : ∀ (x : GB) (w : Wire), (w.isc = false ∧ w ≠ g) →
      (andV x [w, g]).2.n = x.n + 1 ∧ (andV x [w, g]).1 = Wire.nd x.n := fun x w hw => by
    obtain ⟨a, _, c⟩ := andV_two x hw.1 hg hw.2
    exact ⟨a, c⟩
  obtain ⟨h1, h2⟩ := mapG_fresh (fun x w => andV x [w, g]) (fun w => w.isc = false ∧ w ≠ g) hf num gb hnum
  have h3 := mapG_cost (fun x w => andV x [w, g]) (fun _ => 1) (fun _ => 2) (fun w => w.isc = false ∧ w ≠ g)
    (fun _ => True) (fun _ _ _ _ => trivial)
    (fun x w hw _ => by
      obtain ⟨a, b, _⟩ := andV_two x hw.1 hg hw.2
      exact ⟨a, b⟩) num gb hnum trivial
  refine ⟨h1, ?_, h2⟩
  rw [h3.2, sum_const_map]
  omega

/-- The cost of one doubling step of the shift decoder. -/
theorem decStep_cost (gb : GB) (num : List Wire) (j : Nat)
    (hn : ∀ w ∈ num, w.isc = false ∧ w ≠ .nd j ∧ w.ok gb.n) :
    (decStep gb num (.nd j)).2.n = gb.n + 1 + 2 * num.length ∧
    (decStep gb num (.nd j)).2.e = gb.e + 1 + 4 * num.length ∧
    (decStep gb num (.nd j)).1 =
      ((List.range num.length).map fun t => Wire.nd (gb.n + 1 + t)) ++
      ((List.range num.length).map fun t => Wire.nd (gb.n + 1 + num.length + t)) := by
  unfold decStep
  dsimp only
  have h0 := notV_nd gb j
  generalize notV gb (.nd j) = r0 at h0 ⊢
  obtain ⟨n0, e0, f0⟩ := h0
  have hne1 : ∀ w ∈ num, w.isc = false ∧ w ≠ r0.1 := by
    intro w hw
    refine ⟨(hn w hw).1, ?_⟩
    rw [f0]
    intro e
    have := (hn w hw).2.2
    rw [e] at this
    simp [Wire.ok] at this
  obtain ⟨a1, b1, c1⟩ := mapG_and_fresh r0.1 (by rw [f0]; rfl) num r0.2 hne1
  generalize hm1 : mapG (fun x w => andV x [w, r0.1]) r0.2 num = r1 at a1 b1 c1
  obtain ⟨a2, b2, c2⟩ := mapG_and_fresh (.nd j) rfl num r1.2 (fun w hw => ⟨(hn w hw).1, (hn w hw).2.1⟩)
  generalize hm2 : mapG (fun x w => andV x [w, .nd j]) r1.2 num = r2 at a2 b2 c2
  refine ⟨?_, ?_, ?_⟩
  · show r2.2.n = _
    rw [a2, a1, n0]; omega
  · show r2.2.e = _
    rw [b2, b1, e0]; omega
  · show r1.1 ++ r2.1 = _
    rw [c1, c2, n0, a1, n0]

theorem decLoop_cost : ∀ (rest : List Wire) (gb : GB) (num : List Wire),
    (∀ w ∈ num, w.isc = false ∧ w.ok gb.n ∧ w ∉ rest) → (∀ s ∈ rest, ∃ j, s = .nd j ∧ j < gb.n) → rest.Nodup →
    (decLoop gb num rest).2.n + 2 * num.length = gb.n + (rest.length + 2 * (num.length * 2 ^ rest.length)) ∧
    (decLoop gb num rest).2.e + 4 * num.length = gb.e + (rest.length + 4 * (num.length * 2 ^ rest.length)) := by
  intro rest
  induction rest with
  | nil =>
    intro gb num _ _ _
    simp [decLoop]
  | cons s rest ih =>
    intro gb num hnum hs hnd
    obtain ⟨j, hsj, hjn⟩ := hs s List.mem_cons_self
    subst hsj
    have hn' : ∀ w ∈ num, w.isc = false ∧ w ≠ .nd j ∧ w.ok gb.n := by
      intro w hw
      obtain ⟨a, b, c⟩ := hnum w hw
      exact ⟨a, fun e => c (by rw [e]; exact List.mem_cons_self), b⟩
    obtain ⟨n1, e1, o1⟩ := decStep_cost gb num j hn'
    have hlen : (decStep gb num (.nd j)).1.length = 2 * num.length := by
      rw [o1]; simp; omega
    have hdl : decLoop gb num (Wire.nd j :: rest) = decLoop (decStep gb num (.nd j)).2 (decStep gb num (.nd j)).1 rest := rfl
    rw [hdl]
    have hrest_nd : ∀ s' ∈ rest, ∃ j', s' = .nd j' ∧ j' < gb.n := fun s' hs' => hs s' (List.mem_cons_of_mem _ hs')
    have hfresh : ∀ w ∈ (decStep gb num (.nd j)).1, ∃ t, w = Wire.nd t ∧ gb.n + 1 ≤ t ∧ t < gb.n + 1 + 2 * num.length := by
      intro w hw
      rw [o1] at hw
      rcases List.mem_append.1 hw with h | h
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
        have := List.mem_range.1 ht
        exact ⟨_, rfl, by omega, by omega⟩
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
        have := List.mem_range.1 ht
        exact ⟨_, rfl, by omega, by omega⟩
    obtain ⟨ih1, ih2⟩ := ih (decStep gb num (.nd j)).2 (decStep gb num (.nd j)).1
      (by
        intro w hw
        obtain ⟨t, rfl, ht1, ht2⟩ := hfresh w hw
        refine ⟨by simp [Wire.isc], by rw [n1]; exact ht2, ?_⟩
        intro hm
        obtain ⟨j', h1, h2⟩ := hrest_nd _ hm
        have : t = j' := by simpa using h1
        omega)
      (by
        intro s' hs'
        obtain ⟨j', h1, h2⟩ := hrest_nd s' hs'
        exact ⟨j', h1, by rw [n1]; omega⟩)
      (List.nodup_cons.1 hnd).2
    rw [hlen] at ih1 ih2
    have hX : ∀ r : Nat, 2 * num.length * 2 ^ r = 2 * (num.length * 2 ^ r) := fun r => Nat.mul_assoc _ _ _
    have hY : num.length * 2 ^ (rest.length + 1) = 2 * (num.length * 2 ^ rest.length) := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (num.length * 2 ^ rest.length) 2]
    rw [hX] at ih1 ih2
    simp only [List.length_cons]
    rw [hY]
    constructor
    · omega
    · omega

theorem decStep_first (gb : GB) (j : Nat) :
    decStep gb [.cst true] (.nd j) = ([.nd gb.n, .nd j], (gb.add .addneg [j]).2) := by
  have h1 : (notV gb (.nd j)).1 = Wire.nd gb.n := rfl
  have h2 : (notV gb (.nd j)).2 = (gb.add .addneg [j]).2 := rfl
  have a1 : andV (gb.add .addneg [j]).2 [.cst true, .nd gb.n] = (.nd gb.n, (gb.add .addneg [j]).2) :=
    andV_true_left _ rfl
  have a2 : andV (gb.add .addneg [j]).2 [.cst true, .nd j] = (.nd j, (gb.add .addneg [j]).2) :=
    andV_true_left _ rfl
  unfold decStep
  dsimp only
  rw [h1, h2]
  simp [mapG, a1, a2]

theorem decoderShift_cost (gb : GB) (shift : List Wire) (hs : ∀ s ∈ shift, ∃ j, s = .nd j ∧ j < gb.n)
    (hnd : shift.Nodup) (hm : 1 ≤ shift.length) :
    (decoderShift gb shift).2.n + 4 = gb.n + (2 ^ (shift.length + 1) + shift.length) ∧
    (decoderShift gb shift).2.e + 8 = gb.e + (2 ^ (shift.length + 2) + shift.length) := by
  rcases shift with _ | ⟨s, rest⟩
  · simp at hm
  · obtain ⟨j, hsj, hjn⟩ := hs s List.mem_cons_self
    subst hsj
    have hdl : decoderShift gb (Wire.nd j :: rest) =
        decLoop (decStep gb [.cst true] (.nd j)).2 (decStep gb [.cst true] (.nd j)).1 rest := rfl
    rw [hdl, decStep_first]
    have hn1 : (gb.add .addneg [j]).2.n = gb.n + 1 := add_n _ _ _
    have he1 : (gb.add .addneg [j]).2.e = gb.e + 1 := by rw [add_e]; rfl
    have hrest : ∀ s' ∈ rest, ∃ j', s' = Wire.nd j' ∧ j' < gb.n := fun s' hs' => hs s' (List.mem_cons_of_mem _ hs')
    obtain ⟨c1, c2⟩ := decLoop_cost rest (gb.add .addneg [j]).2 [.nd gb.n, .nd j]
      (by
        intro w hw
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with h | h
        · subst h
          refine ⟨rfl, by rw [hn1]; simp [Wire.ok], ?_⟩
          intro hm'
          obtain ⟨j', h1, h2⟩ := hrest _ hm'
          have : gb.n = j' := by simpa using h1
          omega
        · subst h
          refine ⟨rfl, by rw [hn1]; simp [Wire.ok]; omega, ?_⟩
          exact (List.nodup_cons.1 hnd).1)
      (by
        intro s' hs'
        obtain ⟨j', h1, h2⟩ := hrest s' hs'
        exact ⟨j', h1, by rw [hn1]; omega⟩)
      (List.nodup_cons.1 hnd).2
    simp only [List.length_cons, List.length_nil, hn1, he1] at c1 c2 ⊢
    have hp : 2 ^ (rest.length + 1) = 2 * 2 ^ rest.length := by rw [Nat.pow_succ, Nat.mul_comm]
    have hq : 2 ^ (rest.length + 1 + 1) = 4 * 2 ^ rest.length := by
      rw [Nat.pow_add, Nat.pow_add]; simp; omega
    have hq2 : 2 ^ (rest.length + 1 + 2) = 8 * 2 ^ rest.length := by
      rw [Nat.pow_add, Nat.pow_add]; simp; omega
    constructor
    · omega
    · omega

/-- The bitwise XOR of the constant bits of `i` with the shift wires: nodes are created only where the constant bit is `1`. -/
theorem xorPairs_spec : ∀ (bs : List Bool) (ss : List Wire) (gb : GB), bs.length = ss.length →
    (∀ s ∈ ss, ∃ j, s = .nd j ∧ j < gb.n) → ss.Nodup →
    (mapG (fun g p => xorV g [p.1, p.2]) gb ((bs.map Wire.cst).zip ss)).2.n = gb.n + bs.count true ∧
    (mapG (fun g p => xorV g [p.1, p.2]) gb ((bs.map Wire.cst).zip ss)).2.e = gb.e + bs.count true ∧
    (mapG (fun g p => xorV g [p.1, p.2]) gb ((bs.map Wire.cst).zip ss)).1.length = ss.length ∧
    (mapG (fun g p => xorV g [p.1, p.2]) gb ((bs.map Wire.cst).zip ss)).1.Nodup ∧
    (∀ w ∈ (mapG (fun g p => xorV g [p.1, p.2]) gb ((bs.map Wire.cst).zip ss)).1, w.isc = false) ∧
    (∀ w ∈ (mapG (fun g p => xorV g [p.1, p.2]) gb ((bs.map Wire.cst).zip ss)).1,
      w ∈ ss ∨ ∃ t, w = .nd t ∧ gb.n ≤ t ∧ t < (mapG (fun g p => xorV g [p.1, p.2]) gb ((bs.map Wire.cst).zip ss)).2.n) := by
  intro bs
  induction bs with
  | nil =>
    intro ss gb hl _ _
    cases ss with
    | nil => simp [mapG]
    | cons _ _ => simp at hl
  | cons b bt ih =>
    intro ss gb hl hs hnd
    cases ss with
    | nil => simp at hl
    | cons s st =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      obtain ⟨j, hsj, hjn⟩ := hs s List.mem_cons_self
      subst hsj
      have hst : ∀ s' ∈ st, ∃ j', s' = Wire.nd j' ∧ j' < gb.n := fun s' h => hs s' (List.mem_cons_of_mem _ h)
      have hnd' := List.nodup_cons.1 hnd
      have hz : (((b :: bt).map Wire.cst).zip (Wire.nd j :: st)) =
          (Wire.cst b, Wire.nd j) :: ((bt.map Wire.cst).zip st) := rfl
      rw [hz]
      cases b
      · have hf : xorV gb [.cst false, .nd j] = (.nd j, gb) := xorV_false_nd gb j
        have hm : mapG (fun g p => xorV g [p.1, p.2]) gb ((Wire.cst false, Wire.nd j) :: ((bt.map Wire.cst).zip st)) =
            (Wire.nd j :: (mapG (fun g p => xorV g [p.1, p.2]) gb ((bt.map Wire.cst).zip st)).1,
             (mapG (fun g p => xorV g [p.1, p.2]) gb ((bt.map Wire.cst).zip st)).2) := by
          simp only [mapG, hf]
        rw [hm]
        obtain ⟨a, b', c, d, e, f⟩ := ih st gb hl hst hnd'.2
        refine ⟨by simpa using a, by simpa using b', by simp [c], ?_, ?_, ?_⟩
        · refine List.nodup_cons.2 ⟨?_, d⟩
          intro hmem
          rcases f _ hmem with h | ⟨t, ht, h1, h2⟩
          · exact hnd'.1 h
          · have : j = t := by simpa using ht
            omega
        · intro w hw
          rcases List.mem_cons.1 hw with rfl | hw
          · rfl
          · exact e w hw
        · intro w hw
          rcases List.mem_cons.1 hw with rfl | hw
          · exact Or.inl List.mem_cons_self
          · rcases f w hw with h | h
            · exact Or.inl (List.mem_cons_of_mem _ h)
            · exact Or.inr h
      · have hf : xorV gb [.cst true, .nd j] = notV gb (.nd j) := xorV_true_nd gb j
        obtain ⟨n0, e0, f0⟩ := notV_nd gb j
        have hm : mapG (fun g p => xorV g [p.1, p.2]) gb ((Wire.cst true, Wire.nd j) :: ((bt.map Wire.cst).zip st)) =
            (Wire.nd gb.n :: (mapG (fun g p => xorV g [p.1, p.2]) (notV gb (.nd j)).2 ((bt.map Wire.cst).zip st)).1,
             (mapG (fun g p => xorV g [p.1, p.2]) (notV gb (.nd j)).2 ((bt.map Wire.cst).zip st)).2) := by
          simp only [mapG, hf, f0]
        rw [hm]
        obtain ⟨a, b', c, d, e, f⟩ := ih st (notV gb (.nd j)).2 hl (fun s' h => by
          obtain ⟨j', h1, h2⟩ := hst s' h
          exact ⟨j', h1, by rw [n0]; omega⟩) hnd'.2
        refine ⟨?_, ?_, by simp [c], ?_, ?_, ?_⟩
        · rw [a, n0, List.count_cons]; simp; omega
        · rw [b', e0, List.count_cons]; simp; omega
        · refine List.nodup_cons.2 ⟨?_, d⟩
          intro hmem
          rcases f _ hmem with h | ⟨t, ht, h1, h2⟩
          · obtain ⟨j', h3, h4⟩ := hst _ h
            have : gb.n = j' := by simpa using h3
            omega
          · have : gb.n = t := by simpa using ht
            rw [n0] at h1
            omega
        · intro w hw
          rcases List.mem_cons.1 hw with rfl | hw
          · rfl
          · exact e w hw
        · intro w hw
          rcases List.mem_cons.1 hw with rfl | hw
          · refine Or.inr ⟨gb.n, rfl, Nat.le_refl _, ?_⟩
            rw [a, n0]; omega
          · rcases f w hw with h | ⟨t, ht, h1, h2⟩
            · exact Or.inl (List.mem_cons_of_mem _ h)
            · refine Or.inr ⟨t, ht, by rw [n0] at h1; omega, ?_⟩
              rw [a, n0] at h2 ⊢
              first | omega | (simp [List.count_cons]; omega)

theorem decoderOne_multi (gb : GB) (shift : List Wire) (i : Nat) (hi : i < 2 ^ shift.length) :
    multiV xorV gb (constBits i) shift =
      mapG (fun g p => xorV g [p.1, p.2]) gb (((bitsOf i shift.length).map Wire.cst).zip shift) := by
  have hbl : bitLen i ≤ shift.length := bitLen_le i _ hi
  unfold multiV
  dsimp only
  have hmax : max (constBits i).length shift.length = shift.length := by
    simp only [constBits, List.length_map, List.length_range]; omega
  have hz : zeroExt shift.length shift = shift := by unfold zeroExt; simp
  rw [hmax, zeroExt_constBits i _ hbl, hz]

theorem decoderOne_cost (gb : GB) (shift : List Wire) (hs : ∀ s ∈ shift, ∃ j, s = .nd j ∧ j < gb.n)
    (hnd : shift.Nodup) (hm : 1 ≤ shift.length) (i : Nat) (hi : i < 2 ^ shift.length) :
    (decoderOne gb shift i).2.n = gb.n + (bitsOf i shift.length).count true + (if 2 ≤ shift.length then 2 else 1) ∧
    (decoderOne gb shift i).2.e =
      gb.e + (bitsOf i shift.length).count true + (if 2 ≤ shift.length then shift.length + 1 else 1) := by
  unfold decoderOne
  dsimp only
  rw [decoderOne_multi gb shift i hi]
  obtain ⟨a, b, c, d, e, f⟩ := xorPairs_spec (bitsOf i shift.length) shift gb (by simp [bitsOf_length]) hs hnd
  generalize mapG (fun g p => xorV g [p.1, p.2]) gb (((bitsOf i shift.length).map Wire.cst).zip shift) = M at a b c d e f
  unfold cmpZeroV
  have hne0 : M.1.length ≠ 0 := by rw [c]; omega
  have hl0 : ¬ (M.1.length == 0) = true := by simpa using hne0
  rw [if_neg hl0]
  show (notV (orV M.2 M.1).2 (orV M.2 M.1).1).2.n = _ ∧ (notV (orV M.2 M.1).2 (orV M.2 M.1).1).2.e = _
  by_cases h2 : 2 ≤ shift.length
  · obtain ⟨o1, o2, o3⟩ := orV_many M.2 M.1 e d (by rw [c]; exact h2)
    rw [o3]
    obtain ⟨p1, p2, _⟩ := notV_nd (orV M.2 M.1).2 (M.2.n)
    constructor <;> simp only [h2, ↓reduceIte] <;> omega
  · have h1 : shift.length = 1 := by omega
    have hM1 : ∃ w, M.1 = [w] := by
      rcases hl : M.1 with _ | ⟨w, _ | ⟨w2, rest⟩⟩
      · rw [hl] at hne0; simp at hne0
      · exact ⟨w, rfl⟩
      · exfalso
        have h3 := c
        rw [hl] at h3
        simp only [List.length_cons] at h3
        omega
    obtain ⟨w, hw⟩ := hM1
    have hwc : w.isc = false := e w (by rw [hw]; simp)
    rw [hw, orV_one M.2 hwc]
    cases w with
    | cst b => simp [Wire.isc] at hwc
    | nd t =>
      obtain ⟨p1, p2, _⟩ := notV_nd M.2 t
      constructor <;> simp only [h2, ↓reduceIte] <;> omega

theorem sum_range_double (g : Nat → Nat) : ∀ n, ((List.range (2 * n)).map g).sum =
    ((List.range n).map fun q => g (2 * q) + g (2 * q + 1)).sum := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    rw [h, List.range_succ, List.range_succ, List.map_append, List.sum_append, List.map_append, List.sum_append,
      List.range_succ, List.map_append, List.sum_append]
    have ih' := ih
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) from by omega] at *
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

theorem sum_map_lin (l : List Nat) (f : Nat → Nat) :
    (l.map fun q => 2 * f q + 1).sum = 2 * (l.map f).sum + l.length := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega

theorem sum_map_add_const (l : List Nat) (f : Nat → Nat) (k : Nat) :
    (l.map fun q => f q + k).sum = (l.map f).sum + l.length * k := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.add_mul]; omega

theorem bitsOf_count_even (q m : Nat) : (bitsOf (2 * q) (m + 1)).count true = (bitsOf q m).count true := by
  have h1 : (2 * q) % 2 = 0 := by omega
  have h2 : (2 * q) / 2 = q := by omega
  simp [bitsOf, h1, h2, List.count_cons]

theorem bitsOf_count_odd (q m : Nat) : (bitsOf (2 * q + 1) (m + 1)).count true = (bitsOf q m).count true + 1 := by
  have h1 : (2 * q + 1) % 2 = 1 := by omega
  have h2 : (2 * q + 1) / 2 = q := by omega
  simp [bitsOf, h1, h2, List.count_cons]

/-- `Σ_{i < 2^m} popcount(i) = m · 2^(m-1)`, stated without division. -/
theorem pop_sum : ∀ m, 2 * ((List.range (2 ^ m)).map fun i => (bitsOf i m).count true).sum = m * 2 ^ m := by
  intro m
  induction m with
  | zero => simp [bitsOf]
  | succ m ih =>
    have h : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [h, sum_range_double]
    have : ∀ q ∈ List.range (2 ^ m), (bitsOf (2 * q) (m + 1)).count true + (bitsOf (2 * q + 1) (m + 1)).count true =
        2 * (bitsOf q m).count true + 1 := by
      intro q _
      rw [bitsOf_count_even, bitsOf_count_odd]; omega
    rw [List.map_congr_left this, sum_map_lin, List.length_range]
    have e1 : (m + 1) * (2 * 2 ^ m) = 2 * (m * 2 ^ m) + 2 * 2 ^ m := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_left_comm]
    rw [e1]
    omega

theorem decoder_cost_aux (gb : GB) (shift : List Wire) (hs : ∀ s ∈ shift, ∃ j, s = .nd j ∧ j < gb.n)
    (hnd : shift.Nodup) (hm : 1 ≤ shift.length) :
    (decoder gb shift).2.n = gb.n + ((List.range (2 ^ shift.length)).map fun i => (bitsOf i shift.length).count true).sum +
      2 ^ shift.length * (if 2 ≤ shift.length then 2 else 1) ∧
    (decoder gb shift).2.e = gb.e + ((List.range (2 ^ shift.length)).map fun i => (bitsOf i shift.length).count true).sum +
      2 ^ shift.length * (if 2 ≤ shift.length then shift.length + 1 else 1) := by
  unfold decoder
  have := mapG_cost (fun g i => decoderOne g shift i)
    (fun i => (bitsOf i shift.length).count true + (if 2 ≤ shift.length then 2 else 1))
    (fun i => (bitsOf i shift.length).count true + (if 2 ≤ shift.length then shift.length + 1 else 1))
    (fun i => i < 2 ^ shift.length) (fun g => ∀ s ∈ shift, ∃ j, s = .nd j ∧ j < g.n)
    (fun g g' hle hq s hs' => by
      obtain ⟨j, h1, h2⟩ := hq s hs'
      exact ⟨j, h1, by omega⟩)
    (fun g i hi hq => by
      obtain ⟨c1, c2⟩ := decoderOne_cost g shift hq hnd hm i hi
      exact ⟨by omega, by omega⟩) (List.range (2 ^ shift.length)) gb
    (fun a ha => List.mem_range.1 ha) hs
  rw [sum_map_add_const, sum_map_add_const, List.length_range] at this
  obtain ⟨h1, h2⟩ := this
  exact ⟨by omega, by omega⟩

/-- Number of nodes and edges of the literal `decoder_to_virtual` for `m ≥ 2` address bits (the nodes of the
distinct input wires are not counted): `n = (m + 4) · 2^(m-1)`, `e = (3m + 2) · 2^(m-1)`. -/
theorem decoder_cost_ge2 (gb : GB) (shift : List Wire) (hs : ∀ s ∈ shift, ∃ j, s = .nd j ∧ j < gb.n)
    (hnd : shift.Nodup) (hm : 2 ≤ shift.length) :
    2 * (decoder gb shift).2.n = 2 * gb.n + (shift.length + 4) * 2 ^ shift.length ∧
    2 * (decoder gb shift).2.e = 2 * gb.e + (3 * shift.length + 2) * 2 ^ shift.length := by
  obtain ⟨a, b⟩ := decoder_cost_aux gb shift hs hnd (by omega)
  have hp := pop_sum shift.length
  simp only [hm, ↓reduceIte] at a b
  have e : (shift.length + 4) * 2 ^ shift.length = shift.length * 2 ^ shift.length + 4 * 2 ^ shift.length := by
    rw [Nat.add_mul]
  have e3 : (3 * shift.length + 2) * 2 ^ shift.length = 3 * (shift.length * 2 ^ shift.length) + 2 * 2 ^ shift.length := by
    rw [Nat.add_mul, Nat.mul_assoc]
  have e2 : 2 ^ shift.length * (shift.length + 1) = shift.length * 2 ^ shift.length + 2 ^ shift.length := by
    rw [Nat.mul_add, Nat.mul_comm, Nat.mul_one]
  rw [e, e3]
  rw [e2] at b
  constructor <;> omega

theorem decoder_cost_one (gb : GB) (shift : List Wire) (hs : ∀ s ∈ shift, ∃ j, s = .nd j ∧ j < gb.n)
    (hnd : shift.Nodup) (hm : shift.length = 1) :
    (decoder gb shift).2.n = gb.n + 3 ∧ (decoder gb shift).2.e = gb.e + 3 := by
  obtain ⟨a, b⟩ := decoder_cost_aux gb shift hs hnd (by omega)
  have hp := pop_sum shift.length
  rw [hm] at a b hp
  simp at a b hp
  omega

theorem decoder_cost_zero (gb : GB) : (decoder gb []).2.n = gb.n ∧ (decoder gb []).2.e = gb.e := by
  simp [decoder, decoderOne, multiV, cmpZeroV, mapG, constBits, bitLen, zeroExt]

end SmcIrred
