module

public import SmcIrred.Spec.Virt
public import SmcIrred.Spec.BvDsl

public section

namespace SmcIrred

/-- The little-endian bit list of `i` of length `m`. -/
@[expose] def bitsOf : Nat → Nat → List Bool
  | _, 0 => []
  | i, m + 1 => decide (i % 2 = 1) :: bitsOf (i / 2) m

theorem bv_lt (bs : List Bool) : bv bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [bv]
  | cons b t ih =>
    simp only [bv, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

theorem bv_bitsOf : ∀ m i, i < 2 ^ m → bv (bitsOf i m) = i := by
  intro m
  induction m with
  | zero => intro i h; simp at h; simp [bitsOf, bv, h]
  | succ m ih =>
    intro i h
    have h2 : i / 2 < 2 ^ m := by rw [Nat.pow_succ] at h; omega
    simp only [bitsOf, bv]
    rw [ih (i / 2) h2]
    by_cases hi : i % 2 = 1 <;> simp [hi] <;> omega

theorem bv_inj : ∀ (bs cs : List Bool), bs.length = cs.length → bv bs = bv cs → bs = cs := by
  intro bs
  induction bs with
  | nil => intro cs h _; cases cs with | nil => rfl | cons _ _ => simp at h
  | cons b t ih =>
    intro cs h hv
    cases cs with
    | nil => simp at h
    | cons c u =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [bv] at hv
      have h1 : (if b then 1 else 0) = (if c then 1 else 0) := by
        cases b <;> cases c <;> simp at hv ⊢ <;> omega
      have h2 : bv t = bv u := by omega
      have hbc : b = c := by cases b <;> cases c <;> simp at h1 ⊢
      rw [hbc, ih u h h2]

theorem bitsOf_length : ∀ m i, (bitsOf i m).length = m := by
  intro m; induction m with
  | zero => intro i; rfl
  | succ m ih => intro i; simp [bitsOf, ih]

theorem bitLen_succ (n : Nat) : bitLen (n + 1) = bitLen ((n + 1) / 2) + 1 := by
  rw [bitLen]

theorem bitLen_le : ∀ i m, i < 2 ^ m → bitLen i ≤ m := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro m h
    cases i with
    | zero => rw [bitLen]; exact Nat.zero_le _
    | succ n =>
      cases m with
      | zero => simp at h
      | succ m =>
        rw [bitLen_succ]
        have h2 : (n + 1) / 2 < 2 ^ m := by rw [Nat.pow_succ] at h; omega
        have := ih ((n + 1) / 2) (by omega) m h2
        omega

theorem testBit_ge : ∀ j i, bitLen i ≤ j → i.testBit j = false := by
  intro j
  induction j with
  | zero =>
    intro i h
    cases i with
    | zero => simp
    | succ n => rw [bitLen_succ] at h; omega
  | succ j ih =>
    intro i h
    cases i with
    | zero => simp
    | succ n =>
      rw [bitLen_succ] at h
      rw [Nat.testBit_succ]
      exact ih _ (by omega)

theorem bitsOf_range : ∀ m i, (List.range m).map (fun j => i.testBit j) = bitsOf i m := by
  intro m
  induction m with
  | zero => intro i; rfl
  | succ m ih =>
    intro i
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [bitsOf]
    congr 1
    · simp [Nat.testBit_zero]
    · rw [← ih (i / 2)]
      apply List.map_congr_left
      intro j _
      simp [Function.comp, Nat.testBit_succ]

theorem natBits_eq_bitsOf : ∀ (m i : Nat), natBits i m = bitsOf i m := by
  intro m
  induction m with
  | zero => intro i; rfl
  | succ m ih => intro i; simp only [natBits, bitsOf, ih]

theorem zeroExt_constBits (i m : Nat) (h : bitLen i ≤ m) :
    zeroExt m (constBits i) = (bitsOf i m).map Wire.cst := by
  unfold zeroExt constBits
  rw [List.length_map, List.length_range, ← bitsOf_range, List.map_map]
  have : m = bitLen i + (m - bitLen i) := by omega
  conv => rhs; rw [this, List.range_add, List.map_append]
  rw [List.map_map]
  congr 1
  · symm
    have : ∀ t ∈ List.range (m - bitLen i),
        ((Wire.cst ∘ fun j => i.testBit j) ∘ fun x => bitLen i + x) t = Wire.cst false := by
      intro t _
      simp only [Function.comp]
      rw [testBit_ge _ i (by omega)]
    rw [List.map_congr_left this]
    rw [List.map_const', List.length_range]

/-- The hot position of a one-hot vector splits in two halves by the next bit. -/
theorem oneHot_split (L x : Nat) (hx : x < L) (b : Bool) :
    (oneHot L x).map (fun v => v && !b) ++ (oneHot L x).map (fun v => v && b) =
      oneHot (2 * L) (x + L * (if b then 1 else 0)) := by
  unfold oneHot
  rw [Nat.two_mul, List.range_add, List.map_append]
  simp only [List.map_map]
  congr 1 <;>
  (apply List.map_congr_left
   intro p hp
   have := List.mem_range.1 hp
   simp only [Function.comp]
   apply Bool.eq_iff_iff.2
   cases b <;> (try simp) <;> (try omega))

end SmcIrred
