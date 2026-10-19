module

public import SmcIrred.Spec.Recode
public import SmcIrred.Arith.ModExp

public section

namespace SmcIrred.Arith

/-! # NAF and MOF (C58, G31 b)

Existence, uniqueness (up to trailing zeros), minimal Hamming weight among all signed binary representations, weight at most
the binary weight and at most `⌈(len + 1)/2⌉`; the MOF has the right value, alternating signs, and *no* weight reduction (the
weight of `101` is 4 against 2). -/

theorem wt_nil : wt [] = 0 := rfl

theorem wt_cons (a : Int) (t : List Int) : wt (a :: t) = (if a = 0 then 0 else 1) + wt t := by
  unfold wt
  rw [List.countP_cons]
  by_cases h : a = 0 <;> simp [h, Nat.add_comm]

theorem sval_cons (a : Int) (t : List Int) : sval (a :: t) = a + 2 * sval t := rfl

/-! ### The function `naf` -/

theorem naf_zero : naf 0 = [] := by rw [naf]; simp

theorem naf_even {n : Int} (h0 : n ≠ 0) (h : n % 2 = 0) : naf n = 0 :: naf (n / 2) := by
  rw [naf]; simp [h0, h]

theorem naf_odd {n : Int} (h : n % 2 ≠ 0) : naf n = (2 - n % 4) :: naf ((n - (2 - n % 4)) / 2) := by
  have h0 : n ≠ 0 := by omega
  rw [naf]; simp [h0, h]

theorem sval_naf (n : Int) : sval (naf n) = n := by
  by_cases h0 : n = 0
  · subst h0; simp [naf_zero, sval]
  by_cases h : n % 2 = 0
  · rw [naf_even h0 h, sval_cons, sval_naf (n / 2)]; omega
  · rw [naf_odd h, sval_cons, sval_naf ((n - (2 - n % 4)) / 2)]; omega
termination_by n.natAbs
decreasing_by all_goals omega

theorem sd_naf (n : Int) : Sd (naf n) := by
  by_cases h0 : n = 0
  · subst h0; simp [naf_zero, Sd]
  by_cases h : n % 2 = 0
  · rw [naf_even h0 h]
    have := sd_naf (n / 2)
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact Or.inl rfl
    · exact this d hd
  · rw [naf_odd h]
    have := sd_naf ((n - (2 - n % 4)) / 2)
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · omega
    · exact this d hd
termination_by n.natAbs
decreasing_by all_goals omega

theorem isNaf_naf (n : Int) : IsNaf (naf n) := by
  by_cases h0 : n = 0
  · subst h0; rw [naf_zero]; exact .nil
  by_cases h : n % 2 = 0
  · rw [naf_even h0 h]; exact .zero (isNaf_naf (n / 2))
  · rw [naf_odd h]
    refine .nz (by omega) (isNaf_naf _) ?_
    by_cases h1 : (n - (2 - n % 4)) / 2 = 0
    · left; rw [h1, naf_zero]
    · right
      exact ⟨_, naf_even h1 (by omega)⟩
termination_by n.natAbs
decreasing_by all_goals omega

/-- Existence of the NAF: every integer has one. -/
theorem naf_exists (n : Int) : ∃ d, IsNaf d ∧ sval d = n := ⟨naf n, isNaf_naf n, sval_naf n⟩

/-- Uniqueness: every NAF of `n` is `naf n` followed by zeros. -/
theorem naf_unique {d : List Int} (hd : IsNaf d) : ∃ k, d = naf (sval d) ++ List.replicate k 0 := by
  induction hd with
  | nil => exact ⟨0, by simp [sval, naf_zero]⟩
  | @zero t ht ih =>
    obtain ⟨k, hk⟩ := ih
    by_cases h0 : sval t = 0
    · refine ⟨k + 1, ?_⟩
      rw [h0, naf_zero] at hk
      rw [sval_cons, h0]
      simp [naf_zero, hk, List.replicate_succ]
    · refine ⟨k, ?_⟩
      rw [sval_cons, naf_even (by omega) (by omega)]
      have : (0 + 2 * sval t) / 2 = sval t := by omega
      rw [this, List.cons_append, ← hk]
  | @nz a t ha ht hnext ih =>
    obtain ⟨k, hk⟩ := ih
    have hev : sval t % 2 = 0 := by
      rcases hnext with rfl | ⟨t', rfl⟩
      · simp [sval]
      · simp [sval_cons]
    have hodd : (a + 2 * sval t) % 2 ≠ 0 := by omega
    refine ⟨k, ?_⟩
    rw [sval_cons, naf_odd hodd]
    have hu : 2 - (a + 2 * sval t) % 4 = a := by omega
    have hm : (a + 2 * sval t - a) / 2 = sval t := by omega
    rw [hu, hm, List.cons_append, ← hk]

/-! ### Minimal weight -/

/-- The weight of the NAF. -/
@[expose] def nw (n : Int) : Nat := wt (naf n)

theorem nw_zero : nw 0 = 0 := by simp [nw, naf_zero, wt_nil]

theorem nw_even {n : Int} (h : n % 2 = 0) : nw n = nw (n / 2) := by
  by_cases h0 : n = 0
  · subst h0; simp [nw_zero]
  · unfold nw; rw [naf_even h0 h, wt_cons]; simp

theorem nw_odd {n : Int} (h : n % 2 ≠ 0) : nw n = 1 + nw ((n - (2 - n % 4)) / 2) := by
  unfold nw; rw [naf_odd h, wt_cons]
  have : (2 - n % 4) ≠ 0 := by omega
  simp [this]

theorem nw_double (m : Int) : nw (2 * m) = nw m := by
  rw [nw_even (by omega)]
  congr 1; omega

/-- One step above or below an even number costs at most one more nonzero digit, given that the halves behave. -/
theorem nw_lip {e : Int} (he : e % 2 = 0)
    (hA : e % 4 = 2 → nw (e / 2 + 1) ≤ nw (e / 2) ∧ nw (e / 2 - 1) ≤ nw (e / 2)) :
    nw (e + 1) ≤ nw e + 1 ∧ nw (e - 1) ≤ nw e + 1 := by
  have hne : nw e = nw (e / 2) := nw_even he
  constructor
  · by_cases h4 : (e + 1) % 4 = 1
    · rw [nw_odd (by omega)]
      have : (e + 1 - (2 - (e + 1) % 4)) / 2 = e / 2 := by omega
      rw [this]; omega
    · rw [nw_odd (by omega)]
      have : (e + 1 - (2 - (e + 1) % 4)) / 2 = e / 2 + 1 := by omega
      rw [this]
      have := (hA (by omega)).1
      omega
  · by_cases h4 : (e - 1) % 4 = 3
    · rw [nw_odd (by omega)]
      have : (e - 1 - (2 - (e - 1) % 4)) / 2 = e / 2 := by omega
      rw [this]; omega
    · rw [nw_odd (by omega)]
      have : (e - 1 - (2 - (e - 1) % 4)) / 2 = e / 2 - 1 := by omega
      rw [this]
      have := (hA (by omega)).2
      omega

/-- For odd `j` both even neighbours have at most the NAF weight of `j`. -/
theorem nw_odd_nb (j : Int) (hj : j % 2 ≠ 0) : nw (j - 1) ≤ nw j ∧ nw (j + 1) ≤ nw j := by
  by_cases h1 : j % 4 = 1
  · have hj' : nw j = 1 + nw ((j - 1) / 2) := by
      rw [nw_odd hj]; congr 2; omega
    have hlip := nw_lip (e := (j - 1) / 2) (by omega) (fun h4 => by
      have := nw_odd_nb ((j - 1) / 2 / 2) (by omega)
      exact ⟨this.2, this.1⟩)
    constructor
    · have : j - 1 = 2 * ((j - 1) / 2) := by omega
      rw [this, nw_double]; omega
    · have : j + 1 = 2 * ((j - 1) / 2 + 1) := by omega
      rw [this, nw_double]; omega
  · have h3 : j % 4 = 3 := by omega
    have hj' : nw j = 1 + nw ((j + 1) / 2) := by
      rw [nw_odd hj]; congr 2; omega
    have hlip := nw_lip (e := (j + 1) / 2) (by omega) (fun h4 => by
      have := nw_odd_nb ((j + 1) / 2 / 2) (by omega)
      exact ⟨this.2, this.1⟩)
    constructor
    · have : j - 1 = 2 * ((j + 1) / 2 - 1) := by omega
      rw [this, nw_double]; omega
    · have : j + 1 = 2 * ((j + 1) / 2) := by omega
      rw [this, nw_double]; omega
termination_by j.natAbs
decreasing_by all_goals omega

/-- **The NAF has minimal Hamming weight** among all signed binary representations of the same value. -/
theorem naf_minimal {d : List Int} (hd : Sd d) : wt (naf (sval d)) ≤ wt d := by
  induction d with
  | nil => simp [sval, naf_zero, wt_nil]
  | cons h t ih =>
    have hh := hd h (List.mem_cons_self ..)
    have ht : Sd t := fun x hx => hd x (List.mem_cons_of_mem _ hx)
    have ih' := ih ht
    change nw (sval (h :: t)) ≤ wt (h :: t)
    change nw (sval t) ≤ wt t at ih'
    rw [sval_cons, wt_cons]
    rcases hh with rfl | rfl | rfl
    · simp only [Int.zero_add, if_true, Nat.zero_add]
      rw [nw_double]; exact ih'
    · simp only [Int.one_ne_zero, if_false]
      by_cases hm : sval t % 2 = 0
      · rw [nw_odd (by omega)]
        have : (1 + 2 * sval t - (2 - (1 + 2 * sval t) % 4)) / 2 = sval t := by omega
        rw [this]; omega
      · rw [nw_odd (by omega)]
        have : (1 + 2 * sval t - (2 - (1 + 2 * sval t) % 4)) / 2 = sval t + 1 := by omega
        rw [this]
        have := (nw_odd_nb (sval t) hm).2
        omega
    · simp only [if_neg (show (-1 : Int) ≠ 0 by omega)]
      by_cases hm : sval t % 2 = 0
      · rw [nw_odd (by omega)]
        have : (-1 + 2 * sval t - (2 - (-1 + 2 * sval t) % 4)) / 2 = sval t := by omega
        rw [this]; omega
      · rw [nw_odd (by omega)]
        have : (-1 + 2 * sval t - (2 - (-1 + 2 * sval t) % 4)) / 2 = sval t - 1 := by omega
        rw [this]
        have := (nw_odd_nb (sval t) hm).1
        omega

end SmcIrred.Arith
