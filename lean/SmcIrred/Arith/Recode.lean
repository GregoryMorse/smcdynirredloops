module

public import SmcIrred.Arith.NAF

public section

namespace SmcIrred.Arith

/-! # NAF weight bounds and the MOF (C58, G31 b) -/

/-! ### Against the binary representation -/

theorem sval_bin (n : Nat) : sval (bin n) = n := by
  by_cases h : n = 0
  · subst h; simp [bin, sval]
  · rw [bin, dif_neg h, sval_cons, sval_bin (n / 2)]; omega
termination_by n
decreasing_by omega

theorem sd_bin (n : Nat) : Sd (bin n) := by
  by_cases h : n = 0
  · subst h; simp [bin, Sd]
  · rw [bin, dif_neg h]
    have := sd_bin (n / 2)
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · omega
    · exact this d hd
termination_by n
decreasing_by omega

theorem wt_bin (n : Nat) : wt (bin n) = popc n := by
  by_cases h : n = 0
  · subst h; simp [bin, popc, wt_nil]
  · rw [bin, dif_neg h, wt_cons, wt_bin (n / 2), popc_step h]
    by_cases hm : n % 2 = 0
    · have : ((n % 2 : Nat) : Int) = 0 := by omega
      rw [if_pos this]; omega
    · have : ((n % 2 : Nat) : Int) ≠ 0 := by omega
      rw [if_neg this]; omega
termination_by n
decreasing_by omega

/-- The NAF never has more nonzero digits than the binary representation. -/
theorem naf_le_popc (n : Nat) : wt (naf n) ≤ popc n := by
  have := naf_minimal (sd_bin n)
  rwa [sval_bin, wt_bin] at this

/-! ### Non-adjacency bounds the weight -/

theorem naf_weight_len {d : List Int} (hd : IsNaf d) :
    2 * wt d ≤ d.length + 1 ∧ (∀ d', d = 0 :: d' → 2 * wt d ≤ d.length) := by
  induction hd with
  | nil => simp [wt_nil]
  | @zero t ht ih =>
    obtain ⟨h1, _⟩ := ih
    refine ⟨?_, fun d' _ => ?_⟩ <;> rw [wt_cons] <;> simp <;> omega
  | @nz a t ha ht hnext ih =>
    obtain ⟨h1, h2⟩ := ih
    have hne : a ≠ 0 := by omega
    refine ⟨?_, fun d' h => absurd (List.cons.inj h).1 hne⟩
    rw [wt_cons, if_neg hne]
    rcases hnext with rfl | ⟨t', rfl⟩
    · simp [wt_nil]
    · have := h2 t' rfl
      simp only [List.length_cons] at this ⊢
      omega

/-- No two adjacent nonzero digits: at most `⌈(len + 1)/2⌉` of them. -/
theorem naf_weight_le {d : List Int} (hd : IsNaf d) : 2 * wt d ≤ d.length + 1 := (naf_weight_len hd).1

/-- A NAF of length `L` represents a number of absolute value more than `2^L / 3`. -/
theorem naf_len_pow (n : Int) (h0 : n ≠ 0) : 2 ^ (naf n).length + 1 ≤ 3 * n.natAbs := by
  by_cases h : n % 2 = 0
  · rw [naf_even h0 h, List.length_cons, Nat.pow_succ]
    have := naf_len_pow (n / 2) (by omega)
    omega
  · rw [naf_odd h, List.length_cons]
    by_cases hm : (n - (2 - n % 4)) / 2 = 0
    · rw [hm, naf_zero]
      simp
      omega
    · have hev : (n - (2 - n % 4)) / 2 % 2 = 0 := by omega
      rw [naf_even hm hev, List.length_cons, Nat.pow_succ, Nat.pow_succ]
      have := naf_len_pow ((n - (2 - n % 4)) / 2 / 2) (by omega)
      omega
termination_by n.natAbs
decreasing_by all_goals omega

/-- The NAF of `n` has at most `bitLen n + 1` digits. -/
theorem naf_length_le (n : Nat) (h0 : n ≠ 0) : (naf n).length ≤ bitLen n + 1 := by
  have h1 := naf_len_pow n (by omega)
  have h2 := (bitLen_spec h0).2
  have hb : 1 ≤ bitLen n := by
    rcases Nat.eq_zero_or_pos (bitLen n) with h | h
    · rw [h] at h2; simp at h2; omega
    · exact h
  simp only [Int.natAbs_natCast] at h1
  refine Nat.le_of_not_lt fun hc => ?_
  have h3 : 2 ^ (bitLen n + 2) ≤ 2 ^ (naf n).length := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : 2 ^ (bitLen n + 2) = 4 * 2 ^ bitLen n := by rw [Nat.pow_add]; omega
  omega

/-- **Weight of the NAF**: at most `⌈(len + 1)/2⌉` for a number of bit length `len`. -/
theorem naf_weight_bound (n : Nat) : 2 * wt (naf n) ≤ bitLen n + 2 := by
  by_cases h0 : n = 0
  · subst h0; simp [naf_zero, wt_nil]
  · have h1 := naf_weight_le (isNaf_naf n)
    have h2 := naf_length_le n h0
    omega

/-! ### Mutual opposite form -/

theorem sval_mofGo (p : Int) (b : List Int) : sval (mofGo p b) = p + sval b := by
  induction b generalizing p with
  | nil => simp [mofGo, sval]
  | cons x xs ih => simp only [mofGo, sval_cons, ih]; omega

/-- The MOF has the value of the binary digits. -/
theorem sval_mof (b : List Int) : sval (mof b) = sval b := by
  unfold mof; rw [sval_mofGo]; omega

theorem sd_mofGo {p : Int} {b : List Int} (hp : p = 0 ∨ p = 1) (hb : ∀ x ∈ b, x = 0 ∨ x = 1) : Sd (mofGo p b) := by
  induction b generalizing p with
  | nil => intro d hd; simp [mofGo] at hd; omega
  | cons x xs ih =>
    have hx := hb x (List.mem_cons_self ..)
    intro d hd
    simp only [mofGo, List.mem_cons] at hd
    rcases hd with rfl | hd
    · omega
    · exact ih hx (fun y hy => hb y (List.mem_cons_of_mem _ hy)) d hd

theorem sd_mof {b : List Int} (hb : ∀ x ∈ b, x = 0 ∨ x = 1) : Sd (mof b) := sd_mofGo (Or.inl rfl) hb

theorem alt_mofGo {p : Int} {b : List Int} (hp : p = 0 ∨ p = 1) (hb : ∀ x ∈ b, x = 0 ∨ x = 1) :
    Alt (if p = 0 then -1 else 1) (mofGo p b) := by
  induction b generalizing p with
  | nil =>
    simp only [mofGo]
    rcases hp with rfl | rfl
    · exact .zero .nil
    · exact .nz (Or.inl rfl) .nil
  | cons x xs ih =>
    have hx := hb x (List.mem_cons_self ..)
    have ih' := ih hx (fun y hy => hb y (List.mem_cons_of_mem _ hy))
    simp only [mofGo]
    rcases hp with rfl | rfl <;> rcases hx with rfl | rfl <;> simp at ih' ⊢
    · exact .zero ih'
    · exact .nz (Or.inr rfl) (by simpa using ih')
    · exact .nz (Or.inl rfl) (by simpa using ih')
    · exact .zero ih'

/-- The nonzero digits of the MOF alternate in sign, starting with `-1`. -/
theorem alt_mof {b : List Int} (hb : ∀ x ∈ b, x = 0 ∨ x = 1) : Alt (-1) (mof b) := by
  unfold mof
  simpa using alt_mofGo (p := 0) (Or.inl rfl) hb

/-- The MOF does **not** reduce the Hamming weight of every number: `5 = 101₂` has MOF weight 4. -/
theorem mof_not_lighter : wt (mof (bin 5)) = 4 ∧ popc 5 = 2 := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

theorem mof_five : mof (bin 5) = [-1, 1, -1, 1] := by decide +kernel

/-! ### Average weights over all `n`-bit strings -/

theorem allBits_length : ∀ n, (allBits n).length = 2 ^ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [allBits, ih, Nat.pow_succ]; omega

theorem sum_map_add_const {α : Type} (c : Nat) (f : α → Nat) (l : List α) :
    (l.map fun b => c + f b).sum = l.length * c + (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; rw [Nat.add_mul]; omega

/-- Total MOF weight after a previous bit `p` over all `n`-bit strings. -/
def mofTotal (p : Int) (n : Nat) : Nat := ((allBits n).map fun b => wt (mofGo p b)).sum

theorem mofTotal_zero (p : Int) : mofTotal p 0 = if p = 0 then 0 else 1 := by
  simp [mofTotal, allBits, mofGo, wt_cons, wt_nil]

theorem mofTotal_succ (p : Int) (hp : p = 0 ∨ p = 1) (n : Nat) :
    mofTotal p (n + 1) = 2 ^ n + (mofTotal 0 n + mofTotal 1 n) := by
  unfold mofTotal
  simp only [allBits, List.map_append, List.map_map, List.sum_append]
  have e : ∀ x : Int, ((allBits n).map ((fun b => wt (mofGo p b)) ∘ fun b => x :: b)).sum
      = 2 ^ n * (if p = x then 0 else 1) + ((allBits n).map fun b => wt (mofGo x b)).sum := by
    intro x
    have : ∀ b, ((fun b => wt (mofGo p b)) ∘ fun b => x :: b) b = (if p = x then 0 else 1) + wt (mofGo x b) := by
      intro b
      simp only [Function.comp, mofGo, wt_cons]
      by_cases h : p = x
      · subst h; simp
      · have : p - x ≠ 0 := by omega
        simp [h, this]
    rw [List.map_congr_left (fun b _ => this b), sum_map_add_const, allBits_length]
  rw [e 0, e 1]
  rcases hp with rfl | rfl <;> simp <;> omega

theorem mofTotal_closed (n : Nat) : mofTotal 0 n + mofTotal 1 n = (n + 1) * 2 ^ n := by
  induction n with
  | zero => simp [mofTotal_zero]
  | succ n ih =>
    rw [mofTotal_succ 0 (Or.inl rfl), mofTotal_succ 1 (Or.inr rfl), Nat.pow_succ]
    rw [Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc]
    omega

end SmcIrred.Arith
