module

public import SmcIrred.Spec.ModMul

public section

namespace SmcIrred.Arith

/-! # The bit-serial `modmul` computes `a * b mod m` (C54, G31 f)

Invariant of the loop: after the bits `l` of the prefix of `a` the accumulator `d` is below `m` and congruent to
`prefix * b` modulo `m`; the doubling step stays within `[0, m]` and the final conditional subtraction brings the
accumulator below `m`. -/

theorem modmulStep_spec {m b d x : Nat} (hm : 0 < m) (hb : b < m) (hd : d < m) (hx : x ≤ 1) :
    modmulStep m b d x < m ∧ (modmulStep m b d x = 2 * d + x * b ∨ modmulStep m b d x + m = 2 * d + x * b ∨
      modmulStep m b d x + 2 * m = 2 * d + x * b) := by
  have h2 : 2 * (m / 2) ≤ m := by omega
  have h3 : m ≤ 2 * (m / 2) + 1 := by omega
  rcases Nat.eq_zero_or_pos x with rfl | hx1
  · unfold modmulStep
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.add_zero]
    repeat' split
    all_goals omega
  · have hx1' : x = 1 := by omega
    subst hx1'
    unfold modmulStep
    simp only [bne_iff_ne, ne_eq, Nat.one_ne_zero, not_false_eq_true, ↓reduceIte, Nat.one_mul]
    repeat' split
    all_goals omega

theorem msbBits_le (a : Nat) : ∀ x ∈ msbBits a, x ≤ 1 := by
  by_cases h : a = 0
  · subst h; simp [msbBits]
  · rw [msbBits, dif_neg h]
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact msbBits_le (a / 2) x hx
    · simp at hx; omega
termination_by a
decreasing_by omega

theorem msbVal_append (v : Nat) (l : List Nat) (x : Nat) : msbVal v (l ++ [x]) = 2 * msbVal v l + x := by
  simp [msbVal, List.foldl_append]

theorem msbVal_msbBits (a : Nat) : msbVal 0 (msbBits a) = a := by
  by_cases h : a = 0
  · subst h; simp [msbBits, msbVal]
  · rw [msbBits, dif_neg h, msbVal_append, msbVal_msbBits (a / 2)]; omega
termination_by a
decreasing_by omega

theorem modmul_fold {m b : Nat} (hm : 0 < m) (hb : b < m) :
    ∀ (l : List Nat) (d v : Nat), (∀ x ∈ l, x ≤ 1) → d < m → d % m = (v * b) % m →
      l.foldl (modmulStep m b) d < m ∧ l.foldl (modmulStep m b) d % m = (msbVal v l * b) % m := by
  intro l
  induction l with
  | nil => intro d v _ hd hv; exact ⟨hd, by simpa [msbVal] using hv⟩
  | cons x t ih =>
    intro d v hl hd hv
    have hx : x ≤ 1 := hl x (List.mem_cons_self ..)
    have hs := modmulStep_spec hm hb hd hx
    have key : ∀ d e c : Nat, d % m = e % m → (2 * d + c) % m = (2 * e + c) % m := by
      intro d e c h
      rw [Nat.add_mod, Nat.mul_mod, h, ← Nat.mul_mod, ← Nat.add_mod]
    have hmod : modmulStep m b d x % m = ((2 * v + x) * b) % m := by
      have e1 : (2 * v + x) * b = 2 * (v * b) + x * b := by rw [Nat.add_mul, Nat.mul_assoc]
      rw [e1, ← key d (v * b) (x * b) hv]
      rcases hs.2 with h | h | h
      · rw [h]
      · rw [← h, Nat.add_mod_right]
      · rw [← h, Nat.add_mul_mod_self_right]
    have := ih (modmulStep m b d x) (2 * v + x) (fun y hy => hl y (List.mem_cons_of_mem _ hy)) hs.1 hmod
    simp only [List.foldl_cons]
    refine ⟨this.1, ?_⟩
    rw [this.2]
    simp [msbVal]

/-- **The bit-serial `modmul` computes `a * b mod m`.** -/
theorem modmulBit_eq {a b m : Nat} (hm : 0 < m) : modmulBit a b m = a * b % m := by
  have hb : b % m < m := Nat.mod_lt _ hm
  have := modmul_fold hm hb (msbBits (a % m)) 0 0 (msbBits_le _) hm (by simp)
  unfold modmulBit
  have h1 := this.2
  rw [msbVal_msbBits] at h1
  rw [← Nat.mod_eq_of_lt this.1, h1]
  exact (Nat.mul_mod a b m).symm

end SmcIrred.Arith
