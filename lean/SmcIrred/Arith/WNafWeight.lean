module

public import SmcIrred.Arith.WNaf
public import SmcIrred.Arith.Recode
public import SmcIrred.Arith.ModExp

public section

namespace SmcIrred.Arith

/-! # The windowed NAF never has more nonzero digits than binary (C58, G31 b)

For the window `q + 1 = 2^j` the windowed non-adjacent form of a natural number has at most `popc n` nonzero digits
(`wnaf_wt_le_popc`): the paper's "windowed forms which reduce the Hamming weight" holds for the NAF windows in the
non-strict sense, and the strict reduction of the density is the spacing of `wnaf_spaced`. For `q + 1` not a power of two
the bound fails (checked: `q = 2`, `n = 33`), so the hypothesis is needed. -/

theorem popc_zero : popc 0 = 0 := by rw [popc]; simp

theorem popc_step' (e : Nat) : popc e = e % 2 + popc (e / 2) := by
  by_cases h : e = 0
  · subst h; simp [popc_zero]
  · exact popc_step h

theorem popc_shift (b : Nat) : ∀ (r u : Nat), r < 2 ^ b → popc (2 ^ b * u + r) = popc u + popc r := by
  induction b with
  | zero =>
    intro r u hr
    have h0 : r = 0 := by rw [Nat.pow_zero] at hr; omega
    subst h0
    simp [popc_zero]
  | succ b ih =>
    intro r u hr
    have h2 : 2 ^ (b + 1) * u + r = 2 * (2 ^ b * u + r / 2) + r % 2 := by
      have : 2 ^ (b + 1) * u = 2 * (2 ^ b * u) := by rw [Nat.pow_succ, Nat.mul_comm (2 ^ b) 2, Nat.mul_assoc]
      omega
    have hr2 : r / 2 < 2 ^ b := by rw [Nat.pow_succ] at hr; omega
    rw [popc_step' (2 ^ (b + 1) * u + r), popc_step' r, h2]
    have e1 : (2 * (2 ^ b * u + r / 2) + r % 2) % 2 = r % 2 := by omega
    have e2 : (2 * (2 ^ b * u + r / 2) + r % 2) / 2 = 2 ^ b * u + r / 2 := by omega
    rw [e1, e2, ih _ _ hr2]
    omega

theorem popc_succ_le : ∀ u : Nat, popc (u + 1) ≤ popc u + 1 := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
    by_cases h : u % 2 = 0
    · rw [popc_step' (u + 1), popc_step' u]
      have : (u + 1) / 2 = u / 2 := by omega
      rw [this]; omega
    · rw [popc_step' (u + 1), popc_step' u]
      have h1 : (u + 1) / 2 = u / 2 + 1 := by omega
      have := ih (u / 2) (by omega)
      rw [h1]; omega

theorem popc_pos_odd {s : Nat} (h : s % 2 = 1) : 1 ≤ popc s := by
  rw [popc_step' s]; omega

theorem wt_cons_zero (l : List Int) : wt (0 :: l) = wt l := by simp [wt]

theorem wt_cons_ne (d : Int) (l : List Int) (h : d ≠ 0) : wt (d :: l) = wt l + 1 := by
  simp [wt, List.countP_cons, h]

theorem ipow_pos (i : Nat) : (0 : Int) < 2 ^ i := by exact_mod_cast Nat.two_pow_pos i

theorem mul_l1 (P u : Int) : 4 * P * u = 4 * (P * u) := by rw [Int.mul_assoc]

theorem mul_l2 (P u : Int) : 2 * (2 * P * (u + 1)) = 4 * (P * u) + 4 * P := by
  simp only [Int.mul_add, Int.mul_one, Int.mul_assoc]; omega

theorem mul_l3 (P u : Int) : 2 * (2 * P * u) = 4 * (P * u) := by
  simp only [Int.mul_assoc]; omega

theorem wt_wnaf_shift (q : Nat) : ∀ (i : Nat) (c : Int), wt (wnaf q (2 ^ i * c)) = wt (wnaf q c) := by
  intro i
  induction i with
  | zero => intro c; simp
  | succ i ih =>
    intro c
    by_cases h0 : c = 0
    · subst h0; simp
    · have hk : (2 : Int) ^ (i + 1) * c ≠ 0 := by
        have : (2 : Int) ^ (i + 1) ≠ 0 := Int.ne_of_gt (ipow_pos _)
        exact Int.mul_ne_zero this h0
      have hev : ((2 : Int) ^ (i + 1) * c) % 2 = 0 := by
        rw [Int.pow_succ, Int.mul_comm ((2 : Int) ^ i) 2, Int.mul_assoc]; omega
      have hd : ((2 : Int) ^ (i + 1) * c) / 2 = 2 ^ i * c := by
        rw [Int.pow_succ, Int.mul_comm ((2 : Int) ^ i) 2, Int.mul_assoc]; omega
      rw [wnaf_even q hk hev, wt_cons_zero, hd, ih]

theorem wnaf_wt_le_popc (q j : Nat) (hq : q + 1 = 2 ^ j) : ∀ n : Nat, wt (wnaf q (n : Int)) ≤ popc n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h0 : n = 0
    · subst h0; simp [wnaf_zero, wt, popc_zero]
    by_cases hev : n % 2 = 0
    · have hk : (n : Int) ≠ 0 := by omega
      have hk2 : (n : Int) % 2 = 0 := by omega
      rw [wnaf_even q hk hk2, wt_cons_zero, popc_step' n, hev]
      have : (n : Int) / 2 = ((n / 2 : Nat) : Int) := by omega
      rw [this]
      have := ih (n / 2) (by omega)
      omega
    · have hodd : (n : Int) % 2 ≠ 0 := by omega
      rw [wnaf_odd q hodd]
      -- M = 4 (q + 1) = 2^(j+2)
      have hM : 4 * (q + 1) = 2 ^ (j + 2) := by rw [hq, Nat.pow_add]; omega
      have hMi : 4 * ((q : Int) + 1) = ((2 ^ (j + 2) : Nat) : Int) := by
        have h := congrArg (fun x : Nat => (x : Int)) hM
        simpa using h
      have hP1 : (2 : Int) ^ (j + 1) = 2 * 2 ^ j := by rw [Int.pow_succ]; omega
      have hP2 : (2 : Int) ^ (j + 2) = 4 * 2 ^ j := by rw [Int.pow_succ, Int.pow_succ]; omega
      have hn := Nat.div_add_mod n (2 ^ (j + 2))
      have hrlt : n % 2 ^ (j + 2) < 2 ^ (j + 2) := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hrem : (n : Int) % (4 * ((q : Int) + 1)) = ((n % 2 ^ (j + 2) : Nat) : Int) := by
        rw [hMi]; exact Int.natCast_emod n _
      have hpow : (2 : Nat) ^ (j + 2) = 2 * (2 * 2 ^ j) := by rw [Nat.pow_add]; omega
      have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
      have hQ : ((q : Int) + 1) = 2 ^ j := by exact_mod_cast hq
      have hE : 2 ^ (j + 2) * (n / 2 ^ (j + 2)) = 2 * (2 ^ (j + 1) * (n / 2 ^ (j + 2))) := by
        rw [Nat.pow_succ 2 (j + 1), Nat.mul_comm (2 ^ (j + 1)) 2, Nat.mul_assoc]
      have h4 : 4 ≤ 2 ^ (j + 2) := by rw [Nat.pow_add]; omega
      have h4u := Nat.mul_le_mul_right (n / 2 ^ (j + 2)) h4
      generalize hr : n % 2 ^ (j + 2) = r at *
      generalize hu : n / 2 ^ (j + 2) = u at *
      have hr1 : r % 2 = 1 := by omega
      have hu_lt : u < n := by omega
      have hpr : popc n = popc u + popc r := by
        rw [← hn]; exact popc_shift (j + 2) r u hrlt
      unfold wd
      rw [hrem]
      by_cases hc : (r : Int) ≥ 2 * ((q : Int) + 1)
      · -- high residue: the digit is r - M and the rest is 2^(j+1) (u + 1)
        rw [if_pos hc]
        have hsh : ((n : Int) - ((r : Int) - 4 * ((q : Int) + 1))) / 2 = 2 ^ (j + 1) * ((u + 1 : Nat) : Int) := by
          have hn' : (n : Int) = 2 ^ (j + 2) * u + r := by exact_mod_cast hn.symm
          have hQ : ((q : Int) + 1) = 2 ^ j := by exact_mod_cast hq
          have e : (n : Int) - ((r : Int) - 4 * ((q : Int) + 1)) = 2 * (2 ^ (j + 1) * ((u + 1 : Nat) : Int)) := by
            rw [hn', hQ]; push_cast
            rw [hP2, hP1, mul_l1, mul_l2]; omega
          rw [e]; omega
        have hne : (r : Int) - 4 * ((q : Int) + 1) ≠ 0 := by omega
        rw [wt_cons_ne _ _ hne, hsh, wt_wnaf_shift]
        have := ih (u + 1) (by omega)
        have h2 : 2 ≤ popc r := by
          have hsplit : r = 2 ^ (j + 1) * 1 + (r - 2 ^ (j + 1)) := by
            have : (2 * ((q : Int) + 1)) = ((2 ^ (j + 1) : Nat) : Int) := by
              have : ((q : Int) + 1) = 2 ^ j := by exact_mod_cast hq
              rw [this]; push_cast; rw [Int.pow_succ]; omega
            omega
          have hs : r - 2 ^ (j + 1) < 2 ^ (j + 1) := by omega
          have hso : (r - 2 ^ (j + 1)) % 2 = 1 := by
            rw [Nat.pow_succ]; omega
          rw [hsplit, popc_shift (j + 1) _ 1 hs]
          have := popc_pos_odd hso
          have p1 : popc 1 = 1 := by rw [popc_step' 1]; simp [popc_zero]
          omega
        have h3 := popc_succ_le u
        omega
      · rw [if_neg hc]
        have hsh : ((n : Int) - (r : Int)) / 2 = 2 ^ (j + 1) * (u : Int) := by
          have hn' : (n : Int) = 2 ^ (j + 2) * u + r := by exact_mod_cast hn.symm
          have e : (n : Int) - (r : Int) = 2 * (2 ^ (j + 1) * (u : Int)) := by
            rw [hn', hP2, hP1, mul_l1, mul_l3]; omega
          rw [e]; omega
        have hne : (r : Int) ≠ 0 := by omega
        rw [wt_cons_ne _ _ hne, hsh, wt_wnaf_shift]
        have := ih u hu_lt
        have := popc_pos_odd hr1
        omega

end SmcIrred.Arith
