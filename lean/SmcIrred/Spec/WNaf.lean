module

public import SmcIrred.Spec.Recode

public section

namespace SmcIrred.Arith

/-! # Windowed non-adjacent form (paper §4.2, "NAF and MOF and their windowed forms", C58, G31)

For the window parameter `q` (modulus `4 (q + 1)`, digits of absolute value below `2 (q + 1)`; with `q + 1 = 2^j` this is
the `w`-NAF with `w = j + 2`): an odd value gets the odd digit congruent to it modulo `4 (q + 1)` of least absolute value,
after which the next `j + 1` digits are zero. -/

/-- The digit chosen for an odd `k`: the representative of `k` modulo `4 (q + 1)` in `(-2 (q + 1), 2 (q + 1))`. -/
@[expose] def wd (q : Nat) (k : Int) : Int :=
  if k % (4 * ((q : Int) + 1)) ≥ 2 * ((q : Int) + 1) then k % (4 * ((q : Int) + 1)) - 4 * ((q : Int) + 1)
  else k % (4 * ((q : Int) + 1))

/-- The digit of an odd value: odd, below `2 (q + 1)` in absolute value, and `k = d + 4 (q + 1) u`. -/
theorem wd_core (q : Nat) (k : Int) (hk : k % 2 = 1) :
    ∃ N u : Int, N = ((q : Int) + 1) * u ∧ k = wd q k + 4 * N ∧ -(2 * ((q : Int) + 1)) < wd q k ∧
      wd q k < 2 * ((q : Int) + 1) ∧ wd q k % 2 = 1 := by
  have hp : (0 : Int) < 4 * ((q : Int) + 1) := by omega
  have h1 := Int.emod_nonneg k (Int.ne_of_gt hp)
  have h2 := Int.emod_lt_of_pos k hp
  have h3 := Int.mul_ediv_add_emod k (4 * ((q : Int) + 1))
  generalize hr : k % (4 * ((q : Int) + 1)) = r at *
  generalize hu : k / (4 * ((q : Int) + 1)) = u at *
  have hN : 4 * ((q : Int) + 1) * u = 4 * (((q : Int) + 1) * u) := by rw [Int.mul_assoc]
  unfold wd
  rw [hr]
  by_cases hc : r ≥ 2 * ((q : Int) + 1)
  · rw [if_pos hc]
    have hN1 : ((q : Int) + 1) * (u + 1) = ((q : Int) + 1) * u + ((q : Int) + 1) := by
      rw [Int.mul_add, Int.mul_one]
    exact ⟨((q : Int) + 1) * (u + 1), u + 1, rfl, by omega, by omega, by omega, by omega⟩
  · rw [if_neg hc]
    exact ⟨((q : Int) + 1) * u, u, rfl, by omega, by omega, by omega, by omega⟩

theorem wd_dec (q : Nat) (k : Int) (_h0 : k ≠ 0) (hk : k % 2 ≠ 0) :
    ((k - wd q k) / 2).natAbs < k.natAbs := by
  obtain ⟨N, u, hN, hk2, hl, hu, ho⟩ := wd_core q k (by omega)
  have hq : (0 : Int) ≤ (q : Int) + 1 := by omega
  by_cases hu0 : u = 0
  · subst hu0; rw [Int.mul_zero] at hN; omega
  · by_cases hpos : 1 ≤ u
    · have := Int.mul_le_mul_of_nonneg_left hpos hq
      rw [Int.mul_one] at this; omega
    · have := Int.mul_le_mul_of_nonneg_left (show u ≤ -1 by omega) hq
      rw [Int.mul_neg, Int.mul_one] at this; omega

/-- The windowed non-adjacent form of an integer, least significant digit first. -/
@[expose] def wnaf (q : Nat) (k : Int) : List Int :=
  if h : k = 0 then [] else
  if h2 : k % 2 = 0 then 0 :: wnaf q (k / 2)
  else wd q k :: wnaf q ((k - wd q k) / 2)
termination_by k.natAbs
decreasing_by
  · omega
  · exact wd_dec q k h h2

end SmcIrred.Arith
