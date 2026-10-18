module

public import SmcIrred.Spec.RBSD

public section

namespace SmcIrred.Arith

@[expose] def Dig (d : Int) : Prop := d = -1 ∨ d = 0 ∨ d = 1

/-- Recoded digit lists: digits in `{-1, 0, 1}`, and no digit repeats the nonzero digit just below it (`p` is the digit below
the first one). This is the shape `to_rbsd` produces (`rToRbsd_spec`) and `add_rbsd` needs. -/
@[expose] def Rec1 (p : Int) : List Int → Prop
  | [] => Dig p
  | d :: t => Dig p ∧ Dig d ∧ ¬ (d = p ∧ d ≠ 0) ∧ Rec1 d t

theorem dig_mem {d : Int} (hd : Dig d) : d = -1 ∨ d = 0 ∨ d = 1 := hd

theorem dig_zero : Dig 0 := Or.inr (Or.inl rfl)

/-! ### The adder -/

/-- The transfer of a digit pair: `-1` for `(-1, -1)`, `1` for `(1, 1)`, `0` otherwise. -/
@[expose] def rT (x y : Int) : Int := if x = -1 ∧ y = -1 then -1 else if x = 1 ∧ y = 1 then 1 else 0

/-- On every window of digits that the recoded form allows, the table lookup exists and computes
`x + y − 2 T(x, y) + T(x₁, y₁)`. -/
theorem rCell_spec : ∀ x ∈ ([-1, 0, 1] : List Int), ∀ y ∈ ([-1, 0, 1] : List Int), ∀ x1 ∈ ([-1, 0, 1] : List Int),
    ∀ y1 ∈ ([-1, 0, 1] : List Int), ¬ (x = x1 ∧ x ≠ 0) → ¬ (y = y1 ∧ y ≠ 0) →
      rCell x y x1 y1 = some (x + y - 2 * rT x y + rT x1 y1) := by decide

theorem rCell_good {x y x1 y1 : Int} (hx : Dig x) (hy : Dig y) (hx1 : Dig x1) (hy1 : Dig y1)
    (h1 : ¬ (x = x1 ∧ x ≠ 0)) (h2 : ¬ (y = y1 ∧ y ≠ 0)) :
    rCell x y x1 y1 = some (x + y - 2 * rT x y + rT x1 y1) := by
  have key := rCell_spec
  simp only [List.mem_cons, List.not_mem_nil, or_false] at key
  exact key x (dig_mem hx) y (dig_mem hy) x1 (dig_mem hx1) y1 (dig_mem hy1) h1 h2

theorem rT_zero : rT 0 0 = 0 := by decide

theorem bsdVal_head (a : List Int) : bsdVal a = a.headD 0 + 2 * bsdVal a.tail := by
  cases a <;> simp [bsdVal]

/-- The head, its relation to the digit below, and the rest of a recoded list. -/
theorem rec1_head {p : Int} {a : List Int} (h : Rec1 p a) :
    Dig p ∧ Dig (a.headD 0) ∧ ¬ (a.headD 0 = p ∧ a.headD 0 ≠ 0) ∧ Rec1 (a.headD 0) a.tail := by
  cases a with
  | nil => exact ⟨h, dig_zero, by simp, dig_zero⟩
  | cons d t => exact h

/-- Carry-free addition is correct for all lengths and never fails on recoded operands: for operands of at most `k` digits,
`k + 1` positions of the loop of `add_rbsd` produce digits (every table lookup exists) whose value is the sum of the values
of the operands plus the transfer carried in from the position below. -/
theorem rAddGo_val : ∀ (k : Nat) (a b : List Int) (x1 y1 : Int),
    Rec1 x1 a → Rec1 y1 b → a.length ≤ k → b.length ≤ k →
    ∃ out, rAddGo a b x1 y1 (k + 1) = some out ∧ bsdVal out = bsdVal a + bsdVal b + rT x1 y1 := by
  intro k
  induction k with
  | zero =>
    intro a b x1 y1 ha hb hla hlb
    have ea : a = [] := List.eq_nil_of_length_eq_zero (by omega)
    have eb : b = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst ea; subst eb
    obtain ⟨hx1, _, hn1, _⟩ := rec1_head ha
    obtain ⟨hy1, _, hn2, _⟩ := rec1_head hb
    have hc := rCell_good dig_zero dig_zero hx1 hy1 (by simp) (by simp)
    refine ⟨[0 + 0 - 2 * rT 0 0 + rT x1 y1], ?_, ?_⟩
    · simp only [rAddGo, List.headD_nil, List.tail_nil]
      rw [hc]
    · rw [rT_zero]; simp [bsdVal]
  | succ k ih =>
    intro a b x1 y1 ha hb hla hlb
    obtain ⟨hx1, hx, hn1, ha'⟩ := rec1_head ha
    obtain ⟨hy1, hy, hn2, hb'⟩ := rec1_head hb
    have hc := rCell_good hx hy hx1 hy1 hn1 hn2
    obtain ⟨t, ht, hv⟩ := ih a.tail b.tail (a.headD 0) (b.headD 0) ha' hb' (by simp; omega) (by simp; omega)
    refine ⟨(a.headD 0 + b.headD 0 - 2 * rT (a.headD 0) (b.headD 0) + rT x1 y1) :: t, ?_, ?_⟩
    · rw [rAddGo.eq_2, hc]
      simp only [ht]
    · rw [bsdVal_head a, bsdVal_head b]
      simp only [bsdVal]
      omega

theorem rec1_neg : ∀ (p : Int) (b : List Int), Rec1 p b → Rec1 (-p) (b.map (fun d => -d)) := by
  intro p b
  induction b generalizing p with
  | nil =>
    intro h
    show Dig (-p)
    unfold Rec1 Dig at h
    unfold Dig
    omega
  | cons d t ih =>
    intro h
    obtain ⟨hp, hd, hn, ht⟩ := h
    refine ⟨?_, ?_, ?_, ih d ht⟩
    · simp only [Dig] at hp ⊢; omega
    · simp only [Dig] at hd ⊢; omega
    · show ¬ (-d = -p ∧ -d ≠ 0)
      omega

theorem bsdVal_neg : ∀ b : List Int, bsdVal (b.map (fun d => -d)) = - bsdVal b := by
  intro b
  induction b with
  | nil => rfl
  | cons d t ih => simp only [List.map_cons, bsdVal, ih]; omega

/-- `add_rbsd` on recoded operands (`Rec1 0`) of any length returns digits whose value is the sum (`issub = false`) or the
difference (`issub = true`) of the values of the operands. -/
theorem rAdd_spec (a b : List Int) (issub : Bool) (ha : Rec1 0 a) (hb : Rec1 0 b) :
    ∃ out, rAdd a b issub = some out ∧ bsdVal out = bsdVal a + (if issub then - bsdVal b else bsdVal b) := by
  unfold rAdd
  cases issub
  · obtain ⟨out, ho, hv⟩ := rAddGo_val (max a.length b.length) a b 0 0 ha hb (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    refine ⟨out, ?_, ?_⟩
    · simpa using ho
    · rw [hv, rT_zero]; simp
  · have hb' := rec1_neg 0 b hb
    simp only [Int.neg_zero] at hb'
    obtain ⟨out, ho, hv⟩ := rAddGo_val (max a.length b.length) a (b.map (fun d => -d)) 0 0 ha hb' (Nat.le_max_left _ _)
      (by simpa using Nat.le_max_right a.length b.length)
    refine ⟨out, ?_, ?_⟩
    · simpa using ho
    · rw [hv, rT_zero, bsdVal_neg]; simp

/-! ### The recoding -/

/-- The transfer of the recoding, a function of a digit and the two digits below it. -/
@[expose] def rT3 (a b c : Int) : Int :=
  if a = -1 ∧ (b = -1 ∨ (b = 0 ∧ c = -1)) then -1
  else if a = 1 ∧ (b = 1 ∨ (b = 0 ∧ (c = 0 ∨ c = 1))) then 1 else 0

theorem rT3_zero (b c : Int) : rT3 0 b c = 0 := by simp [rT3]

/-- On every window of digits the recoding exists, produces a digit, and satisfies
`out = i + T₃(i₁, i₂, i₃) − 2 T₃(i, i₁, i₂)`. -/
theorem rToCell_spec : ∀ i ∈ ([-1, 0, 1] : List Int), ∀ i1 ∈ ([-1, 0, 1] : List Int), ∀ i2 ∈ ([-1, 0, 1] : List Int),
    ∀ i3 ∈ ([-1, 0, 1] : List Int), rToCell i i1 i2 i3 = some (i + rT3 i1 i2 i3 - 2 * rT3 i i1 i2) := by decide

/-- The digit the recoding gives (`0` where the lookup fails, which it does not on digits). -/
@[expose] def rc (i i1 i2 i3 : Int) : Int := (rToCell i i1 i2 i3).getD 0

/-- The recoded digits are digits, and two consecutive ones are never equal and nonzero. -/
theorem rc_spec : ∀ i ∈ ([-1, 0, 1] : List Int), ∀ i1 ∈ ([-1, 0, 1] : List Int), ∀ i2 ∈ ([-1, 0, 1] : List Int),
    ∀ i3 ∈ ([-1, 0, 1] : List Int), ∀ i4 ∈ ([-1, 0, 1] : List Int),
      (rc i i1 i2 i3 = -1 ∨ rc i i1 i2 i3 = 0 ∨ rc i i1 i2 i3 = 1) ∧
      ¬ (rc i i1 i2 i3 = rc i1 i2 i3 i4 ∧ rc i i1 i2 i3 ≠ 0) := by decide

theorem rc_zero : rc 0 0 0 0 = 0 := by decide

/-- The window a loop has seen at its end: the last digit and the two before it. -/
@[expose] def ft : List Int → Int × Int × Int → Int × Int × Int
  | [], w => w
  | i :: t, w => ft t (i, w.1, w.2.1)

theorem ft_append (l m : List Int) (w : Int × Int × Int) : ft (l ++ m) w = ft m (ft l w) := by
  induction l generalizing w with
  | nil => rfl
  | cons i t ih => exact ih _

theorem mem3 {d : Int} (hd : Dig d) : d ∈ ([-1, 0, 1] : List Int) := by
  rcases hd with rfl | rfl | rfl <;> decide

theorem rToGo_spec : ∀ (L : List Int) (i1 i2 i3 i4 : Int), (∀ d ∈ L, Dig d) → Dig i1 → Dig i2 → Dig i3 → Dig i4 →
    ∃ out, rToGo L i1 i2 i3 = some out ∧ Rec1 (rc i1 i2 i3 i4) out ∧
      bsdVal out + 2 ^ L.length * (rT3 (ft L (i1, i2, i3)).1 (ft L (i1, i2, i3)).2.1 (ft L (i1, i2, i3)).2.2) =
        bsdVal L + rT3 i1 i2 i3 := by
  intro L
  induction L with
  | nil =>
    intro i1 i2 i3 i4 _ h1 h2 h3 h4
    have hd := (rc_spec _ (mem3 h1) _ (mem3 h2) _ (mem3 h3) _ (mem3 h4) 0 (mem3 dig_zero)).1
    exact ⟨[], rfl, hd, by simp [ft, bsdVal]⟩
  | cons i t ih =>
    intro i1 i2 i3 i4 hL h1 h2 h3 h4
    have hi : Dig i := hL i List.mem_cons_self
    have hr := rToCell_spec i (mem3 hi) i1 (mem3 h1) i2 (mem3 h2) i3 (mem3 h3)
    obtain ⟨rest, hrest, hrec, hv⟩ := ih i i1 i2 i3 (fun d hd => hL d (List.mem_cons_of_mem _ hd)) hi h1 h2 h3
    have hrc : rc i i1 i2 i3 = i + rT3 i1 i2 i3 - 2 * rT3 i i1 i2 := by simp [rc, hr]
    have hs := rc_spec i (mem3 hi) i1 (mem3 h1) i2 (mem3 h2) i3 (mem3 h3) i4 (mem3 h4)
    have hp := (rc_spec i1 (mem3 h1) i2 (mem3 h2) i3 (mem3 h3) i4 (mem3 h4) 0 (mem3 dig_zero)).1
    refine ⟨(i + rT3 i1 i2 i3 - 2 * rT3 i i1 i2) :: rest, ?_, ?_, ?_⟩
    · simp only [rToGo, hr, hrest]
    · rw [← hrc]
      exact ⟨hp, hs.1, hs.2, hrec⟩
    · have e : (2 : Int) ^ (t.length + 1) * rT3 (ft (i :: t) (i1, i2, i3)).1 (ft (i :: t) (i1, i2, i3)).2.1
          (ft (i :: t) (i1, i2, i3)).2.2 = 2 * (2 ^ t.length * rT3 (ft t (i, i1, i2)).1 (ft t (i, i1, i2)).2.1
          (ft t (i, i1, i2)).2.2) := by
        show _ * rT3 (ft t (i, i1, i2)).1 (ft t (i, i1, i2)).2.1 (ft t (i, i1, i2)).2.2 = _
        rw [Int.pow_succ, Int.mul_comm ((2:Int) ^ t.length) 2, Int.mul_assoc]
      simp only [List.length_cons, bsdVal]
      rw [e]
      omega

theorem bsdVal_append_zero (l : List Int) : bsdVal (l ++ [0]) = bsdVal l := by
  induction l with
  | nil => rfl
  | cons d t ih => simp only [List.cons_append, bsdVal, ih]

/-- `to_rbsd` of any signed-digit list produces recoded digits (`Rec1 0`) of the same value. -/
theorem rToRbsd_spec (bsd : List Int) (h : ∀ d ∈ bsd, Dig d) :
    ∃ out, rToRbsd bsd = some out ∧ Rec1 0 out ∧ bsdVal out = bsdVal bsd := by
  have hL : ∀ d ∈ bsd ++ [0], Dig d := by
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact h d hd
    · simp at hd; subst hd; exact dig_zero
  obtain ⟨out, ho, hr, hv⟩ := rToGo_spec (bsd ++ [0]) 0 0 0 0 hL dig_zero dig_zero dig_zero dig_zero
  rw [rc_zero] at hr
  refine ⟨out, ho, hr, ?_⟩
  have hf : ft (bsd ++ [0]) (0, 0, 0) = (0, (ft bsd (0, 0, 0)).1, (ft bsd (0, 0, 0)).2.1) := by
    rw [ft_append]; rfl
  rw [hf, rT3_zero, bsdVal_append_zero] at hv
  rw [rT3_zero] at hv
  simpa using hv

/-- The subtraction variant of the bound: for `-N ≤ T < N` (the difference of two residues) the result is the residue of `T` in
`[0, N)`: it differs from `T` by `0` or `N` and lies in range. -/
theorem boundSub_spec (t N : Int) (h1 : -N ≤ t) (h2 : t < N) :
    0 ≤ boundSub t N ∧ boundSub t N < N ∧ (boundSub t N = t ∨ boundSub t N = t + N) := by
  unfold boundSub
  split <;> omega

end SmcIrred.Arith
