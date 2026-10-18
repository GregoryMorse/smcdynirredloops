module

public import SmcIrred.Spec.Gates

public section

namespace SmcIrred

theorem foldl_ne_aux (xs : List Bool) :
    ∀ a : Bool, xs.foldl (fun a b => a != b) a = (a != xs.foldl (fun a b => a != b) false) := by
  induction xs with
  | nil => intro a; simp
  | cons b t ih =>
    intro a
    simp only [List.foldl_cons]
    rw [ih (a != b), ih (false != b)]
    generalize List.foldl (fun a b => a != b) false t = z
    cases a <;> cases b <;> cases z <;> rfl

theorem foldl_ne (xs : List Bool) : ∀ a : Bool, xs.foldl (fun a b => a != b) a = (a != xorL xs) :=
  foldl_ne_aux xs

theorem xorL_nil : xorL [] = false := rfl
theorem xorL_cons (b : Bool) (t : List Bool) : xorL (b :: t) = (b != xorL t) := by
  show List.foldl (fun a b => a != b) (false != b) t = _
  rw [foldl_ne_aux t (false != b)]
  show _ = (b != List.foldl (fun a b => a != b) false t)
  cases b <;> cases List.foldl (fun a b => a != b) false t <;> rfl

theorem xorL_append_singleton (a : List Bool) (y : Bool) : xorL (a ++ [y]) = (xorL a != y) := by
  unfold xorL
  rw [List.foldl_append]
  rfl

theorem andL_cons (b : Bool) (t : List Bool) : andL (b :: t) = (b && andL t) := by
  simp [andL]
theorem orL_cons (b : Bool) (t : List Bool) : orL (b :: t) = (b || orL t) := by
  simp [orL]

/-- The nonempty fold of a binary operation. -/
@[expose] def fb (f : Bool → Bool → Bool) : List Bool → Bool
  | [] => false
  | x :: xs => xs.foldl f x

theorem foldl_assoc (f : Bool → Bool → Bool) (h : ∀ a b c, f (f a b) c = f a (f b c)) (xs : List Bool) :
    ∀ a b, xs.foldl f (f a b) = f a (xs.foldl f b) := by
  induction xs with
  | nil => intro a b; rfl
  | cons y t ih => intro a b; simp only [List.foldl_cons]; rw [h a b y, ih]

theorem fb_append (f : Bool → Bool → Bool) (h : ∀ a b c, f (f a b) c = f a (f b c)) (l1 l2 : List Bool)
    (h1 : l1 ≠ []) (h2 : l2 ≠ []) : fb f (l1 ++ l2) = f (fb f l1) (fb f l2) := by
  cases l1 with
  | nil => exact absurd rfl h1
  | cons x xs =>
    cases l2 with
    | nil => exact absurd rfl h2
    | cons y ys =>
      simp only [fb, List.cons_append, List.foldl_append, List.foldl_cons]
      rw [foldl_assoc f h ys (xs.foldl f x) y]

theorem fb_and (l : List Bool) (h : l ≠ []) : fb (fun a b => a && b) l = andL l := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs =>
    simp only [fb, andL_cons]
    have : ∀ (xs : List Bool) (a : Bool), xs.foldl (fun a b => a && b) a = (a && andL xs) := by
      intro xs
      induction xs with
      | nil => intro a; simp [andL]
      | cons y t ih =>
        intro a; simp only [List.foldl_cons, andL_cons]; rw [ih]
        cases a <;> cases y <;> cases andL t <;> rfl
    exact this xs x

theorem fb_or (l : List Bool) (h : l ≠ []) : fb (fun a b => a || b) l = orL l := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs =>
    simp only [fb, orL_cons]
    have : ∀ (xs : List Bool) (a : Bool), xs.foldl (fun a b => a || b) a = (a || orL xs) := by
      intro xs
      induction xs with
      | nil => intro a; simp [orL]
      | cons y t ih =>
        intro a; simp only [List.foldl_cons, orL_cons]; rw [ih]
        cases a <;> cases y <;> cases orL t <;> rfl
    exact this xs x

theorem fb_xor (l : List Bool) (h : l ≠ []) : fb (fun a b => a != b) l = xorL l := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs =>
    simp only [fb]
    rw [foldl_ne, xorL_cons]

theorem chain_eval (o : Op2) (t : GT) (xs : List Bool) :
    (xs.foldl (fun t y => GT.node o t (.leaf y)) t).eval = xs.foldl o.ev t.eval := by
  induction xs generalizing t with
  | nil => rfl
  | cons y s ih => simp only [List.foldl_cons]; rw [ih]; rfl

theorem chain_gates (o : Op2) (t : GT) (xs : List Bool) :
    (xs.foldl (fun t y => GT.node o t (.leaf y)) t).gates = t.gates + xs.length := by
  induction xs generalizing t with
  | nil => rfl
  | cons y s ih =>
    simp only [List.foldl_cons, List.length_cons]; rw [ih]; simp [GT.gates]; omega

/-- A chain of `|X| - 1` two-input gates computes the multi-input gate (AND, OR, XOR). -/
theorem chain_and (x : Bool) (xs : List Bool) : (chainOf .and (x :: xs)).eval = andL (x :: xs) := by
  rw [← fb_and _ (by simp)]; simp only [chainOf, chain_eval, fb]; rfl
theorem chain_or (x : Bool) (xs : List Bool) : (chainOf .or (x :: xs)).eval = orL (x :: xs) := by
  rw [← fb_or _ (by simp)]; simp only [chainOf, chain_eval, fb]; rfl
theorem chain_xor (x : Bool) (xs : List Bool) : (chainOf .xor (x :: xs)).eval = xorL (x :: xs) := by
  rw [← fb_xor _ (by simp)]; simp only [chainOf, chain_eval, fb]; rfl
theorem chain_gates_eq (o : Op2) (x : Bool) (xs : List Bool) :
    (chainOf o (x :: xs)).gates = (x :: xs).length - 1 := by
  simp only [chainOf, chain_gates]; simp [GT.gates]

theorem tree_split (x y : Bool) (rest : List Bool) :
    1 ≤ (rest.length + 3) / 2 ∧
    ((x :: y :: rest).take ((rest.length + 3) / 2)).length = (rest.length + 3) / 2 ∧
    ((x :: y :: rest).drop ((rest.length + 3) / 2)).length = rest.length + 2 - (rest.length + 3) / 2 ∧
    (x :: y :: rest).take ((rest.length + 3) / 2) ≠ [] ∧
    (x :: y :: rest).drop ((rest.length + 3) / 2) ≠ [] := by
  have hl1 : ((x :: y :: rest).take ((rest.length + 3) / 2)).length = (rest.length + 3) / 2 := by
    simp only [List.length_take, List.length_cons]; omega
  have hl2 : ((x :: y :: rest).drop ((rest.length + 3) / 2)).length = rest.length + 2 - (rest.length + 3) / 2 := by
    simp only [List.length_drop, List.length_cons]
  refine ⟨by omega, hl1, hl2, ?_, ?_⟩
  · intro e; rw [e] at hl1; simp at hl1; omega
  · intro e; rw [e] at hl2; simp at hl2; omega

theorem fb_op_assoc (o : Op2) (h : ∀ a b c, o.ev (o.ev a b) c = o.ev a (o.ev b c)) :
    ∀ n (l : List Bool), l.length = n → l ≠ [] → (treeOf o l).eval = fb o.ev l := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro l hn hne
    match l, hn, hne with
    | [x], _, _ => simp [treeOf, GT.eval, fb]
    | x :: y :: rest, hn, _ =>
      rw [treeOf]
      obtain ⟨_, hl1, hl2, hne1, hne2⟩ := tree_split x y rest
      simp only [GT.eval]
      rw [ih _ (by simp only [List.length_cons] at hn; omega) _ hl1 hne1,
        ih _ (by simp only [List.length_cons] at hn; omega) _ hl2 hne2]
      have := fb_append o.ev h _ _ hne1 hne2
      rw [List.take_append_drop] at this
      exact this.symm

theorem op_and_assoc : ∀ a b c : Bool, Op2.and.ev (Op2.and.ev a b) c = Op2.and.ev a (Op2.and.ev b c) := by
  intro a b c; cases a <;> cases b <;> cases c <;> rfl
theorem op_or_assoc : ∀ a b c : Bool, Op2.or.ev (Op2.or.ev a b) c = Op2.or.ev a (Op2.or.ev b c) := by
  intro a b c; cases a <;> cases b <;> cases c <;> rfl
theorem op_xor_assoc : ∀ a b c : Bool, Op2.xor.ev (Op2.xor.ev a b) c = Op2.xor.ev a (Op2.xor.ev b c) := by
  intro a b c; cases a <;> cases b <;> cases c <;> rfl

/-- The balanced tree of two-input gates computes the multi-input gate. -/
theorem tree_and (l : List Bool) (h : l ≠ []) : (treeOf .and l).eval = andL l := by
  rw [fb_op_assoc .and op_and_assoc _ l rfl h]; exact fb_and l h
theorem tree_or (l : List Bool) (h : l ≠ []) : (treeOf .or l).eval = orL l := by
  rw [fb_op_assoc .or op_or_assoc _ l rfl h]; exact fb_or l h
theorem tree_xor (l : List Bool) (h : l ≠ []) : (treeOf .xor l).eval = xorL l := by
  rw [fb_op_assoc .xor op_xor_assoc _ l rfl h]; exact fb_xor l h

theorem tree_gates (o : Op2) :
    ∀ n (l : List Bool), l.length = n → l ≠ [] → (treeOf o l).gates = l.length - 1 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro l hn hne
    match l, hn, hne with
    | [x], _, _ => simp [treeOf, GT.gates]
    | x :: y :: rest, hn, _ =>
      rw [treeOf]
      obtain ⟨_, hl1, hl2, hne1, hne2⟩ := tree_split x y rest
      simp only [GT.gates]
      rw [ih _ (by simp only [List.length_cons] at hn; omega) _ hl1 hne1,
        ih _ (by simp only [List.length_cons] at hn; omega) _ hl2 hne2, hl1, hl2]
      simp only [List.length_cons]
      omega

theorem treeDepth_succ (n : Nat) (h : 2 ≤ n) : treeDepth n = treeDepth ((n + 1) / 2) + 1 := by
  rw [treeDepth]
  have : ¬ n ≤ 1 := by omega
  simp [this]

theorem treeDepth_le_one (n : Nat) (h : n ≤ 1) : treeDepth n = 0 := by
  rw [treeDepth]; simp [h]

theorem treeDepth_mono : ∀ m n, n ≤ m → treeDepth n ≤ treeDepth m := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro n hnm
    by_cases hn : n ≤ 1
    · rw [treeDepth_le_one n hn]; exact Nat.zero_le _
    · have hm : 2 ≤ m := by omega
      rw [treeDepth_succ n (by omega), treeDepth_succ m hm]
      have := ih ((m + 1) / 2) (by omega) ((n + 1) / 2) (by omega)
      omega

/-- The balanced tree has depth `treeDepth n`. -/
theorem tree_depth (o : Op2) :
    ∀ n (l : List Bool), l.length = n → l ≠ [] → (treeOf o l).depth = treeDepth l.length := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro l hn hne
    match l, hn, hne with
    | [x], _, _ => simp [treeOf, GT.depth, treeDepth_le_one]
    | x :: y :: rest, hn, _ =>
      rw [treeOf]
      obtain ⟨_, hl1, hl2, hne1, hne2⟩ := tree_split x y rest
      simp only [GT.depth]
      rw [ih _ (by simp only [List.length_cons] at hn; omega) _ hl1 hne1,
        ih _ (by simp only [List.length_cons] at hn; omega) _ hl2 hne2, hl1, hl2]
      have hmono := treeDepth_mono ((rest.length + 3) / 2) (rest.length + 2 - (rest.length + 3) / 2) (by omega)
      have hs := treeDepth_succ (x :: y :: rest).length (by simp)
      simp only [List.length_cons] at hs ⊢
      have e : (rest.length + 1 + 1 + 1) / 2 = (rest.length + 3) / 2 := by omega
      rw [e] at hs
      have e2 : rest.length + 1 + 1 = rest.length + 2 := rfl
      rw [e2, hs]
      omega

/-- `treeDepth n` is the least `k` with `n ≤ 2^k`, i.e. `⌈log₂ n⌉`. -/
theorem treeDepth_spec : ∀ n, n ≤ 2 ^ treeDepth n ∧ (treeDepth n = 0 ∨ 2 ^ (treeDepth n - 1) < n) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hn : n ≤ 1
    · rw [treeDepth_le_one n hn]
      refine ⟨?_, Or.inl rfl⟩
      simp; omega
    · have hn2 : 2 ≤ n := by omega
      rw [treeDepth_succ n hn2]
      obtain ⟨h1, h2⟩ := ih ((n + 1) / 2) (by omega)
      refine ⟨?_, Or.inr ?_⟩
      · rw [Nat.pow_succ]; omega
      · simp only [Nat.add_sub_cancel]
        rcases h2 with h2 | h2
        · rw [h2]; simp; omega
        · have hp : 0 < treeDepth ((n + 1) / 2) := by
            apply Classical.byContradiction; intro hz
            have hz' : treeDepth ((n + 1) / 2) = 0 := by omega
            have hle : (n + 1) / 2 ≤ 1 := by
              apply Classical.byContradiction; intro hc
              have := treeDepth_succ ((n + 1) / 2) (by omega)
              omega
            rw [hz'] at h2; simp at h2; omega
          have : 2 ^ treeDepth ((n + 1) / 2) = 2 * 2 ^ (treeDepth ((n + 1) / 2) - 1) := by
            rw [← Nat.pow_succ']; congr 1; omega
          omega

/-- Multi-input XNOR (`|X| = a.length + 1 ≥ 2`) as an XOR chain followed by one final XNOR gate. -/
@[expose] def xnorChain (a : List Bool) (y : Bool) : GT :=
  .node .xnor (chainOf .xor a) (.leaf y)

theorem xnorChain_eval (x : Bool) (xs : List Bool) (y : Bool) :
    (xnorChain (x :: xs) y).eval = xnorL (x :: xs ++ [y]) := by
  unfold xnorChain xnorL
  rw [xorL_append_singleton, ← chain_xor x xs]
  simp only [GT.eval, Op2.ev]
  cases (chainOf .xor (x :: xs)).eval <;> cases y <;> rfl

theorem xnorChain_gates (x : Bool) (xs : List Bool) (y : Bool) :
    (xnorChain (x :: xs) y).gates = (x :: xs ++ [y]).length - 1 := by
  unfold xnorChain
  simp only [GT.gates, chain_gates_eq, GT.gates]
  simp

theorem foldl_xnor (xs : List Bool) :
    ∀ a : Bool, xs.foldl (fun a b => a == b) a = ((a != xorL xs) != decide (xs.length % 2 = 1)) := by
  induction xs with
  | nil => intro a; simp [xorL]
  | cons b t ih =>
    intro a
    simp only [List.foldl_cons]
    rw [ih, xorL_cons, List.length_cons]
    by_cases hp : t.length % 2 = 1
    · have h2 : ¬ ((t.length + 1) % 2 = 1) := by omega
      simp only [hp, h2, decide_true, decide_false]
      cases a <;> cases b <;> cases xorL t <;> rfl
    · have h2 : (t.length + 1) % 2 = 1 := by omega
      simp only [hp, h2, decide_true, decide_false]
      cases a <;> cases b <;> cases xorL t <;> rfl

/-- A pure XNOR chain computes XOR when the number of inputs is odd (and XNOR when it is even). -/
theorem xnor_chain_pure (x : Bool) (xs : List Bool) :
    (chainOf .xnor (x :: xs)).eval = if (x :: xs).length % 2 = 1 then xorL (x :: xs) else xnorL (x :: xs) := by
  simp only [chainOf, chain_eval, GT.eval]
  have : xs.foldl Op2.xnor.ev x = xs.foldl (fun a b => a == b) x := rfl
  rw [this, foldl_xnor, List.length_cons, xorL_cons]
  unfold xnorL
  rw [xorL_cons]
  by_cases hp : xs.length % 2 = 1
  · have h2 : ¬ ((xs.length + 1) % 2 = 1) := by omega
    simp only [hp, h2, decide_true, decide_false, ite_false]
    cases x <;> cases xorL xs <;> rfl
  · have h2 : (xs.length + 1) % 2 = 1 := by omega
    simp only [hp, h2, decide_true, decide_false, ite_true]
    cases x <;> cases xorL xs <;> rfl

theorem nand_single (x : Bool) : nandL [x] = !x := by cases x <;> rfl
theorem nor_single (x : Bool) : norL [x] = !x := by cases x <;> rfl
theorem xnor_single (x : Bool) : xnorL [x] = !x := by cases x <;> rfl

end SmcIrred
