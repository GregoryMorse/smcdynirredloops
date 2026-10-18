module

public section

namespace SmcIrred

/-!
# Multi-input gates, their decomposition, selection (Section 4, Definitions 1 and 2)

`andL`, `orL`, `xorL`, `xnorL` are the multi-input combinators of Definition 1 (XNOR is the complement of XOR). A
decomposition into two-input gates is a tree `GT`; the sequential form is a chain, the balanced form halves the list.
-/

@[expose] def andL (l : List Bool) : Bool := l.all id
@[expose] def orL (l : List Bool) : Bool := l.any id
@[expose] def xorL (l : List Bool) : Bool := l.foldl (fun a b => a != b) false
@[expose] def xnorL (l : List Bool) : Bool := !xorL l
@[expose] def nandL (l : List Bool) : Bool := !andL l
@[expose] def norL (l : List Bool) : Bool := !orL l

inductive Op2 | and | or | xor | xnor | nand | nor

@[expose] def Op2.ev : Op2 → Bool → Bool → Bool
  | .and => fun a b => a && b
  | .or => fun a b => a || b
  | .xor => fun a b => a != b
  | .xnor => fun a b => a == b
  | .nand => fun a b => !(a && b)
  | .nor => fun a b => !(a || b)

/-- A circuit of two-input gates over the leaves. -/
inductive GT
  | leaf (x : Bool)
  | node (o : Op2) (l r : GT)

@[expose] def GT.eval : GT → Bool
  | .leaf x => x
  | .node o l r => o.ev l.eval r.eval

@[expose] def GT.gates : GT → Nat
  | .leaf _ => 0
  | .node _ l r => l.gates + r.gates + 1

@[expose] def GT.depth : GT → Nat
  | .leaf _ => 0
  | .node _ l r => max l.depth r.depth + 1

/-- The sequential (left-to-right) decomposition. -/
@[expose] def chainOf (o : Op2) : List Bool → GT
  | [] => .leaf false
  | x :: xs => xs.foldl (fun t y => .node o t (.leaf y)) (.leaf x)

/-- The balanced decomposition: the left half is the larger one. -/
@[expose] def treeOf (o : Op2) : List Bool → GT
  | [] => .leaf false
  | [x] => .leaf x
  | x :: y :: rest =>
    .node o (treeOf o ((x :: y :: rest).take ((rest.length + 3) / 2)))
            (treeOf o ((x :: y :: rest).drop ((rest.length + 3) / 2)))
termination_by l => l.length
decreasing_by all_goals (simp only [List.length_take, List.length_drop, List.length_cons]; omega)

/-- The depth `⌈log₂ n⌉` of the balanced decomposition of `n` inputs. -/
@[expose] def treeDepth (n : Nat) : Nat :=
  if h : n ≤ 1 then 0 else treeDepth ((n + 1) / 2) + 1
termination_by n
decreasing_by omega

/-- Selection (Definition 2): a sum (XOR) of products of ordered pairs (selector, value). -/
@[expose] def selL (l : List (Bool × Bool)) : Bool := xorL (l.map fun p => p.1 && p.2)
/-- The same with OR as the sum (the paper's remark that XOR is replaceable by OR). -/
@[expose] def selOrL (l : List (Bool × Bool)) : Bool := orL (l.map fun p => p.1 && p.2)
/-- Binary selection `s ∧ x0 ⊕ ¬s ∧ x1`. -/
@[expose] def bsel (s x0 x1 : Bool) : Bool := (s && x0) != (!s && x1)

/-- Formulas over a two-input gate `g` (variables are numbered). -/
inductive F2 (g : Bool → Bool → Bool)
  | var (i : Nat)
  | gate (a b : F2 g)

@[expose] def F2.eval {g : Bool → Bool → Bool} (a : Nat → Bool) : F2 g → Bool
  | .var i => a i
  | .gate x y => g (x.eval a) (y.eval a)

@[expose] def nandG : Bool → Bool → Bool := fun a b => !(a && b)
@[expose] def norG : Bool → Bool → Bool := fun a b => !(a || b)

end SmcIrred
