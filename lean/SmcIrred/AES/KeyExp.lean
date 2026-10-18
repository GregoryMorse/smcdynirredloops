module

public import SmcIrred.Spec.AES

public section

namespace SmcIrred.AES

/-! Key expansion uses only XOR, S-box lookup and round-constant bytes (C50). The expansion `keyExp` is
written once over an abstract byte algebra `Alg`; it commutes with every homomorphism of algebras, so the
symbolic run over variables, evaluated at a concrete key, equals the numeric expansion. -/

structure AlgHom {α β : Type} (A : Alg α) (B : Alg β) (h : α → β) : Prop where
  zero : h A.zero = B.zero
  xor : ∀ a b, h (A.xor a b) = B.xor (h a) (h b)
  sb : ∀ a, h (A.sb a) = B.sb (h a)
  rc : ∀ j, h (A.rc j) = B.rc j

section Hom
variable {α β : Type} {A : Alg α} {B : Alg β} {h : α → β}

theorem zW_map (H : AlgHom A B h) : zW B = (zW A).map h := by
  simp [zW, H.zero]

theorem wxor_map (H : AlgHom A B h) (u v : List α) : wxor B (u.map h) (v.map h) = (wxor A u v).map h := by
  induction u generalizing v with
  | nil => simp [wxor]
  | cons a t ih =>
    cases v with
    | nil => simp [wxor]
    | cons b v =>
      have := ih v
      simp only [wxor, List.map_cons, List.zipWith_cons_cons] at this ⊢
      rw [this, H.xor]

theorem rotW_map (w : List α) : rotW (w.map h) = (rotW w).map h := by
  match w with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | [_, _, _, _] => rfl
  | _ :: _ :: _ :: _ :: _ :: _ => rfl

theorem subW_map (H : AlgHom A B h) (w : List α) : subW B (w.map h) = (subW A w).map h := by
  simp [subW, List.map_map, Function.comp_def, H.sb]

theorem rcW_map (H : AlgHom A B h) (j : Nat) (w : List α) : rcW B j (w.map h) = (rcW A j w).map h := by
  cases w with
  | nil => rfl
  | cons a t => simp [rcW, H.xor, H.rc]

theorem getD_wmap (H : AlgHom A B h) (ws : List (List α)) (i : Nat) :
    (ws.map (·.map h)).getD i (zW B) = (ws.getD i (zW A)).map h := by
  rw [zW_map H]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[i]? <;> simp

theorem expandStep_map (H : AlgHom A B h) (Nk : Nat) (ws : List (List α)) :
    expandStep B Nk (ws.map (·.map h)) = (expandStep A Nk ws).map (·.map h) := by
  unfold expandStep
  simp only [List.length_map, getD_wmap H, List.map_append]
  by_cases c0 : ws.length % Nk = 0
  · simp only [if_pos c0, rotW_map, subW_map H, rcW_map H, wxor_map H]
    rfl
  · by_cases c1 : 6 < Nk ∧ ws.length % Nk = 4
    · simp only [if_neg c0, if_pos c1, subW_map H, wxor_map H]
      rfl
    · simp only [if_neg c0, if_neg c1, wxor_map H]
      rfl

theorem expandN_map (H : AlgHom A B h) (Nk : Nat) :
    ∀ (n : Nat) (ws : List (List α)), expandN B Nk n (ws.map (·.map h)) = (expandN A Nk n ws).map (·.map h) := by
  intro n
  induction n with
  | zero => intro ws; rfl
  | succ n ih => intro ws; simp only [expandN]; rw [expandStep_map H, ih]

theorem getD_map (H : AlgHom A B h) (key : List α) (i : Nat) :
    (key.map h).getD i B.zero = h (key.getD i A.zero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases key[i]? <;> simp [H.zero]

/-- The key expansion commutes with algebra homomorphisms. -/
theorem keyExp_map (H : AlgHom A B h) (Nk Nr : Nat) (key : List α) :
    keyExp B Nk Nr (key.map h) = (keyExp A Nk Nr key).map (·.map h) := by
  unfold keyExp
  rw [← expandN_map H]
  congr 1
  simp only [List.map_map, Function.comp_def, getD_map H]

end Hom

/-- Symbolic bytes: the only byte operations key expansion may use. -/
inductive BExpr where
  | zero : BExpr
  | var : Nat → BExpr
  | xor : BExpr → BExpr → BExpr
  | sb : BExpr → BExpr
  | rc : Nat → BExpr

@[expose] def exprAlg : Alg BExpr := ⟨.zero, .xor, .sb, .rc⟩

@[expose] def BExpr.eval (env : Nat → Nat) : BExpr → Nat
  | .zero => 0
  | .var i => env i
  | .xor a b => a.eval env ^^^ b.eval env
  | .sb a => sbox (a.eval env)
  | .rc j => rconTable.getD j 0

theorem eval_hom (env : Nat → Nat) : AlgHom exprAlg natAlg (BExpr.eval env) :=
  ⟨rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The symbolic expansion of the `4 * Nk` key bytes, evaluated at any assignment `env` of the key bytes,
equals the numeric expansion of that key. -/
theorem keyExp_symbolic (env : Nat → Nat) (Nk Nr : Nat) :
    (keyExp exprAlg Nk Nr ((List.range (4 * Nk)).map BExpr.var)).map (·.map (BExpr.eval env)) =
      keyExp natAlg Nk Nr ((List.range (4 * Nk)).map env) := by
  rw [← keyExp_map (eval_hom env)]
  simp only [List.map_map, Function.comp_def, BExpr.eval]

end SmcIrred.AES
