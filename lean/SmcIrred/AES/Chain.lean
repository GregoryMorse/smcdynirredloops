module

public import SmcIrred.Spec.AES

public section

namespace SmcIrred.AES

/-! # Round-by-round evaluation of `encrypt` and `decrypt`

The kernel evaluates a whole cipher lazily and keeps every unevaluated intermediate term, which needs far more memory
than the Lean cap `-M768` leaves.  The theorems below reduce `encrypt`/`decrypt` to one equation per round between
explicit states; the example-vector modules prove each equation separately, so each kernel run is small. -/

theorem foldl_chain_aux {α β : Type} (f : α → β → α) (d : α) (e : β) (S : List α) :
    ∀ (l : List β) (s0 : α) (k : Nat), S.getD k d = s0 →
      (∀ i < l.length, f (S.getD (k + i) d) (l.getD i e) = S.getD (k + i + 1) d) →
      l.foldl f s0 = S.getD (k + l.length) d := by
  intro l
  induction l with
  | nil => intro s0 k h0 _; simpa using h0.symm
  | cons b l ih =>
    intro s0 k h0 hs
    have h1 := hs 0 (by simp)
    simp only [Nat.add_zero, List.getD_cons_zero] at h1
    rw [h0] at h1
    simp only [List.foldl_cons, List.length_cons]
    rw [h1]
    have := ih (S.getD (k + 1) d) (k + 1) rfl (fun i hi => by
      have := hs (i + 1) (by simp; omega)
      rw [List.getD_cons_succ] at this
      rw [show k + 1 + i = k + (i + 1) by omega]
      exact this)
    rw [this]
    congr 1
    omega

theorem foldl_chain {α β : Type} (f : α → β → α) (d : α) (e : β) (l : List β) (s0 : α) (S : List α)
    (h0 : S.getD 0 d = s0) (hs : ∀ i < l.length, f (S.getD i d) (l.getD i e) = S.getD (i + 1) d) :
    l.foldl f s0 = S.getD l.length d := by
  have := foldl_chain_aux f d e S l s0 0 h0 (by simpa using hs)
  simpa using this

@[expose] def encStep (rk : List (List Nat)) (i : Nat) (s : List Nat) : List Nat :=
  addRoundKey (mixColumns (shiftRows (subBytes s))) (roundKey rk (i + 1))

@[expose] def decStep (rk : List (List Nat)) (i : Nat) (s : List Nat) : List Nat :=
  invSubBytes (invShiftRows (invMixColumns (addRoundKey s (roundKey rk i))))

theorem getD_range {n i : Nat} (e : Nat) (h : i < n) : (List.range n).getD i e = i := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_decIdx {n i : Nat} (e : Nat) (h : i < n) :
    ((List.range n).reverse.map (· + 1)).getD i e = n - i := by
  simp [List.getD_eq_getElem?_getD, h]
  omega

/-- `encrypt` from one equation per round. -/
theorem encrypt_chain (Nr : Nat) (rk : List (List Nat)) (inp out : List Nat) (S : List (List Nat))
    (h0 : addRoundKey inp (roundKey rk 0) = S.getD 0 [])
    (hs : ∀ i < Nr - 1, encStep rk i (S.getD i []) = S.getD (i + 1) [])
    (hf : addRoundKey (shiftRows (subBytes (S.getD (Nr - 1) []))) (roundKey rk Nr) = out) :
    encrypt Nr rk inp = out := by
  unfold encrypt
  simp only
  rw [foldl_chain (fun s i => addRoundKey (mixColumns (shiftRows (subBytes s))) (roundKey rk (i + 1))) []
    0 (List.range (Nr - 1)) _ S h0.symm (fun i hi => by
      rw [List.length_range] at hi
      rw [getD_range 0 hi]
      exact hs i hi), List.length_range]
  exact hf

/-- `decrypt` from one equation per round (step `i` uses round key `Nr - 1 - i`). -/
theorem decrypt_chain (Nr : Nat) (rk : List (List Nat)) (inp out : List Nat) (S : List (List Nat))
    (h0 : invSubBytes (invShiftRows (addRoundKey inp (roundKey rk Nr))) = S.getD 0 [])
    (hs : ∀ i < Nr - 1, decStep rk (Nr - 1 - i) (S.getD i []) = S.getD (i + 1) [])
    (hf : addRoundKey (S.getD (Nr - 1) []) (roundKey rk 0) = out) :
    decrypt Nr rk inp = out := by
  unfold decrypt
  simp only
  rw [foldl_chain (fun s i => invSubBytes (invShiftRows (invMixColumns (addRoundKey s (roundKey rk i))))) []
    0 ((List.range (Nr - 1)).reverse.map (· + 1)) _ S h0.symm (fun i hi => by
      simp only [List.length_map, List.length_reverse, List.length_range] at hi
      rw [getD_decIdx 0 hi]
      exact hs i hi)]
  simp only [List.length_map, List.length_reverse, List.length_range]
  exact hf

end SmcIrred.AES
