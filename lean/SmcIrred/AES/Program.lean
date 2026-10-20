module

public import SmcIrred.AES.BitVal

public section

namespace SmcIrred

open AES

/-! # The semantics of the AES program equals the FIPS-197 specification (R13)

Every stage expression of `Spec.AESProg` has, on a packed state of 16 bytes below 256, the packed result of the
corresponding byte-level function of `Spec.AES`:
`arkE` is `addRoundKey`, `subShiftE` is `shiftRows ∘ subBytes`, `mixE` is `addRoundKey ∘ mixColumns`. -/

/-- A state: 16 bytes, each below 256. -/
@[expose] def StOK (s : List Nat) : Prop := s.length = 16 ∧ ∀ x ∈ s, x < 256

theorem stOK_map16 (g : Nat → Nat) (h : ∀ i, i < 16 → g i < 256) : StOK ((List.range 16).map g) := by
  refine ⟨by simp, ?_⟩
  intro x hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact h i hi

theorem getD_lt256_all {s : List Nat} (hs : ∀ x ∈ s, x < 256) (j : Nat) : s.getD j 0 < 256 := by
  by_cases hj : j < s.length
  · have : s.getD j 0 = s[j] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rw [this]
    exact hs _ (List.getElem_mem hj)
  · have : s.getD j 0 = 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.not_lt.1 hj)]
    rw [this]; omega

theorem getD_lt256 {s : List Nat} (hs : StOK s) (j : Nat) : s.getD j 0 < 256 := getD_lt256_all hs.2 j

theorem xor_lt256 {a b : Nat} (ha : a < 256) (hb : b < 256) : a ^^^ b < 256 := by
  have := Nat.xor_lt_two_pow (n := 8) (x := a) (y := b) (by simpa using ha) (by simpa using hb)
  simpa using this

/-! ### Key bytes -/

/-- The round key is 16 bytes below 256. -/
@[expose] def KeyOK (k : List Nat) : Prop := k.length = 16 ∧ ∀ x ∈ k, x < 256

theorem keyOK_getD {k : List Nat} (hk : KeyOK k) (i : Nat) : k.getD i 0 < 256 :=
  getD_lt256 (s := k) hk i

/-! ### AddRoundKey -/

theorem addRoundKey_eq (s key : List Nat) (hs : s.length = 16) (hk : key.length = 16) :
    addRoundKey s key = (List.range 16).map (fun i => s.getD i 0 ^^^ key.getD i 0) := by
  apply List.ext_getElem
  · simp [addRoundKey, hs, hk]
  · intro i h1 h2
    have h3 : i < 16 := by simpa using h2
    simp [addRoundKey, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < s.length),
      List.getElem?_eq_getElem (by omega : i < key.length)]

theorem stOK_addRoundKey {s key : List Nat} (hs : StOK s) (hk : KeyOK key) : StOK (addRoundKey s key) := by
  rw [addRoundKey_eq s key hs.1 hk.1]
  exact stOK_map16 _ (fun i _ => xor_lt256 (getD_lt256 hs i) (keyOK_getD hk i))

theorem sem_arkE (v : Wire → Bool) (hv : IsVal v) (W : List Wire) (s key : List Nat) (hW : W.map v = bits8 s)
    (hs : StOK s) (hk : KeyOK key) : (arkE W key).sem v = bits8 (addRoundKey s key) := by
  rw [addRoundKey_eq s key hs.1 hk.1, bits8_map, arkE, sem_catAll_map]
  apply flatMap_congr'
  intro i hi
  have hi' : i < 16 := List.mem_range.1 hi
  have hb := sem_byteE v W s hW i (by rw [hs.1]; exact hi')
  have hl := sem_lit8 v hv (key.getD i 0)
  exact sem_bxor8 v _ _ _ _ hb hl (getD_lt256 hs i) (keyOK_getD hk i)

/-! ### SubBytes and ShiftRows -/

theorem getD_map_sbox (s : List Nat) (j : Nat) (hj : j < s.length) : (s.map sbox).getD j 0 = sbox (s.getD j 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem srcIdx_lt (i : Nat) : srcIdx i < 16 := by
  unfold srcIdx
  have h1 : (i / 4 + i % 4) % 4 < 4 := Nat.mod_lt _ (by omega)
  have h2 : i % 4 < 4 := Nat.mod_lt _ (by omega)
  omega

theorem shiftRows_subBytes (s : List Nat) (hs : s.length = 16) :
    shiftRows (subBytes s) = (List.range 16).map (fun i => sbox (s.getD (srcIdx i) 0)) := by
  unfold shiftRows subBytes
  apply List.map_congr_left
  intro i _
  exact getD_map_sbox s _ (by rw [hs]; exact srcIdx_lt i)

theorem sbox_lt256 (a : Nat) (ha : a < 256) : sbox a < 256 := by
  rw [← AES.sbox_table a ha]
  by_cases h : a < AES.sBoxTable.length
  · have : AES.sBoxTable.getD a 0 = AES.sBoxTable[a] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    rw [this]
    exact sBoxTable_lt _ (List.getElem_mem h)
  · have : AES.sBoxTable.getD a 0 = 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.not_lt.1 h)]
    rw [this]; omega

theorem stOK_subShift {s : List Nat} (hs : StOK s) : StOK (shiftRows (subBytes s)) := by
  rw [shiftRows_subBytes s hs.1]
  exact stOK_map16 _ (fun i _ => sbox_lt256 _ (getD_lt256 hs _))

theorem sem_subShiftE (v : Wire → Bool) (W : List Wire) (s : List Nat) (hW : W.map v = bits8 s) (hs : StOK s) :
    (subShiftE W).sem v = bits8 (shiftRows (subBytes s)) := by
  rw [shiftRows_subBytes s hs.1, bits8_map, subShiftE, sem_catAll_map]
  apply flatMap_congr'
  intro i hi
  have hb := sem_byteE v W s hW (srcIdx i) (by rw [hs.1]; exact srcIdx_lt i)
  exact sem_tblSbox v _ _ hb (getD_lt256 hs _)


/-! ### MixColumns -/

theorem flatMap_len4 (f : Nat → List Nat) (hf : ∀ c, (f c).length = 4) :
    ∀ n, ((List.range n).flatMap f).length = 4 * n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp [hf]
    omega

theorem flatMap4_getD (f : Nat → List Nat) (hf : ∀ c, (f c).length = 4) :
    ∀ n i, i < 4 * n → ((List.range n).flatMap f).getD i 0 = (f (i / 4)).getD (i % 4) 0 := by
  intro n
  induction n with
  | zero => intro i h; omega
  | succ n ih =>
    intro i h
    rw [List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    by_cases hi : i < 4 * n
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [flatMap_len4 f hf n]; exact hi),
        ← List.getD_eq_getElem?_getD]
      exact ih i hi
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [flatMap_len4 f hf n]; omega),
        flatMap_len4 f hf n, ← List.getD_eq_getElem?_getD]
      have h1 : i / 4 = n := by omega
      have h2 : i - 4 * n = i % 4 := by omega
      rw [h1, h2]

/-- The byte `i = 4c + r` of `MixColumns`, in the association of `mixColumn`. -/
@[expose] def mixCore (s : List Nat) (i : Nat) : Nat :=
  (s.getD (4 * (i / 4) + i % 4) 0 ^^^
      (((s.getD (4 * (i / 4)) 0 ^^^ s.getD (4 * (i / 4) + 1) 0) ^^^ s.getD (4 * (i / 4) + 2) 0) ^^^
        s.getD (4 * (i / 4) + 3) 0)) ^^^
    xtime (s.getD (4 * (i / 4) + i % 4) 0 ^^^ s.getD (4 * (i / 4) + (i % 4 + 1) % 4) 0)

/-- With the round key. -/
@[expose] def mixVal (s key : List Nat) (i : Nat) : Nat := mixCore s i ^^^ key.getD i 0

theorem mixColumn_len (l : List Nat) (h : l.length = 4) : (mixColumn l).length = 4 := by
  match l, h with
  | [a, b, c, d], _ => rfl

theorem mixCols_len4 (s : List Nat) :
    ∀ c, (mixColumn ((List.range 4).map fun r => s.getD (4 * c + r) 0)).length = 4 := by
  intro c
  exact mixColumn_len _ (by simp)

theorem mixColumns_len (s : List Nat) : (mixColumns s).length = 16 := by
  unfold mixColumns mapCols
  rw [flatMap_len4 _ (mixCols_len4 s) 4]

theorem mixColumns_getD (s : List Nat) (i : Nat) (hi : i < 16) : (mixColumns s).getD i 0 = mixCore s i := by
  unfold mixColumns mapCols
  rw [flatMap4_getD _ (mixCols_len4 s) 4 i (by omega)]
  have e : ∀ g : Nat → Nat, (List.range 4).map g = [g 0, g 1, g 2, g 3] := fun g => rfl
  rw [e]
  have hr : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  rcases hr with h | h | h | h
  · simp only [mixColumn, mixCore, h]; rfl
  · simp only [mixColumn, mixCore, h]; rfl
  · simp only [mixColumn, mixCore, h]; rfl
  · simp only [mixColumn, mixCore, h]; rfl

theorem addRoundKey_mixColumns (s key : List Nat) (hk : key.length = 16) :
    addRoundKey (mixColumns s) key = (List.range 16).map (mixVal s key) := by
  apply List.ext_getElem
  · simp [addRoundKey, mixColumns_len, hk]
  · intro i h1 h2
    have h3 : i < 16 := by simpa using h2
    have e1 : (mixColumns s)[i]'(by rw [mixColumns_len]; exact h3) = (mixColumns s).getD i 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [mixColumns_len]; exact h3 : i < (mixColumns s).length)]
    have e2 : key[i]'(by omega) = key.getD i 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < key.length)]
    simp only [addRoundKey, List.getElem_zipWith, List.getElem_map, List.getElem_range]
    rw [e1, e2, mixColumns_getD s i h3]
    rfl


theorem mixVal_lt (s key : List Nat) (hs : StOK s) (hk : KeyOK key) (i : Nat) : mixVal s key i < 256 := by
  unfold mixVal mixCore
  refine xor_lt256 (xor_lt256 (xor_lt256 (getD_lt256 hs _) ?_) ?_) (keyOK_getD hk i)
  · exact xor_lt256 (xor_lt256 (xor_lt256 (getD_lt256 hs _) (getD_lt256 hs _)) (getD_lt256 hs _)) (getD_lt256 hs _)
  · exact xtime_lt _ (xor_lt256 (getD_lt256 hs _) (getD_lt256 hs _))

theorem stOK_mix {s key : List Nat} (hs : StOK s) (hk : KeyOK key) : StOK (addRoundKey (mixColumns s) key) := by
  rw [addRoundKey_mixColumns s key hk.1]
  exact stOK_map16 _ (fun i _ => mixVal_lt s key hs hk i)

theorem sem_mixByteE (v : Wire → Bool) (hv : IsVal v) (W : List Wire) (s key : List Nat) (hW : W.map v = bits8 s)
    (hs : StOK s) (hk : KeyOK key) (i : Nat) (hi : i < 16) :
    (mixByteE W key i).sem v = natBits (mixVal s key i) 8 := by
  have hc : i / 4 < 4 := by omega
  have hb : ∀ j, j < 4 → (byteE W (4 * (i / 4) + j)).sem v = natBits (s.getD (4 * (i / 4) + j) 0) 8 := by
    intro j hj
    exact sem_byteE v W s hW _ (by rw [hs.1]; omega)
  have hb0 : (byteE W (4 * (i / 4))).sem v = natBits (s.getD (4 * (i / 4)) 0) 8 :=
    sem_byteE v W s hW _ (by rw [hs.1]; omega)
  have hr : (byteE W (4 * (i / 4) + i % 4)).sem v = natBits (s.getD (4 * (i / 4) + i % 4) 0) 8 :=
    hb (i % 4) (Nat.mod_lt _ (by omega))
  have hr1 : (byteE W (4 * (i / 4) + (i % 4 + 1) % 4)).sem v =
      natBits (s.getD (4 * (i / 4) + (i % 4 + 1) % 4) 0) 8 := hb _ (Nat.mod_lt _ (by omega))
  have g := fun j => getD_lt256 hs j
  have t1 := sem_bxor8 v _ _ _ _ hb0 (hb 1 (by omega)) (g _) (g _)
  have t2 := sem_bxor8 v _ _ _ _ t1 (hb 2 (by omega)) (xor_lt256 (g _) (g _)) (g _)
  have t3 := sem_bxor8 v _ _ _ _ t2 (hb 3 (by omega)) (xor_lt256 (xor_lt256 (g _) (g _)) (g _)) (g _)
  have x1 := sem_bxor8 v _ _ _ _ hr hr1 (g _) (g _)
  have x2 := sem_xtimeE v hv _ _ x1 (xor_lt256 (g _) (g _))
  have u1 := sem_bxor8 v _ _ _ _ hr t3 (g _)
    (xor_lt256 (xor_lt256 (xor_lt256 (g _) (g _)) (g _)) (g _))
  have u2 := sem_bxor8 v _ _ _ _ u1 x2
    (xor_lt256 (g _) (xor_lt256 (xor_lt256 (xor_lt256 (g _) (g _)) (g _)) (g _)))
    (xtime_lt _ (xor_lt256 (g _) (g _)))
  have u3 := sem_bxor8 v _ _ _ _ u2 (sem_lit8 v hv (key.getD i 0))
    (xor_lt256 (xor_lt256 (g _) (xor_lt256 (xor_lt256 (xor_lt256 (g _) (g _)) (g _)) (g _)))
      (xtime_lt _ (xor_lt256 (g _) (g _))))
    (keyOK_getD hk i)
  exact u3

theorem sem_mixE (v : Wire → Bool) (hv : IsVal v) (W : List Wire) (s key : List Nat) (hW : W.map v = bits8 s)
    (hs : StOK s) (hk : KeyOK key) :
    (mixE W key).sem v = bits8 (addRoundKey (mixColumns s) key) := by
  rw [addRoundKey_mixColumns s key hk.1, bits8_map, mixE, sem_catAll_map]
  apply flatMap_congr'
  intro i hi
  exact sem_mixByteE v hv W s key hW hs hk i (List.mem_range.1 hi)

end SmcIrred
