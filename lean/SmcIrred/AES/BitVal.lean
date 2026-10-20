module

public import SmcIrred.Prims.BvDsl
public import SmcIrred.Prims.BvVal
public import SmcIrred.Spec.AESProg
public import SmcIrred.AES.Xtime
public import SmcIrred.AES.TabSbox

public section

namespace SmcIrred

/-! # Bit-level bridging for the AES program (R13)

Bit lists are `natBits value width`. The lemmas relate the semantics of the expression constructors on such lists to the
bitwise operations of the natural numbers, so that the semantics of the AES program can be read as the byte-level
specification. -/

theorem natBits_pad (a w d : Nat) (h : a < 2 ^ w) :
    natBits a w ++ List.replicate d false = natBits a (w + d) := by
  rw [natBits_range, natBits_range, List.range_add, List.map_append]
  congr 1
  symm
  rw [List.eq_replicate_iff]
  refine ⟨by simp, ?_⟩
  intro b hb
  simp only [List.map_map, List.mem_map, List.mem_range, Function.comp] at hb
  obtain ⟨x, _, rfl⟩ := hb
  exact testBit_ge (w + x) a (Nat.le_trans (bitLen_le a w h) (by omega))

theorem padB_natBits (a w m : Nat) (h : a < 2 ^ w) (hm : w ≤ m) : padB m (natBits a w) = natBits a m := by
  unfold padB
  rw [natBits_length, natBits_pad a w (m - w) h, show w + (m - w) = m by omega]

theorem bitwiseB_nat (f : Bool → Bool → Bool) (op : Nat → Nat → Nat)
    (hop : ∀ a b j, (op a b).testBit j = f (a.testBit j) (b.testBit j))
    (a b w1 w2 : Nat) (ha : a < 2 ^ w1) (hb : b < 2 ^ w2) :
    bitwiseB f (natBits a w1) (natBits b w2) = natBits (op a b) (max w1 w2) := by
  unfold bitwiseB
  rw [natBits_length, natBits_length, padB_natBits a w1 _ ha (Nat.le_max_left _ _),
    padB_natBits b w2 _ hb (Nat.le_max_right _ _)]
  apply List.ext_getElem
  · simp [natBits_length]
  · intro i h1 h2
    simp [natBits_range, hop]

theorem slice_natBits (a w i n : Nat) : ((natBits a w).drop i).take n = natBits (a >>> i) (min n (w - i)) := by
  apply List.ext_getElem
  · simp [natBits_length]
  · intro j h1 h2
    simp [natBits_range, Nat.testBit_shiftRight, Nat.add_comm]


theorem bits8_cons (x : Nat) (t : List Nat) : AES.bits8 (x :: t) = natBits x 8 ++ AES.bits8 t := by
  simp [AES.bits8]

theorem bits8_length (bs : List Nat) : (AES.bits8 bs).length = 8 * bs.length := by
  induction bs with
  | nil => rfl
  | cons x t ih => rw [bits8_cons, List.length_append, natBits_length, ih]; simp; omega

/-- Byte `b` of a packed state is the bits of the `b`-th byte. -/
theorem byte_slice : ∀ (bs : List Nat) (b : Nat), b < bs.length →
    ((AES.bits8 bs).drop (8 * b)).take 8 = natBits (bs.getD b 0) 8 := by
  intro bs
  induction bs with
  | nil => intro b h; simp at h
  | cons x t ih =>
    intro b h
    rw [bits8_cons]
    cases b with
    | zero =>
      simp only [Nat.mul_zero, List.drop_zero, List.getD_cons_zero]
      exact List.take_left' (natBits_length 8 x)
    | succ b =>
      have e : 8 * (b + 1) = (natBits x 8).length + 8 * b := by rw [natBits_length]; omega
      rw [e, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
        Nat.add_sub_cancel_left, ih b (by simpa using h)]
      simp

theorem sem_byteE (v : Wire → Bool) (W : List Wire) (bs : List Nat) (hW : W.map v = AES.bits8 bs) (b : Nat)
    (hb : b < bs.length) : (AES.byteE W b).sem v = natBits (bs.getD b 0) 8 := by
  simp only [AES.byteE, BvExp.sem, hW]
  exact byte_slice bs b hb

theorem sem_lit8 (v : Wire → Bool) (hv : IsVal v) (n : Nat) : (AES.lit8 n).sem v = natBits n 8 := by
  have hv' : ∀ b, v (.cst b) = b := hv
  simp [AES.lit8, BvExp.sem, natBits_range, hv']

/-- The valuation of the byte `a` on the nodes `0..7`. -/
@[expose] def vA (a : Nat) : Wire → Bool
  | .cst b => b
  | .nd j => a.testBit j

theorem xt_check : ∀ a < 256, (AES.xtimeE (.inp ((List.range 8).map Wire.nd))).sem (vA a) =
    natBits (AES.xtime a) 8 := by
  intro a ha
  have := AES.forall_lt 256
    (fun a => decide ((AES.xtimeE (.inp ((List.range 8).map Wire.nd))).sem (vA a) = natBits (AES.xtime a) 8))
    (by decide +kernel) a ha
  simpa using this

theorem sem_xtimeE_congr (v w : Wire → Bool) (hv : IsVal v) (hw : IsVal w) (x y : BvExp) (h : x.sem v = y.sem w) :
    (AES.xtimeE x).sem v = (AES.xtimeE y).sem w := by
  have hv' : ∀ b, v (.cst b) = b := hv
  have hw' : ∀ b, w (.cst b) = b := hw
  simp [AES.xtimeE, AES.shlE, AES.lit8, BvExp.sem, h, hv', hw', Function.comp_def]

theorem sem_xtimeE (v : Wire → Bool) (hv : IsVal v) (x : BvExp) (a : Nat) (hx : x.sem v = natBits a 8)
    (ha : a < 256) : (AES.xtimeE x).sem v = natBits (AES.xtime a) 8 := by
  have h1 : (BvExp.inp ((List.range 8).map Wire.nd)).sem (vA a) = natBits a 8 := by
    simp [BvExp.sem, natBits_range, vA]
  exact (sem_xtimeE_congr v (vA a) hv (fun _ => rfl) x _ (hx.trans h1.symm)).trans (xt_check a ha)


theorem bitLen_div (n : Nat) (h : n ≠ 0) : bitLen n = bitLen (n / 2) + 1 := by
  cases n with
  | zero => exact absurd rfl h
  | succ m => exact bitLen_succ m

theorem bitLen202 : bitLen 202 = 8 := by
  have h0 : bitLen 0 = 0 := by rw [bitLen]
  simp only [bitLen_div 202 (by decide), bitLen_div 101 (by decide), bitLen_div 50 (by decide),
    bitLen_div 25 (by decide), bitLen_div 12 (by decide), bitLen_div 6 (by decide), bitLen_div 3 (by decide),
    bitLen_div 1 (by decide), Nat.reduceDiv, h0]

theorem foldl_max_le {α : Type} (f : α → Nat) (c : Nat) : ∀ (l : List α) (c0 : Nat), c0 ≤ c →
    (∀ x ∈ l, f x ≤ c) → (l.map f).foldl max c0 ≤ c := by
  intro l
  induction l with
  | nil => intro c0 h _; simpa using h
  | cons a t ih =>
    intro c0 h hl
    simp only [List.map_cons, List.foldl_cons]
    exact ih _ (Nat.max_le.2 ⟨h, hl a List.mem_cons_self⟩) (fun x hx => hl x (List.mem_cons_of_mem _ hx))

theorem sBoxTable_lt : ∀ x ∈ AES.sBoxTable, x < 256 := by
  intro x hx
  have : AES.sBoxTable.all (fun y => decide (y < 256)) = true := by decide +kernel
  simpa using List.all_eq_true.1 this x hx

theorem tblW_sbox : tblW AES.sBoxTable = 8 := by
  unfold tblW
  apply Nat.le_antisymm
  · apply foldl_max_le bitLen 8 AES.sBoxTable 0 (Nat.zero_le _)
    intro x hx
    exact bitLen_le x 8 (by simpa using sBoxTable_lt x hx)
  · have hm : 202 ∈ AES.sBoxTable := by decide +kernel
    have := le_foldl_max bitLen AES.sBoxTable 0 202 hm
    rw [bitLen202] at this
    exact this

theorem sem_tblSbox (v : Wire → Bool) (idx : BvExp) (a : Nat) (hx : idx.sem v = natBits a 8) (ha : a < 256) :
    (BvExp.tbl idx AES.sBoxTable).sem v = natBits (AES.sbox a) 8 := by
  simp only [BvExp.sem, hx]
  rw [bv_natBits 8 a (by simpa using ha), AES.sbox_table a ha, tblW_sbox]

theorem sem_bxor8 (v : Wire → Bool) (x y : BvExp) (a b : Nat) (hx : x.sem v = natBits a 8)
    (hy : y.sem v = natBits b 8) (ha : a < 256) (hb : b < 256) :
    (BvExp.bxor x y).sem v = natBits (a ^^^ b) 8 := by
  simp only [BvExp.sem, hx, hy]
  rw [bitwiseB_nat (fun p q => p != q) (fun p q => p ^^^ q) (fun p q j => Nat.testBit_xor p q j) a b 8 8
    (by simpa using ha) (by simpa using hb)]
  simp

theorem sem_catAll_map {α : Type} (l : List α) (f : α → BvExp) (v : Wire → Bool) :
    (AES.catAll (l.map f)).sem v = l.flatMap (fun a => (f a).sem v) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [AES.catAll, BvExp.sem, ih]

theorem bits8_map {α : Type} (l : List α) (g : α → Nat) :
    AES.bits8 (l.map g) = l.flatMap (fun a => natBits (g a) 8) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [bits8_cons, ih]

theorem flatMap_congr' {α β : Type} (l : List α) (f g : α → List β) (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.flatMap_cons]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem ok_catAll_map {α : Type} (l : List α) (f : α → BvExp) (n : Nat) (h : ∀ a ∈ l, (f a).ok n) :
    (AES.catAll (l.map f)).ok n := by
  induction l with
  | nil => intro w hw; simp at hw
  | cons a t ih =>
    exact ⟨h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

end SmcIrred
