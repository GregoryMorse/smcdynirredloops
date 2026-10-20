module

public import SmcIrred.AES.Program

public section

namespace SmcIrred

open AES

/-! # The compiled AES graph computes AES (R13, G30)

With `Prims.BvDsl.comp_correct` for the stage expressions and `AES.Program` for their semantics, the graph `aesCircuit` built
stage by stage (the wires of a stage are shared by everything that reads them) computes the packed result of
`Spec.AES.encrypt` for every block, under the hypothesis that the round keys are 16 bytes below 256
(`KeyOK`, checked in `AES.KeyExp` for the expanded keys).  Nothing here uses the native listing: the statement is about
the Lean transcription of the generator (`Spec/Virt`, `Spec/VirtSel`), whose fidelity to `python/virt.py` is evidence. -/

section
variable {inp : Nat → Bool} {k : Nat}

theorem ok_byteE {n : Nat} {W : List Wire} (h : ∀ w ∈ W, w.ok n) (b : Nat) : (byteE W b).ok n :=
  fun w hw => (Wire.inb_iff n w).2 (h w hw)

theorem ok_lit8 (n k : Nat) : (lit8 k).ok n := by
  intro w hw
  simp only [lit8, List.mem_map] at hw
  obtain ⟨j, _, rfl⟩ := hw
  trivial

theorem ok_xtimeE {n : Nat} {x : BvExp} (h : x.ok n) : (xtimeE x).ok n := by
  have hs : (shlE x).ok n := ⟨fun w hw => by simp at hw; rw [hw]; trivial, h⟩
  exact ⟨h, ⟨hs, ok_lit8 n 0x1B⟩, hs⟩

theorem width_byteE (W : List Wire) (b : Nat) (h : 8 * b + 8 ≤ W.length) : (byteE W b).width = 8 := by
  simp only [byteE, BvExp.width]
  omega

theorem ok_arkE {n : Nat} {W : List Wire} (h : ∀ w ∈ W, w.ok n) (key : List Nat) : (arkE W key).ok n := by
  apply ok_catAll_map
  intro i _
  exact ⟨ok_byteE h i, ok_lit8 n _⟩

theorem ok_mixE {n : Nat} {W : List Wire} (h : ∀ w ∈ W, w.ok n) (key : List Nat) : (mixE W key).ok n := by
  apply ok_catAll_map
  intro i _
  have b := fun j => ok_byteE h j
  exact ⟨⟨⟨b _, ⟨⟨⟨b _, b _⟩, b _⟩, b _⟩⟩, ok_xtimeE ⟨b _, b _⟩⟩, ok_lit8 n _⟩

theorem ok_subShiftE {n : Nat} {W : List Wire} (h : ∀ w ∈ W, w.ok n) (hl : W.length = 128) :
    (subShiftE W).ok n := by
  apply ok_catAll_map
  intro i hi
  have hs := srcIdx_lt i
  refine ⟨ok_byteE h _, ?_⟩
  rw [width_byteE W _ (by omega)]
  simpa using AES.sBoxTable_length

/-- The invariant of a stage boundary: the wires carry the packed bytes `s`. -/
@[expose] def AInv (inp : Nat → Bool) (k : Nat) (gb : GB) (W : List Wire) (s : List Nat) : Prop :=
  Reach gb ∧ k ≤ gb.n ∧ (∀ w ∈ W, w.ok gb.n) ∧ W.map (wev gb inp) = bits8 s ∧ StOK s

theorem AInv.len {gb : GB} {W : List Wire} {s : List Nat} (h : AInv inp k gb W s) : W.length = 128 := by
  have := congrArg List.length h.2.2.2.1
  rw [List.length_map, bits8_length, h.2.2.2.2.1] at this
  exact this

theorem stage_comp (hinp : ∀ i, k ≤ i → inp i = false) (e : BvExp) {gb : GB} (hk : k ≤ gb.n) (hr : Reach gb)
    (he : e.ok gb.n) (s' : List Nat) (hs' : StOK s') (hsem : e.sem (wev gb inp) = bits8 s') :
    Ext gb (e.comp gb).2 ∧ AInv inp k (e.comp gb).2 (e.comp gb).1 s' := by
  obtain ⟨e1, r1, o1, v1⟩ := comp_correct hinp e gb hk hr he
  exact ⟨e1, r1, Nat.le_trans hk e1.n_le, o1, by rw [v1, hsem], hs'⟩

theorem ark_step (hinp : ∀ i, k ≤ i → inp i = false) {gb : GB} {W : List Wire} {s : List Nat}
    (h : AInv inp k gb W s) (key : List Nat) (hk : KeyOK key) :
    Ext gb ((arkE W key).comp gb).2 ∧
      AInv inp k ((arkE W key).comp gb).2 ((arkE W key).comp gb).1 (addRoundKey s key) :=
  stage_comp hinp _ h.2.1 h.1 (ok_arkE h.2.2.1 key) _ (stOK_addRoundKey h.2.2.2.2 hk)
    (sem_arkE _ (fun _ => rfl) W s key h.2.2.2.1 h.2.2.2.2 hk)

theorem subShift_step (hinp : ∀ i, k ≤ i → inp i = false) {gb : GB} {W : List Wire} {s : List Nat}
    (h : AInv inp k gb W s) :
    Ext gb ((subShiftE W).comp gb).2 ∧
      AInv inp k ((subShiftE W).comp gb).2 ((subShiftE W).comp gb).1 (shiftRows (subBytes s)) :=
  stage_comp hinp _ h.2.1 h.1 (ok_subShiftE h.2.2.1 h.len) _ (stOK_subShift h.2.2.2.2)
    (sem_subShiftE _ W s h.2.2.2.1 h.2.2.2.2)

theorem mix_step (hinp : ∀ i, k ≤ i → inp i = false) {gb : GB} {W : List Wire} {s : List Nat}
    (h : AInv inp k gb W s) (key : List Nat) (hk : KeyOK key) :
    Ext gb ((mixE W key).comp gb).2 ∧
      AInv inp k ((mixE W key).comp gb).2 ((mixE W key).comp gb).1 (addRoundKey (mixColumns s) key) :=
  stage_comp hinp _ h.2.1 h.1 (ok_mixE h.2.2.1 key) _ (stOK_mix h.2.2.2.2 hk)
    (sem_mixE _ (fun _ => rfl) W s key h.2.2.2.1 h.2.2.2.2 hk)

theorem round_step (hinp : ∀ i, k ≤ i → inp i = false) {gb : GB} {W : List Wire} {s : List Nat}
    (h : AInv inp k gb W s) (key : List Nat) (hk : KeyOK key) :
    Ext gb (aesRound key gb W).2 ∧
      AInv inp k (aesRound key gb W).2 (aesRound key gb W).1
        (addRoundKey (mixColumns (shiftRows (subBytes s))) key) := by
  obtain ⟨e1, h1⟩ := subShift_step hinp h
  obtain ⟨e2, h2⟩ := mix_step hinp h1 key hk
  exact ⟨e1.trans e2, h2⟩

theorem rounds_step (hinp : ∀ i, k ≤ i → inp i = false) (rk : List (List Nat)) :
    ∀ (n : Nat), (∀ i, i < n → KeyOK (roundKey rk (i + 1))) → ∀ {gb : GB} {W : List Wire} {s : List Nat},
      AInv inp k gb W s →
      Ext gb ((List.range n).foldl (fun (st : List Wire × GB) i => aesRound (roundKey rk (i + 1)) st.2 st.1) (W, gb)).2 ∧
        AInv inp k ((List.range n).foldl (fun (st : List Wire × GB) i => aesRound (roundKey rk (i + 1)) st.2 st.1) (W, gb)).2
          ((List.range n).foldl (fun (st : List Wire × GB) i => aesRound (roundKey rk (i + 1)) st.2 st.1) (W, gb)).1
          ((List.range n).foldl
            (fun s i => addRoundKey (mixColumns (shiftRows (subBytes s))) (roundKey rk (i + 1))) s) := by
  intro n
  induction n with
  | zero => intro _ gb W s h; exact ⟨Ext.refl _, h⟩
  | succ n ih =>
    intro hkeys gb W s h
    obtain ⟨e1, h1⟩ := ih (fun i hi => hkeys i (by omega)) h
    obtain ⟨e2, h2⟩ := round_step hinp h1 (roundKey rk (n + 1)) (hkeys n (by omega))
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    exact ⟨e1.trans e2, h2⟩

/-- The compiled AES graph computes `Spec.AES.encrypt` on the packed block. -/
theorem aesCircuit_correct (hinp : ∀ i, k ≤ i → inp i = false) (Nr : Nat) (rk : List (List Nat))
    (hkeys : ∀ r, r ≤ Nr → KeyOK (roundKey rk r)) {gb : GB} {W : List Wire} {s : List Nat}
    (h : AInv inp k gb W s) :
    Ext gb (aesCircuit Nr rk gb W).2 ∧ Reach (aesCircuit Nr rk gb W).2 ∧
      (∀ w ∈ (aesCircuit Nr rk gb W).1, w.ok (aesCircuit Nr rk gb W).2.n) ∧
      (aesCircuit Nr rk gb W).1.map (wev (aesCircuit Nr rk gb W).2 inp) = bits8 (encrypt Nr rk s) ∧
      StOK (encrypt Nr rk s) := by
  obtain ⟨e0, h0⟩ := ark_step hinp h (roundKey rk 0) (hkeys 0 (Nat.zero_le _))
  obtain ⟨e1, h1⟩ := rounds_step hinp rk (Nr - 1) (fun i hi => hkeys (i + 1) (by omega)) h0
  obtain ⟨e2, h2⟩ := subShift_step hinp h1
  obtain ⟨e3, h3⟩ := ark_step hinp h2 (roundKey rk Nr) (hkeys Nr (Nat.le_refl _))
  refine ⟨e0.trans (e1.trans (e2.trans e3)), h3.1, h3.2.2.1, ?_, h3.2.2.2.2⟩
  simp only [aesCircuit, encrypt]
  exact h3.2.2.2.1

end


/-! ### The input nodes -/

theorem mkInputs_eq (k : Nat) : ∀ (gb : GB),
    mkInputs gb k = ((List.range k).map (fun j => Wire.nd (gb.n + j)),
      (⟨gb.nodes ++ List.replicate k (Kind.flow, [])⟩ : GB)) := by
  induction k with
  | zero => intro gb; simp [mkInputs]
  | succ k ih =>
    intro gb
    have e : mkInputs gb (k + 1) = (Wire.nd gb.n :: (mkInputs (gb.add .flow []).2 k).1,
        (mkInputs (gb.add .flow []).2 k).2) := rfl
    rw [e, ih]
    have hn : (gb.add .flow []).2.n = gb.n + 1 := by simp [GB.add, GB.n]
    have hnodes : (gb.add .flow []).2.nodes = gb.nodes ++ [(Kind.flow, [])] := rfl
    rw [hn, hnodes, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine Prod.ext ?_ ?_
    · simp only [Nat.add_zero]
      congr 1
      apply List.map_congr_left
      intro j _
      simp [Nat.add_assoc, Nat.add_comm 1 j]
    · show (⟨_⟩ : GB) = ⟨_⟩
      congr 1
      rw [List.append_assoc, List.replicate_succ]
      rfl

theorem reach_replicate (k : Nat) : Reach (⟨List.replicate k (Kind.flow, [])⟩ : GB) := by
  induction k with
  | zero => exact Reach.empty
  | succ k ih =>
    have := Reach.add (gb := ⟨List.replicate k (Kind.flow, [])⟩) Kind.flow [] ih trivial (by simp)
    have e : (GB.add ⟨List.replicate k (Kind.flow, [])⟩ Kind.flow []).2 =
        ⟨List.replicate (k + 1) (Kind.flow, [])⟩ := by
      simp [GB.add, List.replicate_succ']
    rw [e] at this
    exact this

theorem evalNodes_replicate (inp : Nat → Bool) (k : Nat) :
    evalNodes inp (List.replicate k (Kind.flow, [])) = (List.range k).map inp := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ', evalNodes_append, ih, List.range_succ, List.map_append]
    simp only [List.foldl_cons, List.foldl_nil, stepE, List.length_map, List.length_range, List.map_cons, List.map_nil]
    congr 1
    cases inp k <;> simp [nodeVal]

theorem flatMap_bytes (f : Nat → Bool) : ∀ n,
    (List.range n).flatMap (fun b => (List.range 8).map fun j => f (8 * b + j)) = (List.range (8 * n)).map f := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ (n := n), List.flatMap_append, ih, show 8 * (n + 1) = 8 * n + 8 by omega, List.range_add,
      List.map_append]
    simp

theorem natBits_bv (l : List Bool) : natBits (bv l) l.length = l := by
  apply bv_inj
  · rw [natBits_length]
  · exact bv_natBits _ _ (bv_lt l)

theorem blockBytes_bits (inp : Nat → Bool) : bits8 (blockBytes inp) = (List.range 128).map inp := by
  unfold blockBytes
  rw [bits8_map]
  have : ∀ b ∈ List.range 16, natBits (bv ((List.range 8).map fun j => inp (8 * b + j))) 8 =
      (List.range 8).map fun j => inp (8 * b + j) := by
    intro b _
    have := natBits_bv ((List.range 8).map fun j => inp (8 * b + j))
    simpa using this
  rw [flatMap_congr' _ _ _ this, flatMap_bytes inp 16]

theorem stOK_blockBytes (inp : Nat → Bool) : StOK (blockBytes inp) := by
  unfold blockBytes
  apply stOK_map16
  intro b _
  have := bv_lt ((List.range 8).map fun j => inp (8 * b + j))
  simpa using this

/-- AES as a generated graph: the 128 input nodes, then the stages. For every assignment of the input nodes (every
other node reads no input) and every expanded key whose round keys are 16 bytes below 256, the 128 output wires carry
the bits of `Spec.AES.encrypt` of the block, and the graph is built from simple nodes only. -/
theorem aesGraph_correct (Nr : Nat) (rk : List (List Nat)) (hkeys : ∀ r, r ≤ Nr → KeyOK (roundKey rk r))
    (inp : Nat → Bool) (hinp : ∀ i, 128 ≤ i → inp i = false) :
    Reach (aesGraph Nr rk).2 ∧ (∀ w ∈ (aesGraph Nr rk).1, w.ok (aesGraph Nr rk).2.n) ∧
      (aesGraph Nr rk).1.map (wev (aesGraph Nr rk).2 inp) = bits8 (encrypt Nr rk (blockBytes inp)) := by
  have hm := mkInputs_eq 128 ⟨[]⟩
  have hn : (⟨[]⟩ : GB).n = 0 := rfl
  have hr : Reach (mkInputs ⟨[]⟩ 128).2 := by
    rw [hm]
    simpa using reach_replicate 128
  have hW : ∀ w ∈ (mkInputs ⟨[]⟩ 128).1, w.ok (mkInputs ⟨[]⟩ 128).2.n := by
    intro w hw
    rw [hm] at hw ⊢
    simp only [hn, Nat.zero_add, List.mem_map, List.mem_range] at hw
    obtain ⟨j, hj, rfl⟩ := hw
    simpa [GB.n, Wire.ok] using hj
  have hv : (mkInputs ⟨[]⟩ 128).1.map (wev (mkInputs ⟨[]⟩ 128).2 inp) = bits8 (blockBytes inp) := by
    rw [blockBytes_bits, hm]
    simp only [hn, Nat.zero_add, List.map_map]
    apply List.map_congr_left
    intro j hj
    have hj' : j < 128 := List.mem_range.1 hj
    simp only [Function.comp, wev, Wire.ev, List.nil_append]
    rw [evalNodes_replicate]
    simp [List.getD_eq_getElem?_getD, hj']
  have hinv : AInv inp 128 (mkInputs ⟨[]⟩ 128).2 (mkInputs ⟨[]⟩ 128).1 (blockBytes inp) :=
    ⟨hr, by rw [hm]; simp [GB.n], hW, hv, stOK_blockBytes inp⟩
  obtain ⟨_, r, o, v, _⟩ := aesCircuit_correct hinp Nr rk hkeys hinv
  exact ⟨r, o, v⟩

end SmcIrred
