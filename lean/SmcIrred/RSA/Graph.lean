module

public import SmcIrred.RSA.Circuit
public import SmcIrred.AES.Circuit

public section

namespace SmcIrred

open RSA

/-! # The RSA graph computes modular exponentiation (R15, G30)

For an odd modulus `1 < N ≤ 2^B`, the Montgomery constants `Np`, `R2` and a window `1 ≤ w`, the compiled graph of
`rsaGraph` carries, on its output wires, `a ^ e % N` for the number `a < N` on the `B` input nodes (every other node
reads no input). The multiplier variants of the Python code are not part of this graph (see `Spec.RsaProg`). -/

section
variable {inp : Nat → Bool} {k : Nat}

theorem rel_const (gb : GB) (n B : Nat) (hn : n < 2 ^ B) : Rel inp gb (constWires n B) n := by
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [constWires, List.mem_map] at hw
    obtain ⟨j, _, rfl⟩ := hw
    trivial
  · have : (constWires n B).map (wev gb inp) = natBits n B := by
      rw [natBits_range, constWires, List.map_map]
      rfl
    rw [this]
    exact bv_natBits B n hn

/-- The circuit of the RSA graph on wires `W` carrying `a`. -/
theorem rsaCircuit_rel (hinp : ∀ i, k ≤ i → inp i = false) (B N Np R2 w e : Nat) (hN : N < 2 ^ B) (hNp : Np < 2 ^ B)
    (hR2 : R2 < 2 ^ B) (h0 : Arith.redc B N Np R2 < 2 ^ B) (hN1 : N ≠ 1) (hone : 1 < 2 ^ B)
    {gb : GB} {W : List Wire} {a : Nat} (h : WI k gb) (hW : Rel inp gb W a) :
    Ext gb (rsaCircuit B N Np R2 w e gb W).2 ∧ WI k (rsaCircuit B N Np R2 w e gb W).2 ∧
      Rel inp (rsaCircuit B N Np R2 w e gb W).2 (rsaCircuit B N Np R2 w e gb W).1
        (Arith.redc B N Np (Arith.modexpMontWin B N Np R2 w (Arith.toM B N Np R2 a) e)) := by
  unfold rsaCircuit
  dsimp only
  obtain ⟨e1, w1, r1⟩ := mmulG_rel hinp B N Np hN hNp h hW (rel_const gb R2 B hR2)
  obtain ⟨e2, w2, r2⟩ := winExpG_rel hinp B N Np hN hNp (oneW := constWires (Arith.redc B N Np R2) B) w e w1
    (rel_const _ _ B h0) r1
  have hc : Rel inp (winExpG B N Np (constWires (Arith.redc B N Np R2) B) (mmulG B N Np gb W (constWires R2 B)).1 w e
      (mmulG B N Np gb W (constWires R2 B)).2).2 (constWires 1 B) 1 := rel_const _ 1 B hone
  obtain ⟨e3, w3, r3⟩ := mmulG_rel hinp B N Np hN hNp w2 r2 hc
  refine ⟨e1.trans (e2.trans e3), w3, ?_⟩
  have := r3
  rw [Nat.mul_one] at this
  unfold Arith.modexpMontWin Arith.toM
  rw [if_neg hN1]
  exact this

end

theorem rsaGraph_correct (B N Np R2 w e : Nat) (hN : 1 < N) (hodd : N % 2 = 1) (hNp : (N * Np + 1) % 2 ^ B = 0)
    (hRi : ∃ Ri, Arith.Cong N (2 ^ B * Ri) 1) (hNR : N ≤ 2 ^ B) (hNpB : Np < 2 ^ B)
    (hR2 : R2 = (2 ^ B * 2 ^ B) % N) (inp : Nat → Bool) (hinp : ∀ i, B ≤ i → inp i = false)
    (ha : bv ((List.range B).map inp) < N) (hw : 1 ≤ w) (he : e < 2 ^ B) :
    Reach (rsaGraph B N Np R2 w e).2 ∧ (∀ x ∈ (rsaGraph B N Np R2 w e).1, x.ok (rsaGraph B N Np R2 w e).2.n) ∧
      bv ((rsaGraph B N Np R2 w e).1.map (wev (rsaGraph B N Np R2 w e).2 inp)) =
        bv ((List.range B).map inp) ^ e % N := by
  obtain ⟨Ri, hRi⟩ := hRi
  have hm := mkInputs_eq B ⟨[]⟩
  have hn : (⟨[]⟩ : GB).n = 0 := rfl
  have hr : Reach (mkInputs ⟨[]⟩ B).2 := by
    rw [hm]
    simpa using reach_replicate B
  have hW : ∀ x ∈ (mkInputs ⟨[]⟩ B).1, x.ok (mkInputs ⟨[]⟩ B).2.n := by
    intro x hx
    rw [hm] at hx ⊢
    simp only [hn, Nat.zero_add, List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    simpa [GB.n, Wire.ok] using hj
  have hv : (mkInputs ⟨[]⟩ B).1.map (wev (mkInputs ⟨[]⟩ B).2 inp) = (List.range B).map inp := by
    rw [hm]
    simp only [hn, Nat.zero_add, List.map_map]
    apply List.map_congr_left
    intro j hj
    have hj' : j < B := List.mem_range.1 hj
    simp only [Function.comp, wev, Wire.ev, List.nil_append]
    rw [evalNodes_replicate]
    simp [List.getD_eq_getElem?_getD, hj']
  have hWI : WI B (mkInputs ⟨[]⟩ B).2 := ⟨hr, by rw [hm]; simp [GB.n]⟩
  have hNpos : 0 < N := by omega
  have hRrel : Rel inp (mkInputs ⟨[]⟩ B).2 (mkInputs ⟨[]⟩ B).1 (bv ((List.range B).map inp)) := ⟨hW, by rw [hv]⟩
  have hNB : N < 2 ^ B := by
    have : N ≠ 2 ^ B := by
      intro h
      have h2 : 2 ^ B % 2 = 1 := h ▸ hodd
      cases B with
      | zero => omega
      | succ b => rw [Nat.pow_succ] at h2; omega
    omega
  have hR2lt : R2 < N := by rw [hR2]; exact Nat.mod_lt _ hNpos
  have h0 : Arith.redc B N Np R2 < N :=
    (Arith.redc_spec hNpos hNp (by
      have : N ≤ 2 ^ B * N := Nat.le_mul_of_pos_left N (Nat.two_pow_pos B)
      omega)).1
  have hone : 1 < 2 ^ B := by omega
  obtain ⟨_, w1, r1⟩ := rsaCircuit_rel (inp := inp) (k := B) (fun i hi => hinp i hi) B N Np R2 w e hNB hNpB
    (by omega) (by omega) (by omega) hone hWI hRrel
  have hc := Arith.modexpMontWin_correct hNpos hodd hNp hRi hNR hR2 ha hw he
  unfold rsaGraph
  dsimp only
  refine ⟨w1.1, r1.1, ?_⟩
  rw [r1.2, hc]

end SmcIrred
