module

public import SmcIrred.AES.Circuit

public section

namespace SmcIrred

open AES

/-! # The expanded AES key is made of bytes (R13)

`aesCircuit_correct` needs every round key to be 16 bytes below 256. For the expanded key of `Spec.AES.keyExp` over the
byte algebra `natAlg` this holds whenever the key bytes are below 256: the expansion only moves words around, XORs bytes,
looks up the S-box and adds a round-constant byte. -/

/-- Every word has four bytes below 256. -/
@[expose] def WOK (ws : List (List Nat)) : Prop := ∀ w ∈ ws, w.length = 4 ∧ ∀ x ∈ w, x < 256

theorem rcon_lt (j : Nat) : rconTable.getD j 0 < 256 := by
  have h : rconTable.all (fun y => decide (y < 256)) = true := by decide +kernel
  by_cases hj : j < rconTable.length
  · have : rconTable.getD j 0 = rconTable[j] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rw [this]
    simpa using List.all_eq_true.1 h _ (List.getElem_mem hj)
  · have : rconTable.getD j 0 = 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.not_lt.1 hj)]
    rw [this]; omega

theorem wok_getD {ws : List (List Nat)} (h : WOK ws) (i : Nat) :
    (ws.getD i (zW natAlg)).length = 4 ∧ ∀ x ∈ ws.getD i (zW natAlg), x < 256 := by
  by_cases hi : i < ws.length
  · have : ws.getD i (zW natAlg) = ws[i] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rw [this]
    exact h _ (List.getElem_mem hi)
  · have : ws.getD i (zW natAlg) = zW natAlg := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.not_lt.1 hi)]
    rw [this]
    simp [zW, natAlg]

theorem rotW_len (w : List Nat) : (rotW w).length = w.length := by
  match w with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | [_, _, _, _] => rfl
  | _ :: _ :: _ :: _ :: _ :: _ => rfl

theorem rotW_mem (w : List Nat) (x : Nat) (h : x ∈ rotW w) : x ∈ w := by
  match w with
  | [] => exact h
  | [_] => exact h
  | [_, _] => exact h
  | [_, _, _] => exact h
  | [a, b, c, d] =>
    simp only [rotW, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    omega
  | _ :: _ :: _ :: _ :: _ :: _ => exact h

/-- A word of four bytes below 256. -/
@[expose] def WdOK (w : List Nat) : Prop := w.length = 4 ∧ ∀ x ∈ w, x < 256

theorem wd_rot {w : List Nat} (h : WdOK w) : WdOK (rotW w) :=
  ⟨by rw [rotW_len, h.1], fun x hx => h.2 x (rotW_mem w x hx)⟩

theorem wd_sub {w : List Nat} (h : WdOK w) : WdOK (subW natAlg w) := by
  refine ⟨by simp [subW, natAlg, h.1], ?_⟩
  intro x hx
  simp only [subW, natAlg, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact sbox_lt256 _ (h.2 y hy)

theorem wd_rc (j : Nat) {w : List Nat} (h : WdOK w) : WdOK (rcW natAlg j w) := by
  match w, h with
  | [], h => simp [WdOK] at h
  | a :: t, h =>
    refine ⟨by simpa [rcW] using h.1, ?_⟩
    intro x hx
    simp only [rcW, List.mem_cons, natAlg] at hx
    rcases hx with rfl | hx
    · exact xor_lt256 (h.2 a List.mem_cons_self) (rcon_lt j)
    · exact h.2 x (List.mem_cons_of_mem _ hx)

theorem zipWith_xor_lt : ∀ (u v : List Nat), (∀ x ∈ u, x < 256) → (∀ y ∈ v, y < 256) →
    ∀ z ∈ List.zipWith (· ^^^ ·) u v, z < 256 := by
  intro u
  induction u with
  | nil => intro v _ _ z hz; simp at hz
  | cons a t ih =>
    intro v hu hv z hz
    cases v with
    | nil => simp at hz
    | cons b w =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact xor_lt256 (hu a List.mem_cons_self) (hv b List.mem_cons_self)
      · exact ih w (fun x hx => hu x (List.mem_cons_of_mem _ hx)) (fun y hy => hv y (List.mem_cons_of_mem _ hy)) z hz

theorem wd_xor {u v : List Nat} (hu : WdOK u) (hv : WdOK v) : WdOK (wxor natAlg u v) :=
  ⟨by simp [wxor, natAlg, hu.1, hv.1], zipWith_xor_lt u v hu.2 hv.2⟩

theorem expandStep_wok (Nk : Nat) (ws : List (List Nat)) (h : WOK ws) : WOK (expandStep natAlg Nk ws) := by
  unfold expandStep
  intro w hw
  dsimp only at hw
  rcases List.mem_append.1 hw with h1 | h1
  · exact h _ h1
  · simp only [List.mem_singleton] at h1
    subst h1
    have hb : WdOK (ws.getD (ws.length - Nk) (zW natAlg)) := wok_getD h _
    have hp : WdOK (ws.getD (ws.length - 1) (zW natAlg)) := wok_getD h _
    apply wd_xor hb
    split
    · exact wd_rc _ (wd_sub (wd_rot hp))
    · split
      · exact wd_sub hp
      · exact hp

theorem expandN_wok (Nk : Nat) : ∀ (n : Nat) (ws : List (List Nat)), WOK ws → WOK (expandN natAlg Nk n ws) := by
  intro n
  induction n with
  | zero => intro ws h; exact h
  | succ n ih => intro ws h; exact ih _ (expandStep_wok Nk ws h)

theorem expandStep_len (Nk : Nat) (ws : List (List Nat)) : (expandStep natAlg Nk ws).length = ws.length + 1 := by
  unfold expandStep
  simp

theorem expandN_len (Nk : Nat) : ∀ (n : Nat) (ws : List (List Nat)), (expandN natAlg Nk n ws).length = ws.length + n := by
  intro n
  induction n with
  | zero => intro ws; rfl
  | succ n ih => intro ws; rw [expandN, ih, expandStep_len]; omega

theorem keyExp_wok (Nk Nr : Nat) (key : List Nat) (hkey : ∀ x ∈ key, x < 256) (hle : Nk ≤ 4 * (Nr + 1)) :
    WOK (keyExp natAlg Nk Nr key) ∧ (keyExp natAlg Nk Nr key).length = 4 * (Nr + 1) := by
  unfold keyExp
  have h0 : WOK ((List.range Nk).map fun j => (List.range 4).map fun r => key.getD (4 * j + r) natAlg.zero) := by
    intro w hw
    simp only [List.mem_map, List.mem_range] at hw
    obtain ⟨j, _, rfl⟩ := hw
    refine ⟨by simp, ?_⟩
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨r, _, rfl⟩ := hx
    exact getD_lt256_all hkey _
  refine ⟨expandN_wok Nk _ _ h0, ?_⟩
  rw [expandN_len]
  simp
  omega


theorem roundKey_keyOK (rk : List (List Nat)) (hrk : WOK rk) (Nr : Nat) (hlen : rk.length = 4 * (Nr + 1))
    (r : Nat) (hr : r ≤ Nr) : KeyOK (roundKey rk r) := by
  have hw : ∀ c, c < 4 → (rk.getD (4 * r + c) []).length = 4 ∧ ∀ x ∈ rk.getD (4 * r + c) [], x < 256 := by
    intro c hc
    have hi : 4 * r + c < rk.length := by omega
    have : rk.getD (4 * r + c) [] = rk[4 * r + c] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rw [this]
    exact hrk _ (List.getElem_mem hi)
  have e : List.range 4 = [0, 1, 2, 3] := rfl
  unfold roundKey KeyOK
  rw [e]
  have h0 := hw 0 (by omega)
  have h1 := hw 1 (by omega)
  have h2 := hw 2 (by omega)
  have h3 := hw 3 (by omega)
  refine ⟨by simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append, h0.1, h1.1, h2.1, h3.1], ?_⟩
  intro x hx
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hx
  rcases hx with hx | hx | hx | hx
  · exact h0.2 x hx
  · exact h1.2 x hx
  · exact h2.2 x hx
  · exact h3.2 x hx

theorem expandedKey_ok (Nk Nr : Nat) (key : List Nat) (hkey : ∀ x ∈ key, x < 256) (hle : Nk ≤ 4 * (Nr + 1)) :
    ∀ r, r ≤ Nr → KeyOK (roundKey (keyExp natAlg Nk Nr key) r) := by
  obtain ⟨h1, h2⟩ := keyExp_wok Nk Nr key hkey hle
  intro r hr
  exact roundKey_keyOK _ h1 Nr h2 r hr

theorem beBytes_lt (n : Nat) : ∀ k, ∀ x ∈ beBytes n k, x < 256 := by
  intro k
  induction k with
  | zero => intro x hx; simp [beBytes] at hx
  | succ k ih =>
    intro x hx
    simp only [beBytes, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.mod_lt _ (by omega)
    · exact ih x hx

/-- AES-128 for every key and block, as a generated graph. -/
theorem aes128Graph_correct (key : Nat) (inp : Nat → Bool) (hinp : ∀ i, 128 ≤ i → inp i = false) :
    Reach (aesGraph 10 (aes128 key)).2 ∧ (∀ w ∈ (aesGraph 10 (aes128 key)).1, w.ok (aesGraph 10 (aes128 key)).2.n) ∧
      (aesGraph 10 (aes128 key)).1.map (wev (aesGraph 10 (aes128 key)).2 inp) =
        bits8 (encrypt 10 (aes128 key) (blockBytes inp)) :=
  aesGraph_correct 10 (aes128 key) (expandedKey_ok 4 10 _ (beBytes_lt key 16) (by omega)) inp hinp

/-- AES-192 for every key and block, as a generated graph. -/
theorem aes192Graph_correct (key : Nat) (inp : Nat → Bool) (hinp : ∀ i, 128 ≤ i → inp i = false) :
    Reach (aesGraph 12 (aes192 key)).2 ∧ (∀ w ∈ (aesGraph 12 (aes192 key)).1, w.ok (aesGraph 12 (aes192 key)).2.n) ∧
      (aesGraph 12 (aes192 key)).1.map (wev (aesGraph 12 (aes192 key)).2 inp) =
        bits8 (encrypt 12 (aes192 key) (blockBytes inp)) :=
  aesGraph_correct 12 (aes192 key) (expandedKey_ok 6 12 _ (beBytes_lt key 24) (by omega)) inp hinp

/-- AES-256 for every key and block, as a generated graph. -/
theorem aes256Graph_correct (key : Nat) (inp : Nat → Bool) (hinp : ∀ i, 128 ≤ i → inp i = false) :
    Reach (aesGraph 14 (aes256 key)).2 ∧ (∀ w ∈ (aesGraph 14 (aes256 key)).1, w.ok (aesGraph 14 (aes256 key)).2.n) ∧
      (aesGraph 14 (aes256 key)).1.map (wev (aesGraph 14 (aes256 key)).2 inp) =
        bits8 (encrypt 14 (aes256 key) (blockBytes inp)) :=
  aesGraph_correct 14 (aes256 key) (expandedKey_ok 8 14 _ (beBytes_lt key 32) (by omega)) inp hinp

end SmcIrred
