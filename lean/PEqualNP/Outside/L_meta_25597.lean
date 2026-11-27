import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Notation

namespace PEqualNP.Outside.L_meta_25597

private def mix (x : ℤ → Bool) (z : ℤ) : Bool :=
  xor (xor (x (z - 1)) (x z)) (x (z + 1))

private def evolve (x inj : ℤ → Bool) (z : ℤ) : Bool :=
  xor (xor (mix x z) (!(mix x (z + 1)) && mix x (z + 2))) (inj z)

private def block (v : ℕ) (x : ℤ → Bool) (c : ℤ) : ℕ :=
  (List.range v).foldl (fun (acc pos : ℕ) => acc ||| ((x (c + 1 + (pos : ℤ))).toNat <<< pos)) 0

private def trial (b : ℤ) (ref : ℤ → Bool) (tailBits : ℕ) (site : ℤ) : Bool :=
  if site ≤ b then ref site else tailBits.testBit (site - b - 1).toNat

private def recoverStep (c : ℤ) (inj : ℤ → Bool) (tval : ℕ) (partialWord j : ℕ) : ℕ :=
  let jz := c + 1 + (j : ℤ)
  let bits := fun (z : ℤ) => partialWord.testBit (z - c).toNat
  let chosen := xor (tval.testBit j) (evolve bits inj jz)
  partialWord ||| (chosen.toNat <<< j)

private def recFold (c : ℤ) (inj : ℤ → Bool) (tval : ℕ) (k pw : ℕ) : ℕ :=
  ((List.range k).reverse).foldl (recoverStep c inj tval) pw

private def rawSuffix (v : ℕ) (b c : ℤ) (ref : ℤ → Bool) (raw : ℕ) : ℕ :=
  (List.range 4).foldl (fun acc k => acc ||| ((trial b ref raw (c + ((v + k : ℕ) : ℤ))).toNat <<< k)) 0

private def makeOld (skip span middle outside : ℕ) : ℕ :=
  (outside % 2 ^ skip) ||| (middle <<< skip) ||| ((outside >>> skip) <<< (skip + span))

private def toOutside (w skip span raw : ℕ) : ℕ :=
  (raw % 2 ^ skip) ||| (((raw % 2 ^ w) >>> (skip + span)) <<< skip)

private def fromOutside (skip span readEnd offset predWord middle outside : ℕ) : ℕ :=
  makeOld skip span middle outside |||
    (((predWord >>> (offset + span)) % 2 ^ (readEnd - (skip + span))) <<< (skip + span))

private theorem testBit_bool_shiftLeft (b : Bool) (k i : ℕ) :
    (b.toNat <<< k).testBit i = (decide (i = k) && b) := by
  rw [Nat.testBit_shiftLeft]
  by_cases h : i = k
  · subst h; cases b <;> simp
  · by_cases hge : i ≥ k
    · have hlt : b.toNat < 2 ^ (i - k) := by
        cases b
        · exact Nat.two_pow_pos _
        · have h1 : 1 ≤ i - k := by omega
          exact Nat.lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide) h1)
      rw [Nat.testBit_lt_two_pow hlt]
      simp [h]
    · simp [h, hge]

private theorem testBit_pack (f : ℕ → Bool) (n i : ℕ) :
    ((List.range n).foldl (fun acc pos => acc ||| ((f pos).toNat <<< pos)) 0).testBit i =
      (decide (i < n) && f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Nat.testBit_or, ih, testBit_bool_shiftLeft]
    by_cases h : i = n
    · subst h; simp
    · have hlt : (i < n + 1) ↔ (i < n) := by omega
      simp [h, hlt]

private theorem pack_lt (f : ℕ → Bool) (n : ℕ) :
    (List.range n).foldl (fun acc pos => acc ||| ((f pos).toNat <<< pos)) 0 < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_pack]
  have hnot : ¬ (i < n) := by omega
  simp [hnot]

private theorem testBit_lt_of_le {x n i : ℕ} (hx : x < 2 ^ n) (hi : n ≤ i) :
    x.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))

private theorem block_eq_iff (v : ℕ) (x : ℤ → Bool) (c : ℤ) (target : Fin (2 ^ v)) :
    block v x c = target.val ↔ ∀ j < v, x (c + 1 + (j : ℤ)) = target.val.testBit j := by
  constructor
  · intro h j hj
    have hb := congrArg (fun n => n.testBit j) h
    unfold block at hb
    rw [testBit_pack] at hb
    simpa [hj] using hb
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    unfold block
    rw [testBit_pack]
    by_cases hj : j < v
    · simp [hj, h j hj]
    · rw [testBit_lt_of_le target.isLt (by omega)]
      simp [hj]

private theorem evolve_congr {x y inj : ℤ → Bool} {z : ℤ}
    (h : ∀ u : ℤ, z - 1 ≤ u → u ≤ z + 3 → x u = y u) :
    evolve x inj z = evolve y inj z := by
  unfold evolve mix
  rw [h (z - 1) (by omega) (by omega),
      h z (by omega) (by omega),
      h (z + 1) (by omega) (by omega),
      h (z + 1 - 1) (by omega) (by omega),
      h (z + 1 + 1) (by omega) (by omega),
      h (z + 2 - 1) (by omega) (by omega),
      h (z + 2) (by omega) (by omega),
      h (z + 2 + 1) (by omega) (by omega)]

private theorem bool_xor_evolve (a b c d e : Bool) :
    xor (xor (xor (xor a b) c) d) e = xor a (xor (xor (xor (xor false b) c) d) e) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

private theorem bool_xor_cancel (a b : Bool) : xor (xor a b) b = a := by
  cases a <;> cases b <;> rfl

private theorem evolve_xor_left {x y inj : ℤ → Bool} {z : ℤ}
    (hx0 : x (z - 1) = false)
    (h : ∀ u : ℤ, z ≤ u → u ≤ z + 3 → y u = x u) :
    evolve y inj z = xor (y (z - 1)) (evolve x inj z) := by
  unfold evolve mix
  rw [h z (by omega) (by omega),
      h (z + 1) (by omega) (by omega),
      h (z + 1 - 1) (by omega) (by omega),
      h (z + 1 + 1) (by omega) (by omega),
      h (z + 2 - 1) (by omega) (by omega),
      h (z + 2) (by omega) (by omega),
      h (z + 2 + 1) (by omega) (by omega),
      hx0]
  exact bool_xor_evolve _ _ _ _ _

private theorem recFold_zero (c : ℤ) (inj : ℤ → Bool) (tval pw : ℕ) :
    recFold c inj tval 0 pw = pw := rfl

private theorem recFold_succ (c : ℤ) (inj : ℤ → Bool) (tval k pw : ℕ) :
    recFold c inj tval (k + 1) pw = recFold c inj tval k (recoverStep c inj tval pw k) := by
  unfold recFold
  rw [List.range_succ, List.reverse_append]
  rfl

private theorem testBit_recoverStep_ne (c : ℤ) (inj : ℤ → Bool) (tval pw j i : ℕ) (h : i ≠ j) :
    (recoverStep c inj tval pw j).testBit i = pw.testBit i := by
  unfold recoverStep
  rw [Nat.testBit_or, testBit_bool_shiftLeft]
  simp [h]

private theorem testBit_recoverStep_eq (c : ℤ) (inj : ℤ → Bool) (tval pw j : ℕ)
    (hp : pw.testBit j = false) :
    (recoverStep c inj tval pw j).testBit j =
      xor (tval.testBit j) (evolve (fun z => pw.testBit (z - c).toNat) inj (c + 1 + (j : ℤ))) := by
  unfold recoverStep
  rw [Nat.testBit_or, testBit_bool_shiftLeft, hp]
  simp

private theorem recFold_testBit_ge (c : ℤ) (inj : ℤ → Bool) (tval : ℕ) :
    ∀ k pw i, k ≤ i → (recFold c inj tval k pw).testBit i = pw.testBit i := by
  intro k
  induction k with
  | zero => intro pw i _; rfl
  | succ k ih =>
    intro pw i hi
    rw [recFold_succ, ih _ i (by omega), testBit_recoverStep_ne _ _ _ _ _ _ (by omega)]

private theorem recFold_evolve (c : ℤ) (inj : ℤ → Bool) (tval : ℕ) :
    ∀ k pw, (∀ i < k, pw.testBit i = false) →
      ∀ j < k, evolve (fun z => (recFold c inj tval k pw).testBit (z - c).toNat) inj (c + 1 + (j : ℤ)) =
        tval.testBit j := by
  intro k
  induction k with
  | zero => intro _ _ j hj; omega
  | succ k ih =>
    intro pw hlo j hj
    rw [recFold_succ]
    let pw' := recoverStep c inj tval pw k
    have hlo' : ∀ i < k, pw'.testBit i = false := by
      intro i hi
      rw [testBit_recoverStep_ne _ _ _ _ _ _ (by omega)]
      exact hlo i (by omega)
    by_cases hjk : j < k
    · exact ih pw' hlo' j hjk
    · have hjeq : j = k := by omega
      subst hjeq
      have hidx0 : (c + 1 + (j : ℤ) - 1 - c).toNat = j := by omega
      have hx0 : pw.testBit (c + 1 + (j : ℤ) - 1 - c).toNat = false := by
        rw [hidx0]; exact hlo j (by omega)
      have hagree : ∀ u : ℤ, c + 1 + (j : ℤ) ≤ u → u ≤ c + 1 + (j : ℤ) + 3 →
          (recFold c inj tval j pw').testBit (u - c).toNat = pw.testBit (u - c).toNat := by
        intro u hu1 hu2
        have hge : j ≤ (u - c).toNat := by omega
        have hne : (u - c).toNat ≠ j := by omega
        rw [recFold_testBit_ge c inj tval j pw' _ hge,
            testBit_recoverStep_ne c inj tval pw j _ hne]
      rw [evolve_xor_left hx0 hagree, hidx0,
          recFold_testBit_ge c inj tval j pw' j (Nat.le_refl j),
          testBit_recoverStep_eq c inj tval pw j (hlo j (by omega)),
          bool_xor_cancel]

private theorem recFold_unique (c : ℤ) (inj : ℤ → Bool) (tval : ℕ) :
    ∀ (k pw N : ℕ) (x : ℤ → Bool), k + 4 ≤ N →
      (∀ i < k, pw.testBit i = false) →
      (∀ i, k ≤ i → i < N → pw.testBit i = x (c + (i : ℤ))) →
      (∀ j < k, evolve x inj (c + 1 + (j : ℤ)) = tval.testBit j) →
      ∀ i < N, (recFold c inj tval k pw).testBit i = x (c + (i : ℤ)) := by
  intro k
  induction k with
  | zero =>
    intro pw N x _ _ hhi _ i hi
    exact hhi i (Nat.zero_le i) hi
  | succ k ih =>
    intro pw N x hN hlo hhi hev i hi
    rw [recFold_succ]
    let pw' := recoverStep c inj tval pw k
    have hlo' : ∀ m < k, pw'.testBit m = false := by
      intro m hm
      rw [testBit_recoverStep_ne _ _ _ _ _ _ (by omega)]
      exact hlo m (by omega)
    have hhi' : ∀ m, k ≤ m → m < N → pw'.testBit m = x (c + (m : ℤ)) := by
      intro m hm1 hm2
      by_cases hmk : m = k
      · subst hmk
        rw [testBit_recoverStep_eq c inj tval pw m (hlo m (by omega))]
        have hidx0 : (c + 1 + (m : ℤ) - 1 - c).toNat = m := by omega
        have hx0 : pw.testBit (c + 1 + (m : ℤ) - 1 - c).toNat = false := by
          rw [hidx0]; exact hlo m (by omega)
        have hagree : ∀ u : ℤ, c + 1 + (m : ℤ) ≤ u → u ≤ c + 1 + (m : ℤ) + 3 →
            x u = pw.testBit (u - c).toNat := by
          intro u hu1 hu2
          have hu_eq : c + ((u - c).toNat : ℤ) = u := by omega
          have h1 : m + 1 ≤ (u - c).toNat := by omega
          have h2 : (u - c).toNat < N := by omega
          rw [hhi (u - c).toNat h1 h2, hu_eq]
        have hev_m : evolve x inj (c + 1 + (m : ℤ)) = tval.testBit m := hev m (by omega)
        rw [← hev_m, evolve_xor_left hx0 hagree, bool_xor_cancel]
        have hzm : c + 1 + (m : ℤ) - 1 = c + (m : ℤ) := by omega
        rw [hzm]
      · rw [testBit_recoverStep_ne c inj tval pw k m hmk]
        exact hhi m (by omega) hm2
    exact ih pw' N x (by omega) hlo' hhi' (fun j hj => hev j (by omega)) i hi

private theorem length_filter_range_add (a b : ℕ) (p : ℕ → Bool) :
    ((List.range (a + b)).filter p).length =
      ((List.range a).filter p).length + ((List.range b).filter (fun x => p (a + x))).length := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, List.range_succ, List.filter_append, List.length_append, ih,
        List.range_succ, List.filter_append, List.length_append]
    cases hp : p (a + b) <;> simp [hp, Nat.add_assoc]

private theorem length_filter_range_two_pow_add (L k : ℕ) (p : ℕ → Bool)
    (hp : ∀ x, p x = p (x % 2 ^ L)) :
    ((List.range (2 ^ (L + k))).filter p).length =
      2 ^ k * ((List.range (2 ^ L)).filter p).length := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpow : 2 ^ (L + (k + 1)) = 2 ^ (L + k) + 2 ^ (L + k) := by
      rw [show L + (k + 1) = (L + k) + 1 by omega, Nat.pow_succ]
      omega
    rw [hpow, length_filter_range_add]
    have hshift : (fun x => p (2 ^ (L + k) + x)) = p := by
      funext x
      rw [hp (2 ^ (L + k) + x), hp x, Nat.pow_add, Nat.mul_add_mod]
    rw [hshift, ih, Nat.pow_succ]
    have hmul : 2 ^ k * 2 * ((List.range (2 ^ L)).filter p).length =
        2 ^ k * ((List.range (2 ^ L)).filter p).length +
          2 ^ k * ((List.range (2 ^ L)).filter p).length := by
      rw [Nat.mul_right_comm, Nat.mul_two]
    exact hmul.symm

private theorem sum_map_zero (K : ℕ) : ((List.range K).map (fun _ => 0)).sum = 0 := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    rfl

private theorem sum_map_ite_add (K t : ℕ) (ht : t < K) (g : ℕ → ℕ) :
    ((List.range K).map (fun s => if t == s then g s + 1 else g s)).sum =
      ((List.range K).map g).sum + 1 := by
  induction K with
  | zero => omega
  | succ K ih =>
    rw [List.range_succ, List.map_append, List.sum_append,
        List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases h : t = K
    · subst h
      have hneq : (List.range t).map (fun s => if t == s then g s + 1 else g s) =
          (List.range t).map g := by
        apply List.map_congr_left
        intro s hs
        have hlt : s < t := List.mem_range.mp hs
        have hne : (t == s) = false := beq_false_of_ne (by omega)
        simp [hne]
      rw [hneq]
      simp [Nat.add_assoc]
    · have hlt : t < K := by omega
      have hne : (t == K) = false := beq_false_of_ne h
      rw [ih hlt]
      simp [hne]
      omega

private theorem length_filter_eq_sum_range {α : Type} (l : List α) (p : α → Bool)
    (f : α → ℕ) (K : ℕ) (hf : ∀ a ∈ l, f a < K) :
    (l.filter p).length =
      ((List.range K).map (fun s => (l.filter (fun a => p a && (f a == s))).length)).sum := by
  induction l with
  | nil =>
    simp [sum_map_zero]
  | cons a tl ih =>
    have hfa : f a < K := hf a (by simp)
    have hftl : ∀ x ∈ tl, f x < K := fun x hx => hf x (by simp [hx])
    cases hpa : p a
    · have hcongr : (List.range K).map (fun s => ((a :: tl).filter (fun x => p x && (f x == s))).length) =
          (List.range K).map (fun s => (tl.filter (fun x => p x && (f x == s))).length) := by
        apply List.map_congr_left
        intro s _
        simp [hpa]
      rw [List.filter_cons, hpa, hcongr]
      exact ih hftl
    · have hcongr : (List.range K).map (fun s => ((a :: tl).filter (fun x => p x && (f x == s))).length) =
          (List.range K).map (fun s =>
            if f a == s then (tl.filter (fun x => p x && (f x == s))).length + 1
            else (tl.filter (fun x => p x && (f x == s))).length) := by
        apply List.map_congr_left
        intro s _
        cases hfs : (f a == s) <;> simp [hpa, hfs]
      rw [hcongr]
      simp only [List.filter_cons, hpa, ↓reduceIte, List.length_cons]
      rw [sum_map_ite_add K (f a) hfa, ih hftl]

private theorem nodup_map_of_inj {α β : Type} {f : α → β} :
    ∀ {l : List α}, l.Nodup → (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: t, hnd, hinj => by
    rw [List.map_cons, List.nodup_cons]
    have hnd_a := List.nodup_cons.mp hnd
    constructor
    · intro hmem
      rw [List.mem_map] at hmem
      rcases hmem with ⟨x, hx, hfx⟩
      have hax : a = x := hinj a (by simp) x (by simp [hx]) hfx.symm
      exact hnd_a.1 (hax ▸ hx)
    · exact nodup_map_of_inj hnd_a.2 (fun x hx y hy => hinj x (by simp [hx]) y (by simp [hy]))

private theorem nodup_length_le_of_subset {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {l1 l2 : List α}, l1.Nodup → (∀ x ∈ l1, x ∈ l2) → l1.length ≤ l2.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, l2, hnd, hsub => by
    have ha : a ∈ l2 := hsub a (by simp)
    have hnd_a := List.nodup_cons.mp hnd
    have hsub' : ∀ x ∈ t, x ∈ l2.erase a := fun x hx =>
      (List.mem_erase_of_ne (fun (h : x = a) => hnd_a.1 (h ▸ hx))).mpr (hsub x (by simp [hx]))
    have ih := nodup_length_le_of_subset hnd_a.2 hsub'
    have her : (l2.erase a).length + 1 = l2.length := by
      rw [List.length_erase_of_mem ha]
      exact Nat.sub_add_cancel (List.length_pos_of_mem ha)
    simp only [List.length_cons]
    omega

private theorem length_filter_range_le_of_inj {M N : ℕ} {p q : ℕ → Bool}
    (f g : ℕ → ℕ)
    (hf_lt : ∀ a < M, p a = true → f a < N)
    (hf_q : ∀ a < M, p a = true → q (f a) = true)
    (hfg : ∀ a < M, p a = true → g (f a) = a) :
    ((List.range M).filter p).length ≤ ((List.range N).filter q).length := by
  have hlen : (((List.range M).filter p).map f).length = ((List.range M).filter p).length :=
    List.length_map ..
  rw [← hlen]
  apply nodup_length_le_of_subset
  · apply nodup_map_of_inj (List.nodup_range.filter p)
    intro x hx y hy hxy
    rw [List.mem_filter, List.mem_range] at hx hy
    calc x = g (f x) := (hfg x hx.1 hx.2).symm
      _ = g (f y) := congrArg g hxy
      _ = y := hfg y hy.1 hy.2
  · intro b hb
    rw [List.mem_map] at hb
    rcases hb with ⟨a, ha, rfl⟩
    rw [List.mem_filter, List.mem_range] at ha ⊢
    exact ⟨hf_lt a ha.1 ha.2, hf_q a ha.1 ha.2⟩

private theorem length_filter_range_eq_of_bij {M N : ℕ} {p q : ℕ → Bool}
    (f g : ℕ → ℕ)
    (hf_lt : ∀ a < M, p a = true → f a < N)
    (hf_q : ∀ a < M, p a = true → q (f a) = true)
    (hg_lt : ∀ b < N, q b = true → g b < M)
    (hg_p : ∀ b < N, q b = true → p (g b) = true)
    (hfg : ∀ a < M, p a = true → g (f a) = a)
    (hgf : ∀ b < N, q b = true → f (g b) = b) :
    ((List.range M).filter p).length = ((List.range N).filter q).length :=
  Nat.le_antisymm
    (length_filter_range_le_of_inj f g hf_lt hf_q hfg)
    (length_filter_range_le_of_inj g f hg_lt hg_p hgf)

private theorem getD_toArray_map_range (n : ℕ) (f : ℕ → ℕ) (i d : ℕ) (hi : i < n) :
    (((List.range n).map f).toArray).getD i d = f i := by
  simp [Array.getD, hi]

private theorem testBit_makeOld_lt_skip {skip span middle outside i : ℕ} (hi : i < skip) :
    (makeOld skip span middle outside).testBit i = outside.testBit i := by
  unfold makeOld
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_mod_two_pow,
      Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
  have h1 : ¬ (i ≥ skip) := by omega
  have h2 : ¬ (i ≥ skip + span) := by omega
  simp [hi, h1, h2]

private theorem testBit_makeOld_mid {skip span middle outside i : ℕ}
    (hi1 : skip ≤ i) (hi2 : i < skip + span) :
    (makeOld skip span middle outside).testBit i = middle.testBit (i - skip) := by
  unfold makeOld
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_mod_two_pow,
      Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
  have h1 : ¬ (i < skip) := by omega
  have h2 : ¬ (i ≥ skip + span) := by omega
  simp [h1, hi1, h2]

private theorem testBit_makeOld_hi {skip span middle outside i : ℕ}
    (hm : middle < 2 ^ span) (hi1 : skip + span ≤ i) :
    (makeOld skip span middle outside).testBit i = outside.testBit (i - span) := by
  unfold makeOld
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_mod_two_pow,
      Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have h1 : ¬ (i < skip) := by omega
  have hm0 : middle.testBit (i - skip) = false := testBit_lt_of_le hm (by omega)
  have hidx : skip + (i - (skip + span)) = i - span := by omega
  simp [h1, hm0, hi1, hidx]

private theorem testBit_makeOld_ge_w {w skip span middle outside i : ℕ}
    (hss : skip + span ≤ w) (hm : middle < 2 ^ span) (ho : outside < 2 ^ (w - span)) (hi : w ≤ i) :
    (makeOld skip span middle outside).testBit i = false := by
  unfold makeOld
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_mod_two_pow,
      Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have h1 : ¬ (i < skip) := by omega
  have hm0 : middle.testBit (i - skip) = false := testBit_lt_of_le hm (by omega)
  have ho0 : outside.testBit (skip + (i - (skip + span))) = false :=
    testBit_lt_of_le ho (by omega)
  simp [h1, hm0, ho0]

private theorem makeOld_lt {w skip span middle outside : ℕ}
    (hss : skip + span ≤ w) (hm : middle < 2 ^ span) (ho : outside < 2 ^ (w - span)) :
    makeOld skip span middle outside < 2 ^ w :=
  Nat.lt_pow_two_of_testBit _ (fun _ hi => testBit_makeOld_ge_w hss hm ho hi)

private theorem testBit_toOutside_lt_skip {w skip span raw j : ℕ} (hj : j < skip) :
    (toOutside w skip span raw).testBit j = raw.testBit j := by
  unfold toOutside
  rw [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  have h1 : ¬ (j ≥ skip) := by omega
  simp [hj, h1]

private theorem testBit_toOutside_mid {w skip span raw j : ℕ}
    (hj1 : skip ≤ j) (hj2 : j < w - span) :
    (toOutside w skip span raw).testBit j = raw.testBit (j + span) := by
  unfold toOutside
  rw [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
      Nat.testBit_shiftRight, Nat.testBit_mod_two_pow]
  have h1 : ¬ (j < skip) := by omega
  have hidx : skip + span + (j - skip) = j + span := by omega
  have hw : j + span < w := by omega
  simp [h1, hj1, hidx, hw]

private theorem testBit_toOutside_ge {w skip span raw j : ℕ}
    (hss : skip + span ≤ w) (hj : w - span ≤ j) :
    (toOutside w skip span raw).testBit j = false := by
  unfold toOutside
  rw [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
      Nat.testBit_shiftRight, Nat.testBit_mod_two_pow]
  have h1 : ¬ (j < skip) := by omega
  have h2 : ¬ (skip + span + (j - skip) < w) := by omega
  simp [h1, h2]

private theorem toOutside_lt {w skip span raw : ℕ} (hss : skip + span ≤ w) :
    toOutside w skip span raw < 2 ^ (w - span) :=
  Nat.lt_pow_two_of_testBit _ (fun _ hj => testBit_toOutside_ge hss hj)

private theorem toOutside_mod_w {w skip span raw : ℕ} (hsw : skip ≤ w) :
    toOutside w skip span (raw % 2 ^ w) = toOutside w skip span raw := by
  apply Nat.eq_of_testBit_eq
  intro j
  unfold toOutside
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
      Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
      Nat.testBit_shiftRight, Nat.testBit_shiftRight,
      Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hj : j < skip
  · have hltw : j < w := by omega
    have hge : ¬ (j ≥ skip) := by omega
    simp [hj, hltw, hge]
  · simp only [hj, decide_false, Bool.false_and, Bool.false_or]
    cases decide (skip + span + (j - skip) < w) <;> simp

private theorem makeOld_toOutside {w skip span middle raw : ℕ}
    (hss : skip + span ≤ w) (hm : middle < 2 ^ span)
    (hmid : ∀ i, skip ≤ i → i < skip + span → raw.testBit i = middle.testBit (i - skip)) :
    makeOld skip span middle (toOutside w skip span raw) = raw % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow]
  by_cases h1 : i < skip
  · rw [testBit_makeOld_lt_skip h1, testBit_toOutside_lt_skip h1]
    have hltw : i < w := by omega
    simp [hltw]
  · by_cases h2 : i < skip + span
    · rw [testBit_makeOld_mid (by omega) h2, ← hmid i (by omega) h2]
      have hltw : i < w := by omega
      simp [hltw]
    · by_cases h3 : i < w
      · rw [testBit_makeOld_hi hm (by omega),
            testBit_toOutside_mid (by omega) (by omega)]
        have hidx : i - span + span = i := by omega
        simp [h3, hidx]
      · rw [testBit_makeOld_ge_w hss hm (toOutside_lt hss) (by omega)]
        simp [h3]

private theorem fromOutside_lt {w skip span readEnd offset predWord middle outside : ℕ}
    (hss : skip + span = min w readEnd) (hm : middle < 2 ^ span) (ho : outside < 2 ^ (w - span)) :
    fromOutside skip span readEnd offset predWord middle outside < 2 ^ (max w readEnd) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  unfold fromOutside
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow]
  have h1 : (makeOld skip span middle outside).testBit i = false :=
    testBit_makeOld_ge_w (by omega) hm ho (by omega)
  have h2 : ¬ (i - (skip + span) < readEnd - (skip + span)) := by omega
  simp [h1, h2]

private theorem fromOutside_mod_w {w skip span readEnd offset predWord middle outside : ℕ}
    (hss : skip + span = min w readEnd) (hm : middle < 2 ^ span) (ho : outside < 2 ^ (w - span)) :
    fromOutside skip span readEnd offset predWord middle outside % 2 ^ w =
      makeOld skip span middle outside := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow]
  by_cases hi : i < w
  · unfold fromOutside
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow]
    by_cases h1 : i < skip + span
    · have hge : ¬ (i ≥ skip + span) := by omega
      simp [hi, hge]
    · have h2 : ¬ (i - (skip + span) < readEnd - (skip + span)) := by omega
      simp [hi, h2]
  · rw [testBit_makeOld_ge_w (by omega) hm ho (by omega)]
    simp [hi]

private theorem fromOutside_match_pred {w skip span readEnd offset predWord outside : ℕ}
    (hss : skip + span = min w readEnd) (ho : outside < 2 ^ (w - span)) :
    let middle := (predWord >>> offset) % 2 ^ span
    ∀ i, skip ≤ i → i < readEnd →
      (fromOutside skip span readEnd offset predWord middle outside).testBit i =
        predWord.testBit (offset + (i - skip)) := by
  intro middle i hi1 hi2
  have hm : middle < 2 ^ span := Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold fromOutside
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases h1 : i < skip + span
  · rw [testBit_makeOld_mid hi1 h1]
    have hge : ¬ (i ≥ skip + span) := by omega
    have hlt : i - skip < span := by omega
    simp only [hge, decide_false, Bool.false_and, Bool.or_false]
    dsimp only [middle]
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    simp [hlt]
  · have hwi : w ≤ i := by omega
    rw [testBit_makeOld_ge_w (by omega) hm ho hwi]
    have hge : i ≥ skip + span := by omega
    have hlt : i - (skip + span) < readEnd - (skip + span) := by omega
    have hidx : offset + span + (i - (skip + span)) = offset + (i - skip) := by omega
    simp [hge, hlt, hidx]

private theorem toOutside_fromOutside {w skip span readEnd offset predWord middle outside : ℕ}
    (hss : skip + span = min w readEnd) (hm : middle < 2 ^ span) (ho : outside < 2 ^ (w - span)) :
    toOutside w skip span (fromOutside skip span readEnd offset predWord middle outside) = outside := by
  rw [← toOutside_mod_w (by omega), fromOutside_mod_w hss hm ho]
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases h1 : j < skip
  · rw [testBit_toOutside_lt_skip h1, testBit_makeOld_lt_skip h1]
  · by_cases h2 : j < w - span
    · rw [testBit_toOutside_mid (by omega) h2,
          testBit_makeOld_hi hm (by omega)]
      have hidx : j + span - span = j := by omega
      rw [hidx]
    · rw [testBit_toOutside_ge (by omega) (by omega), testBit_lt_of_le ho (by omega)]

private theorem fromOutside_toOutside {w skip span readEnd offset predWord raw : ℕ}
    (hss : skip + span = min w readEnd) (hraw : raw < 2 ^ (max w readEnd))
    (hmatch : ∀ i, skip ≤ i → i < readEnd → raw.testBit i = predWord.testBit (offset + (i - skip))) :
    let middle := (predWord >>> offset) % 2 ^ span
    fromOutside skip span readEnd offset predWord middle (toOutside w skip span raw) = raw := by
  intro middle
  have hm : middle < 2 ^ span := Nat.mod_lt _ (Nat.two_pow_pos _)
  have ho : toOutside w skip span raw < 2 ^ (w - span) := toOutside_lt (by omega)
  have hmid : ∀ i, skip ≤ i → i < skip + span → raw.testBit i = middle.testBit (i - skip) := by
    intro i hi1 hi2
    rw [hmatch i hi1 (by omega)]
    dsimp only [middle]
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    have hlt : i - skip < span := by omega
    simp [hlt]
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h1 : i < w
  · have hmod := congrArg (fun n => n.testBit i) (fromOutside_mod_w (predWord := predWord) (offset := offset) hss hm ho)
    rw [Nat.testBit_mod_two_pow, makeOld_toOutside (by omega) hm hmid, Nat.testBit_mod_two_pow] at hmod
    simpa [h1] using hmod
  · by_cases h2 : i < readEnd
    · rw [fromOutside_match_pred hss ho i (by omega) h2, hmatch i (by omega) h2]
    · rw [testBit_lt_of_le (fromOutside_lt hss hm ho) (by omega),
          testBit_lt_of_le hraw (by omega)]

private theorem rawSuffix_lt (v : ℕ) (b c : ℤ) (ref : ℤ → Bool) (raw : ℕ) :
    rawSuffix v b c ref raw < 16 :=
  pack_lt (fun k => trial b ref raw (c + ((v + k : ℕ) : ℤ))) 4

private theorem testBit_rawSuffix (v : ℕ) (b c : ℤ) (ref : ℤ → Bool) (raw k : ℕ) (hk : k < 4) :
    (rawSuffix v b c ref raw).testBit k = trial b ref raw (c + ((v + k : ℕ) : ℤ)) := by
  unfold rawSuffix
  rw [testBit_pack]
  simp [hk]

private theorem mod_two_pow_mod {w L raw : ℕ} (hwL : w ≤ L) :
    (raw % 2 ^ L) % 2 ^ w = raw % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases h : i < w
  · have hL : i < L := by omega
    simp [h, hL]
  · simp [h]

private theorem main_proof :
    ∀ (w v m : ℕ) (b c : ℤ) (ref inj : ℤ → Bool) (mask : ℕ),
      b - 3 ≤ c → c ≤ b + (w : ℤ) + 1 → w ≤ m → c + (v : ℤ) + 3 ≤ b + (m : ℤ) →
      let skip := (c - b - 1).toNat
      let readEnd := (c + (v : ℤ) + 3 - b).toNat
      let span := min w readEnd - skip
      let hist := ((List.range (2 ^ span)).map (fun middle =>
        ((List.range (2 ^ (w - span))).filter (fun outside =>
          let old := (outside % 2 ^ skip) ||| (middle <<< skip) |||
            ((outside >>> skip) <<< (skip + span))
          mask.testBit old)).length)).toArray
      ∀ target : Fin (2 ^ v),
        let recover := fun (suffix : ℕ) =>
          recFold c inj target.val v (suffix <<< v)
        let price := fun (suffix : ℕ) =>
          let predWord := recover suffix
          let prefixOK := (List.range (v + 4)).all (fun coord =>
            let z := c + (coord : ℤ)
            decide (b < z) || (predWord.testBit coord == ref z))
          let offset := (b + 1 + (skip : ℤ) - c).toNat
          let middle := (predWord >>> offset) % 2 ^ span
          if prefixOK then hist.getD middle 0 else 0
        ((List.range (2 ^ m)).filter (fun raw =>
          mask.testBit (raw % 2 ^ w) && (block v (evolve (trial b ref raw) inj) c == target.val))).length =
          2 ^ (m - max w readEnd) * ((List.range 16).map price).sum := by
  intro w v m b c ref inj mask hc1 hc2 hwm hcm skip readEnd span hist target recover price
  let L := max w readEnd
  let offset := (b + 1 + (skip : ℤ) - c).toNat
  have hreadEnd_le_m : readEnd ≤ m := by dsimp only [readEnd]; omega
  have hL_le_m : L ≤ m := by dsimp only [L]; omega
  have hskip_le_w : skip ≤ w := by dsimp only [skip]; omega
  have hoff_le : offset ≤ 4 := by dsimp only [offset, skip]; omega
  have hcoord_eq : c + (offset : ℤ) = b + 1 + (skip : ℤ) := by dsimp only [offset, skip]; omega
  have hreadEnd_eq : readEnd = skip + (v + 4 - offset) := by dsimp only [readEnd, offset, skip]; omega
  have hskip_le_readEnd : skip ≤ readEnd := by omega
  have hss : skip + span = min w readEnd := by dsimp only [span]; omega
  have hsite_gt : ∀ coord : ℕ, b < c + (coord : ℤ) ↔ offset ≤ coord := by
    intro coord; dsimp only [offset, skip]; omega
  have hsite_idx : ∀ coord : ℕ, offset ≤ coord →
      (c + (coord : ℤ) - b - 1).toNat = skip + (coord - offset) := by
    intro coord h; dsimp only [offset, skip] at h ⊢; omega
  let P : ℕ → Bool := fun raw =>
    mask.testBit (raw % 2 ^ w) && (block v (evolve (trial b ref raw) inj) c == target.val)
  have hP_mod : ∀ raw, P raw = P (raw % 2 ^ L) := by
    intro raw
    dsimp only [P]
    rw [mod_two_pow_mod (show w ≤ L by dsimp only [L]; omega)]
    have hblk : block v (evolve (trial b ref raw) inj) c =
        block v (evolve (trial b ref (raw % 2 ^ L)) inj) c := by
      apply Nat.eq_of_testBit_eq
      intro j
      unfold block
      rw [testBit_pack, testBit_pack]
      by_cases hj : j < v
      · simp only [hj, decide_true, Bool.true_and]
        apply evolve_congr
        intro u hu1 hu2
        unfold trial
        by_cases hub : u ≤ b
        · simp [hub]
        · simp only [hub, ↓reduceIte]
          rw [Nat.testBit_mod_two_pow]
          have hult : (u - b - 1).toNat < L := by
            have : (u - b - 1).toNat < readEnd := by dsimp only [readEnd]; omega
            dsimp only [L]; omega
          simp only [hult, decide_true, Bool.true_and]
      · simp [hj]
    rw [hblk]
  have hm_eq : m = L + (m - L) := by omega
  have hstep1 : ((List.range (2 ^ m)).filter P).length =
      2 ^ (m - L) * ((List.range (2 ^ L)).filter P).length := by
    have h := length_filter_range_two_pow_add L (m - L) P hP_mod
    rw [← hm_eq] at h
    exact h
  change ((List.range (2 ^ m)).filter P).length = 2 ^ (m - L) * ((List.range 16).map price).sum
  rw [hstep1]
  apply congrArg (2 ^ (m - L) * ·)
  rw [length_filter_eq_sum_range (List.range (2 ^ L)) P (rawSuffix v b c ref) 16
        (fun raw _ => rawSuffix_lt v b c ref raw)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro suffix hsuf
  have hsuf_lt : suffix < 16 := List.mem_range.mp hsuf
  let predWord := recover suffix
  let prefixOK := (List.range (v + 4)).all (fun coord =>
    let z := c + (coord : ℤ)
    decide (b < z) || (predWord.testBit coord == ref z))
  let middle := (predWord >>> offset) % 2 ^ span
  have hshift_lo : ∀ i < v, (suffix <<< v).testBit i = false := by
    intro i hi
    rw [Nat.testBit_shiftLeft]
    have hge : ¬ (i ≥ v) := by omega
    simp [hge]
  have hrec_hi : ∀ k < 4, predWord.testBit (v + k) = suffix.testBit k := by
    intro k hk
    dsimp only [predWord, recover]
    rw [recFold_testBit_ge c inj target.val v (suffix <<< v) (v + k) (by omega),
        Nat.testBit_shiftLeft]
    have hge : v + k ≥ v := by omega
    have hsub : v + k - v = k := by omega
    simp [hge, hsub]
  have hrec_ev : ∀ j < v,
      evolve (fun z => predWord.testBit (z - c).toNat) inj (c + 1 + (j : ℤ)) = target.val.testBit j :=
    recFold_evolve c inj target.val v (suffix <<< v) hshift_lo
  have hchar : ∀ raw,
      (P raw && (rawSuffix v b c ref raw == suffix)) = true ↔
        (mask.testBit (raw % 2 ^ w) = true ∧
          ∀ coord < v + 4, predWord.testBit coord = trial b ref raw (c + (coord : ℤ))) := by
    intro raw
    dsimp only [P]
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, block_eq_iff]
    constructor
    · rintro ⟨⟨hmask, hev⟩, hsuf_eq⟩
      refine ⟨hmask, ?_⟩
      apply recFold_unique c inj target.val v (suffix <<< v) (v + 4) (trial b ref raw)
        (Nat.le_refl _) hshift_lo
      · intro i hi1 hi2
        rw [Nat.testBit_shiftLeft]
        have hge : i ≥ v := by omega
        have hlt4 : i - v < 4 := by omega
        simp only [hge, decide_true, Bool.true_and]
        rw [← hsuf_eq, testBit_rawSuffix v b c ref raw (i - v) hlt4]
        have hvi : v + (i - v) = i := by omega
        rw [hvi]
      · exact hev
    · rintro ⟨hmask, hwin⟩
      refine ⟨⟨hmask, ?_⟩, ?_⟩
      · intro j hj
        rw [← hrec_ev j hj]
        apply evolve_congr
        intro u hu1 hu2
        have hu_lt : (u - c).toNat < v + 4 := by omega
        have hu_eq : c + ((u - c).toNat : ℤ) = u := by omega
        rw [hwin (u - c).toNat hu_lt, hu_eq]
      · apply Nat.eq_of_testBit_eq
        intro k
        by_cases hk : k < 4
        · rw [testBit_rawSuffix v b c ref raw k hk, ← hwin (v + k) (by omega), hrec_hi k hk]
        · rw [testBit_lt_of_le (n := 4) (rawSuffix_lt v b c ref raw) (by omega),
              testBit_lt_of_le (n := 4) hsuf_lt (by omega)]
  dsimp only [price]
  change ((List.range (2 ^ L)).filter (fun raw => P raw && (rawSuffix v b c ref raw == suffix))).length =
    if prefixOK then hist.getD middle 0 else 0
  cases hpre : prefixOK
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hall_false : ∀ raw ∈ (List.range (2 ^ L)),
        (P raw && (rawSuffix v b c ref raw == suffix)) = false := by
      intro raw _
      cases hq : (P raw && (rawSuffix v b c ref raw == suffix))
      · rfl
      · exfalso
        have hwin := ((hchar raw).mp hq).2
        have htrue : prefixOK = true := by
          dsimp only [prefixOK]
          rw [List.all_eq_true]
          intro coord hcoord
          have hclt : coord < v + 4 := List.mem_range.mp hcoord
          by_cases hgt : b < c + (coord : ℤ)
          · simp [hgt]
          · have hle : c + (coord : ℤ) ≤ b := by omega
            have htw : trial b ref raw (c + (coord : ℤ)) = ref (c + (coord : ℤ)) := by
              unfold trial; simp [hle]
            rw [hwin coord hclt, htw]
            simp
        rw [hpre] at htrue
        exact Bool.noConfusion htrue
    have hempty : (List.range (2 ^ L)).filter (fun raw => P raw && (rawSuffix v b c ref raw == suffix)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro raw hraw
      rw [hall_false raw hraw]
      exact Bool.noConfusion
    rw [hempty]
    rfl
  · simp only [↓reduceIte]
    have hmid_lt : middle < 2 ^ span := Nat.mod_lt _ (Nat.two_pow_pos _)
    dsimp only [hist]
    rw [getD_toArray_map_range (2 ^ span) _ middle 0 hmid_lt]
    have hpre_ok : ∀ coord < v + 4, c + (coord : ℤ) ≤ b → predWord.testBit coord = ref (c + (coord : ℤ)) := by
      intro coord hclt hle
      dsimp only [prefixOK] at hpre
      rw [List.all_eq_true] at hpre
      have hc := hpre coord (List.mem_range.mpr hclt)
      have hngt : ¬ (b < c + (coord : ℤ)) := by omega
      simp [hngt] at hc
      exact hc
    have hwin_iff : ∀ raw,
        (∀ coord < v + 4, predWord.testBit coord = trial b ref raw (c + (coord : ℤ))) ↔
          (∀ i, skip ≤ i → i < readEnd → raw.testBit i = predWord.testBit (offset + (i - skip))) := by
      intro raw
      constructor
      · intro hwin i hi1 hi2
        let coord := offset + (i - skip)
        have hclt : coord < v + 4 := by dsimp only [coord]; omega
        have hgt : b < c + (coord : ℤ) := (hsite_gt coord).mpr (by dsimp only [coord]; omega)
        have hnle : ¬ (c + (coord : ℤ) ≤ b) := by omega
        have hidx : (c + (coord : ℤ) - b - 1).toNat = i := by
          rw [hsite_idx coord (by dsimp only [coord]; omega)]
          dsimp only [coord]; omega
        have hw := hwin coord hclt
        unfold trial at hw
        simp only [hnle, ↓reduceIte, hidx] at hw
        exact hw.symm
      · intro hbits coord hclt
        by_cases hgt : b < c + (coord : ℤ)
        · have hoffc : offset ≤ coord := (hsite_gt coord).mp hgt
          have hnle : ¬ (c + (coord : ℤ) ≤ b) := by omega
          unfold trial
          simp only [hnle, ↓reduceIte, hsite_idx coord hoffc]
          have hi1 : skip ≤ skip + (coord - offset) := by omega
          have hi2 : skip + (coord - offset) < readEnd := by omega
          have hb := hbits (skip + (coord - offset)) hi1 hi2
          have hco : offset + (skip + (coord - offset) - skip) = coord := by omega
          rw [hco] at hb
          exact hb.symm
        · have hle : c + (coord : ℤ) ≤ b := by omega
          unfold trial
          simp only [hle, ↓reduceIte]
          exact hpre_ok coord hclt hle
    apply length_filter_range_eq_of_bij
      (toOutside w skip span)
      (fromOutside skip span readEnd offset predWord middle)
    · intro raw _ _
      exact toOutside_lt (by omega)
    · intro raw _ hraw
      rcases (hchar raw).mp hraw with ⟨hmask, hwin⟩
      have hbits := (hwin_iff raw).mp hwin
      have hmid_eq : ∀ i, skip ≤ i → i < skip + span → raw.testBit i = middle.testBit (i - skip) := by
        intro i hi1 hi2
        rw [hbits i hi1 (by omega)]
        dsimp only [middle]
        rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
        have hlt : i - skip < span := by omega
        simp [hlt]
      change mask.testBit (makeOld skip span middle (toOutside w skip span raw)) = true
      rw [makeOld_toOutside (by omega) hmid_lt hmid_eq]
      exact hmask
    · intro outside hout _
      exact fromOutside_lt hss hmid_lt hout
    · intro outside hout hmask
      rw [hchar]
      refine ⟨?_, ?_⟩
      · rw [fromOutside_mod_w hss hmid_lt hout]
        exact hmask
      · rw [hwin_iff]
        exact fromOutside_match_pred hss hout
    · intro raw hraw_lt hraw
      rcases (hchar raw).mp hraw with ⟨_, hwin⟩
      exact fromOutside_toOutside hss hraw_lt ((hwin_iff raw).mp hwin)
    · intro outside hout _
      exact toOutside_fromOutside hss hmid_lt hout

end PEqualNP.Outside.L_meta_25597

theorem PEqualNP.Outside.L_meta_25597 : let mix := fun (x : ℤ → Bool) (z : ℤ) => xor (xor (x (z-1)) (x z)) (x (z+1))
let evolve := fun (x inj : ℤ → Bool) (z : ℤ) =>
  xor (xor (mix x z) (!(mix x (z+1)) && mix x (z+2))) (inj z)
let block := fun (v : ℕ) (x : ℤ → Bool) (c : ℤ) =>
  (List.range v).foldl (fun (acc pos : ℕ) => acc ||| ((x (c+1+(pos : ℤ))).toNat <<< pos)) 0
∀ (w v m : ℕ) (b c : ℤ) (ref inj : ℤ → Bool) (mask : ℕ),
  b-3 ≤ c → c ≤ b+(w : ℤ)+1 → w ≤ m → c+(v : ℤ)+3 ≤ b+(m : ℤ) →
  let skip := (c-b-1).toNat
  let readEnd := (c+(v : ℤ)+3-b).toNat
  let span := min w readEnd - skip
  let hist := ((List.range (2^span)).map (fun middle =>
    ((List.range (2^(w-span))).filter (fun outside =>
      let old := (outside % 2^skip) ||| (middle <<< skip) |||
        ((outside >>> skip) <<< (skip+span))
      mask.testBit old)).length)).toArray
  let trial := fun (tailBits : ℕ) (site : ℤ) =>
    if site ≤ b then ref site else tailBits.testBit (site-b-1).toNat
  ∀ target : Fin (2^v),
    let recover := fun (suffix : ℕ) =>
      ((List.range v).reverse).foldl (fun (partialWord j : ℕ) =>
        let jz := c+1+(j : ℤ)
        let bits := fun (z : ℤ) => partialWord.testBit (z-c).toNat
        let chosen := xor (target.val.testBit j) (evolve bits inj jz)
        partialWord ||| (chosen.toNat <<< j)) (suffix <<< v)
    let price := fun (suffix : ℕ) =>
      let predWord := recover suffix
      let prefixOK := (List.range (v+4)).all (fun coord =>
        let z := c+(coord : ℤ)
        decide (b < z) || (predWord.testBit coord == ref z))
      let offset := (b+1+(skip : ℤ)-c).toNat
      let middle := (predWord >>> offset) % 2^span
      if prefixOK then hist.getD middle 0 else 0
    ((List.range (2^m)).filter (fun raw =>
      mask.testBit (raw % 2^w) && (block v (evolve (trial raw) inj) c == target.val))).length =
      2^(m - max w readEnd) * ((List.range 16).map price).sum :=
  PEqualNP.Outside.L_meta_25597.main_proof
