import Mathlib.Data.Finset.Card

namespace PEqualNP.Outside.L_meta_39005

def chiB (a b c : Bool) : Bool :=
  xor a (!b && c)

def tap (k start x j back : Nat) : Bool :=
  x.testBit ((start + j + k - back) % k)

def pulse (k start : Nat) (col : Bool) (x j : Nat) : Bool :=
  if col then xor (tap k start x j 1) (xor (tap k start x j 3) (tap k start x j 5))
  else xor (tap k start x j 0) (xor (tap k start x j 1) (tap k start x j 2))

def chiFn (bits : Nat → Bool) (j : Nat) : Bool :=
  xor (bits j) (!(bits (j + 1)) && bits (j + 2))

def fiber (h : Nat) (z : Fin h → Bool) : Set Nat :=
  {u : Nat | u < 2 ^ (h + 2) ∧ ∀ j : Fin h, chiFn (fun i => u.testBit i) j = z j}

def tail (h k start : Nat) (col : Bool) (x len u : Nat) : Finset Nat :=
  (Finset.range len).filter (fun j =>
    chiFn (fun i => xor (u.testBit i) (pulse k start col x i)) (h - len + j))

def ok (h k start x : Nat) (r c : Fin h → Bool) : Prop :=
  Set.InjOn (tail h k start false x 5) (fiber h r) ∧
    Set.InjOn (tail h k start true x 4) (fiber h c)

def runTrace (n h : Nat) (ask : List Bool → Option (Fin n × Bool × Fin h))
    (r c : Fin n → Fin h → Bool) (q : Nat) : List Bool :=
  (List.range q).foldl (fun (hist : List Bool) _ =>
    let bit := ((ask hist).map (fun u =>
      if u.2.1 then c u.1 u.2.2 else r u.1 u.2.2)).getD false
    bit :: hist) []

lemma runTrace_succ (n h : Nat) (ask : List Bool → Option (Fin n × Bool × Fin h))
    (r c : Fin n → Fin h → Bool) (m : Nat) :
    runTrace n h ask r c (m + 1) =
      (((ask (runTrace n h ask r c m)).map (fun u =>
        if u.2.1 then c u.1 u.2.2 else r u.1 u.2.2)).getD false) ::
        runTrace n h ask r c m := by
  unfold runTrace
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

def packBits : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, f => packBits n f ||| ((f n).toNat <<< n)

lemma packBits_lt (n : Nat) (f : Nat → Bool) : packBits n f < 2 ^ n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih =>
    unfold packBits
    have h1 : packBits n f < 2 ^ (n + 1) :=
      Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by omega) (Nat.le_succ n))
    have h2 : (f n).toNat <<< n < 2 ^ (n + 1) := by
      cases f n
      · simp [Nat.two_pow_pos]
      · rw [Bool.toNat_true, Nat.shiftLeft_eq, Nat.one_mul]
        exact Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self n)
    exact Nat.or_lt_two_pow h1 h2

lemma testBit_packBits (n : Nat) (f : Nat → Bool) (i : Nat) :
    (packBits n f).testBit i = (decide (i < n) && f i) := by
  induction n with
  | zero => simp [packBits]
  | succ n ih =>
    unfold packBits
    rw [Nat.testBit_or, ih]
    cases hf : f n
    · simp only [Bool.toNat_false, Nat.zero_shiftLeft, Nat.zero_testBit, Bool.or_false]
      by_cases hi : i = n
      · subst hi; simp [hf]
      · have hcmp : (i < n + 1) ↔ (i < n) := by omega
        simp [hcmp]
    · rw [Bool.toNat_true, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
      by_cases hi : i = n
      · subst hi; simp [hf]
      · have hne : n ≠ i := fun h => hi h.symm
        have hcmp : (i < n + 1) ↔ (i < n) := by omega
        simp [hne, hcmp]

def backPair (h : Nat) (z : Fin h → Bool) (a b : Bool) : Nat → Bool × Bool
  | 0 => (a, b)
  | d + 1 =>
    let p := backPair h z a b d
    let w := if hd : h - (d + 1) < h then xor (z ⟨h - (d + 1), hd⟩) (!p.1 && p.2) else false
    (w, p.1)

def fiberBit (h : Nat) (z : Fin h → Bool) (a b : Bool) (i : Nat) : Bool :=
  if i = h + 1 then b
  else if i ≤ h then (backPair h z a b (h - i)).1
  else false

lemma fiberBit_h (h : Nat) (z : Fin h → Bool) (a b : Bool) :
    fiberBit h z a b h = a := by
  unfold fiberBit
  simp [backPair]

lemma fiberBit_h1 (h : Nat) (z : Fin h → Bool) (a b : Bool) :
    fiberBit h z a b (h + 1) = b := by
  simp [fiberBit]

lemma backPair_snd_eq (h : Nat) (z : Fin h → Bool) (a b : Bool) (d : Nat) (hd : d ≤ h) :
    (backPair h z a b d).2 = fiberBit h z a b (h - d + 1) := by
  cases d with
  | zero =>
    simp [backPair, fiberBit_h1]
  | succ d =>
    unfold backPair fiberBit
    have hne : h - (d + 1) ≠ h := by omega
    have hle : h - (d + 1) + 1 ≤ h := by omega
    have hsub : h - (h - (d + 1) + 1) = d := by omega
    simp [hne, hle, hsub]

lemma fiberBit_lt (h : Nat) (z : Fin h → Bool) (a b : Bool) (i : Nat) (hi : i < h) :
    fiberBit h z a b i =
      xor (z ⟨i, hi⟩) (!(fiberBit h z a b (i + 1)) && fiberBit h z a b (i + 2)) := by
  have hne : i ≠ h + 1 := by omega
  have hle : i ≤ h := by omega
  have hne1 : i + 1 ≠ h + 1 := by omega
  have hle1 : i + 1 ≤ h := by omega
  have hd : h - i = (h - (i + 1)) + 1 := by omega
  have hsub : h - ((h - (i + 1)) + 1) = i := by omega
  have hsnd := backPair_snd_eq h z a b (h - (i + 1)) (by omega)
  have heq2 : h - (h - (i + 1)) + 1 = i + 2 := by omega
  rw [heq2] at hsnd
  have hstep1 : fiberBit h z a b (i + 1) = (backPair h z a b (h - (i + 1))).1 := by
    unfold fiberBit
    simp only [hne1, hle1, ↓reduceIte]
  conv_lhs => unfold fiberBit
  simp only [hne, hle, ↓reduceIte]
  rw [hd]
  unfold backPair
  simp only [hsub, hi, ↓reduceDIte, hsnd, hstep1]

lemma xor_eq_iff_left (x y z : Bool) : xor x y = z ↔ x = xor z y := by
  cases x <;> cases y <;> cases z <;> decide

def fiberVal (h : Nat) (z : Fin h → Bool) (a b : Bool) : Nat :=
  packBits (h + 2) (fiberBit h z a b)

lemma fiberVal_testBit (h : Nat) (z : Fin h → Bool) (a b : Bool) (i : Nat) (hi : i < h + 2) :
    (fiberVal h z a b).testBit i = fiberBit h z a b i := by
  unfold fiberVal
  rw [testBit_packBits, decide_eq_true hi, Bool.true_and]

lemma fiberVal_mem (h : Nat) (z : Fin h → Bool) (a b : Bool) :
    fiberVal h z a b ∈ fiber h z := by
  refine ⟨packBits_lt (h + 2) (fiberBit h z a b), ?_⟩
  intro j
  unfold chiFn
  dsimp only
  rw [fiberVal_testBit h z a b j.val (by omega),
    fiberVal_testBit h z a b (j.val + 1) (by omega),
    fiberVal_testBit h z a b (j.val + 2) (by omega),
    fiberBit_lt h z a b j.val j.isLt]
  cases z j <;> cases fiberBit h z a b (j.val + 1) <;> cases fiberBit h z a b (j.val + 2) <;> rfl

lemma fiber_eq_of_top_eq {h : Nat} {z : Fin h → Bool} {u1 u2 : Nat}
    (hu1 : u1 ∈ fiber h z) (hu2 : u2 ∈ fiber h z)
    (hh : u1.testBit h = u2.testBit h) (hh1 : u1.testBit (h + 1) = u2.testBit (h + 1)) :
    u1 = u2 := by
  have hdown : ∀ d, d ≤ h →
      u1.testBit (h - d) = u2.testBit (h - d) ∧
      u1.testBit (h - d + 1) = u2.testBit (h - d + 1) := by
    intro d
    induction d with
    | zero =>
      intro _
      exact ⟨hh, hh1⟩
    | succ d ih =>
      intro hd
      have hprev := ih (by omega)
      have hi : h - (d + 1) < h := by omega
      have h1 : h - (d + 1) + 1 = h - d := by omega
      have h2 : h - (d + 1) + 2 = h - d + 1 := by omega
      have hz1 := hu1.2 ⟨h - (d + 1), hi⟩
      have hz2 := hu2.2 ⟨h - (d + 1), hi⟩
      unfold chiFn at hz1 hz2
      dsimp only at hz1 hz2
      rw [h1, h2] at hz1 hz2
      rw [h1]
      refine ⟨?_, hprev.1⟩
      rw [xor_eq_iff_left] at hz1 hz2
      rw [hz1, hz2, hprev.1, hprev.2]
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i ≤ h
  · have hdi := hdown (h - i) (by omega)
    have heq : h - (h - i) = i := by omega
    rw [heq] at hdi
    exact hdi.1
  · by_cases hi1 : i = h + 1
    · subst hi1; exact hh1
    · have hge : h + 2 ≤ i := by omega
      have hb1 := Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hu1.1 (Nat.pow_le_pow_right (by omega) hge))
      have hb2 := Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hu2.1 (Nat.pow_le_pow_right (by omega) hge))
      rw [hb1, hb2]

def sim4 (p0 p1 p2 p3 p4 p5 z0 z1 z2 z3 a b : Bool) : Bool × Bool × Bool × Bool :=
  let w3 := xor z3 (!a && b)
  let w2 := xor z2 (!w3 && a)
  let w1 := xor z1 (!w2 && w3)
  let w0 := xor z0 (!w1 && w2)
  let v0 := xor w0 p0
  let v1 := xor w1 p1
  let v2 := xor w2 p2
  let v3 := xor w3 p3
  let v4 := xor a p4
  let v5 := xor b p5
  (chiB v0 v1 v2, chiB v1 v2 v3, chiB v2 v3 v4, chiB v3 v4 v5)

def sim5 (p0 p1 p2 p3 p4 p5 p6 z0 z1 z2 z3 z4 a b : Bool) :
    Bool × Bool × Bool × Bool × Bool :=
  let w4 := xor z4 (!a && b)
  let w3 := xor z3 (!w4 && a)
  let w2 := xor z2 (!w3 && w4)
  let w1 := xor z1 (!w2 && w3)
  let w0 := xor z0 (!w1 && w2)
  let v0 := xor w0 p0
  let v1 := xor w1 p1
  let v2 := xor w2 p2
  let v3 := xor w3 p3
  let v4 := xor w4 p4
  let v5 := xor a p5
  let v6 := xor b p6
  (chiB v0 v1 v2, chiB v1 v2 v3, chiB v2 v3 v4, chiB v3 v4 v5, chiB v4 v5 v6)

lemma fiber_testBit_step {h : Nat} {z : Fin h → Bool} {u : Nat} (hu : u ∈ fiber h z)
    (i : Nat) (hi : i < h) :
    u.testBit i = xor (z ⟨i, hi⟩) (!(u.testBit (i + 1)) && u.testBit (i + 2)) := by
  have hz := hu.2 ⟨i, hi⟩
  unfold chiFn at hz
  exact (xor_eq_iff_left _ _ _).mp hz

lemma tail5_eq_sim5 {h k start x u : Nat} {z : Fin h → Bool} (hh : 5 ≤ h) (hu : u ∈ fiber h z) :
    (chiFn (fun i => xor (u.testBit i) (pulse k start false x i)) (h - 5 + 0),
     chiFn (fun i => xor (u.testBit i) (pulse k start false x i)) (h - 5 + 1),
     chiFn (fun i => xor (u.testBit i) (pulse k start false x i)) (h - 5 + 2),
     chiFn (fun i => xor (u.testBit i) (pulse k start false x i)) (h - 5 + 3),
     chiFn (fun i => xor (u.testBit i) (pulse k start false x i)) (h - 5 + 4)) =
    sim5 (pulse k start false x (h - 5)) (pulse k start false x (h - 4))
         (pulse k start false x (h - 3)) (pulse k start false x (h - 2))
         (pulse k start false x (h - 1)) (pulse k start false x h)
         (pulse k start false x (h + 1))
         (z ⟨h - 5, by omega⟩) (z ⟨h - 4, by omega⟩) (z ⟨h - 3, by omega⟩)
         (z ⟨h - 2, by omega⟩) (z ⟨h - 1, by omega⟩)
         (u.testBit h) (u.testBit (h + 1)) := by
  have e0 : h - 5 + 0 = h - 5 := by omega
  have e1 : h - 5 + 1 = h - 4 := by omega
  have e2 : h - 5 + 2 = h - 3 := by omega
  have e3 : h - 5 + 3 = h - 2 := by omega
  have e4 : h - 5 + 4 = h - 1 := by omega
  have hw4 := fiber_testBit_step hu (h - 1) (by omega)
  have hw3 := fiber_testBit_step hu (h - 2) (by omega)
  have hw2 := fiber_testBit_step hu (h - 3) (by omega)
  have hw1 := fiber_testBit_step hu (h - 4) (by omega)
  have hw0 := fiber_testBit_step hu (h - 5) (by omega)
  have f41 : h - 1 + 1 = h := by omega
  have f42 : h - 1 + 2 = h + 1 := by omega
  have f31 : h - 2 + 1 = h - 1 := by omega
  have f32 : h - 2 + 2 = h := by omega
  have f21 : h - 3 + 1 = h - 2 := by omega
  have f22 : h - 3 + 2 = h - 1 := by omega
  have f11 : h - 4 + 1 = h - 3 := by omega
  have f12 : h - 4 + 2 = h - 2 := by omega
  have f01 : h - 5 + 1 = h - 4 := by omega
  have f02 : h - 5 + 2 = h - 3 := by omega
  rw [f41, f42] at hw4
  rw [f31, f32] at hw3
  rw [f21, f22] at hw2
  rw [f11, f12] at hw1
  rw [f01, f02] at hw0
  unfold chiFn sim5 chiB
  simp only [e0, e1, e2, e3, e4, f11, f12, f21, f22, f31, f32, f41, f42]
  rw [hw0, hw1, hw2, hw3, hw4]

lemma tail4_eq_sim4 {h k start x u : Nat} {z : Fin h → Bool} (hh : 5 ≤ h) (hu : u ∈ fiber h z) :
    (chiFn (fun i => xor (u.testBit i) (pulse k start true x i)) (h - 4 + 0),
     chiFn (fun i => xor (u.testBit i) (pulse k start true x i)) (h - 4 + 1),
     chiFn (fun i => xor (u.testBit i) (pulse k start true x i)) (h - 4 + 2),
     chiFn (fun i => xor (u.testBit i) (pulse k start true x i)) (h - 4 + 3)) =
    sim4 (pulse k start true x (h - 4)) (pulse k start true x (h - 3))
         (pulse k start true x (h - 2)) (pulse k start true x (h - 1))
         (pulse k start true x h) (pulse k start true x (h + 1))
         (z ⟨h - 4, by omega⟩) (z ⟨h - 3, by omega⟩)
         (z ⟨h - 2, by omega⟩) (z ⟨h - 1, by omega⟩)
         (u.testBit h) (u.testBit (h + 1)) := by
  have e0 : h - 4 + 0 = h - 4 := by omega
  have e1 : h - 4 + 1 = h - 3 := by omega
  have e2 : h - 4 + 2 = h - 2 := by omega
  have e3 : h - 4 + 3 = h - 1 := by omega
  have hw3 := fiber_testBit_step hu (h - 1) (by omega)
  have hw2 := fiber_testBit_step hu (h - 2) (by omega)
  have hw1 := fiber_testBit_step hu (h - 3) (by omega)
  have hw0 := fiber_testBit_step hu (h - 4) (by omega)
  have f31 : h - 1 + 1 = h := by omega
  have f32 : h - 1 + 2 = h + 1 := by omega
  have f21 : h - 2 + 1 = h - 1 := by omega
  have f22 : h - 2 + 2 = h := by omega
  have f11 : h - 3 + 1 = h - 2 := by omega
  have f12 : h - 3 + 2 = h - 1 := by omega
  have f01 : h - 4 + 1 = h - 3 := by omega
  have f02 : h - 4 + 2 = h - 2 := by omega
  rw [f31, f32] at hw3
  rw [f21, f22] at hw2
  rw [f11, f12] at hw1
  rw [f01, f02] at hw0
  unfold chiFn sim4 chiB
  simp only [e0, e1, e2, e3, f11, f12, f21, f22, f31, f32]
  rw [hw0, hw1, hw2, hw3]

lemma bool_eq_of_iff {a b : Bool} (h : (a = true) ↔ (b = true)) : a = b := by
  cases a <;> cases b <;> simp at h ⊢

lemma tail_bit_eq_of_tail_eq {h k start x len u1 u2 j : Nat} {col : Bool}
    (ht : tail h k start col x len u1 = tail h k start col x len u2) (hj : j < len) :
    chiFn (fun i => xor (u1.testBit i) (pulse k start col x i)) (h - len + j) =
      chiFn (fun i => xor (u2.testBit i) (pulse k start col x i)) (h - len + j) := by
  apply bool_eq_of_iff
  have hmem : j ∈ tail h k start col x len u1 ↔ j ∈ tail h k start col x len u2 := by
    rw [ht]
  unfold tail at hmem
  simp only [Finset.mem_filter, Finset.mem_range, hj, true_and] at hmem
  exact hmem

lemma injOn_tail5_of_sim5 {h k start x : Nat} {z : Fin h → Bool} (hh : 5 ≤ h)
    (hinj : ∀ a1 b1 a2 b2 : Bool,
      sim5 (pulse k start false x (h - 5)) (pulse k start false x (h - 4))
           (pulse k start false x (h - 3)) (pulse k start false x (h - 2))
           (pulse k start false x (h - 1)) (pulse k start false x h)
           (pulse k start false x (h + 1))
           (z ⟨h - 5, by omega⟩) (z ⟨h - 4, by omega⟩) (z ⟨h - 3, by omega⟩)
           (z ⟨h - 2, by omega⟩) (z ⟨h - 1, by omega⟩) a1 b1 =
      sim5 (pulse k start false x (h - 5)) (pulse k start false x (h - 4))
           (pulse k start false x (h - 3)) (pulse k start false x (h - 2))
           (pulse k start false x (h - 1)) (pulse k start false x h)
           (pulse k start false x (h + 1))
           (z ⟨h - 5, by omega⟩) (z ⟨h - 4, by omega⟩) (z ⟨h - 3, by omega⟩)
           (z ⟨h - 2, by omega⟩) (z ⟨h - 1, by omega⟩) a2 b2 →
      a1 = a2 ∧ b1 = b2) :
    Set.InjOn (tail h k start false x 5) (fiber h z) := by
  intro u1 hu1 u2 hu2 ht
  have h0 := tail_bit_eq_of_tail_eq ht (j := 0) (by omega)
  have h1 := tail_bit_eq_of_tail_eq ht (j := 1) (by omega)
  have h2 := tail_bit_eq_of_tail_eq ht (j := 2) (by omega)
  have h3 := tail_bit_eq_of_tail_eq ht (j := 3) (by omega)
  have h4 := tail_bit_eq_of_tail_eq ht (j := 4) (by omega)
  have hs1 := tail5_eq_sim5 (k := k) (start := start) (x := x) hh hu1
  have hs2 := tail5_eq_sim5 (k := k) (start := start) (x := x) hh hu2
  have hsim : sim5 (pulse k start false x (h - 5)) (pulse k start false x (h - 4))
           (pulse k start false x (h - 3)) (pulse k start false x (h - 2))
           (pulse k start false x (h - 1)) (pulse k start false x h)
           (pulse k start false x (h + 1))
           (z ⟨h - 5, by omega⟩) (z ⟨h - 4, by omega⟩) (z ⟨h - 3, by omega⟩)
           (z ⟨h - 2, by omega⟩) (z ⟨h - 1, by omega⟩)
           (u1.testBit h) (u1.testBit (h + 1)) =
      sim5 (pulse k start false x (h - 5)) (pulse k start false x (h - 4))
           (pulse k start false x (h - 3)) (pulse k start false x (h - 2))
           (pulse k start false x (h - 1)) (pulse k start false x h)
           (pulse k start false x (h + 1))
           (z ⟨h - 5, by omega⟩) (z ⟨h - 4, by omega⟩) (z ⟨h - 3, by omega⟩)
           (z ⟨h - 2, by omega⟩) (z ⟨h - 1, by omega⟩)
           (u2.testBit h) (u2.testBit (h + 1)) := by
    rw [← hs1, ← hs2, h0, h1, h2, h3, h4]
  have hab := hinj _ _ _ _ hsim
  exact fiber_eq_of_top_eq hu1 hu2 hab.1 hab.2

lemma injOn_tail4_of_sim4 {h k start x : Nat} {z : Fin h → Bool} (hh : 5 ≤ h)
    (hinj : ∀ a1 b1 a2 b2 : Bool,
      sim4 (pulse k start true x (h - 4)) (pulse k start true x (h - 3))
           (pulse k start true x (h - 2)) (pulse k start true x (h - 1))
           (pulse k start true x h) (pulse k start true x (h + 1))
           (z ⟨h - 4, by omega⟩) (z ⟨h - 3, by omega⟩)
           (z ⟨h - 2, by omega⟩) (z ⟨h - 1, by omega⟩) a1 b1 =
      sim4 (pulse k start true x (h - 4)) (pulse k start true x (h - 3))
           (pulse k start true x (h - 2)) (pulse k start true x (h - 1))
           (pulse k start true x h) (pulse k start true x (h + 1))
           (z ⟨h - 4, by omega⟩) (z ⟨h - 3, by omega⟩)
           (z ⟨h - 2, by omega⟩) (z ⟨h - 1, by omega⟩) a2 b2 →
      a1 = a2 ∧ b1 = b2) :
    Set.InjOn (tail h k start true x 4) (fiber h z) := by
  intro u1 hu1 u2 hu2 ht
  have h0 := tail_bit_eq_of_tail_eq ht (j := 0) (by omega)
  have h1 := tail_bit_eq_of_tail_eq ht (j := 1) (by omega)
  have h2 := tail_bit_eq_of_tail_eq ht (j := 2) (by omega)
  have h3 := tail_bit_eq_of_tail_eq ht (j := 3) (by omega)
  have hs1 := tail4_eq_sim4 (k := k) (start := start) (x := x) hh hu1
  have hs2 := tail4_eq_sim4 (k := k) (start := start) (x := x) hh hu2
  have hsim : sim4 (pulse k start true x (h - 4)) (pulse k start true x (h - 3))
           (pulse k start true x (h - 2)) (pulse k start true x (h - 1))
           (pulse k start true x h) (pulse k start true x (h + 1))
           (z ⟨h - 4, by omega⟩) (z ⟨h - 3, by omega⟩)
           (z ⟨h - 2, by omega⟩) (z ⟨h - 1, by omega⟩)
           (u1.testBit h) (u1.testBit (h + 1)) =
      sim4 (pulse k start true x (h - 4)) (pulse k start true x (h - 3))
           (pulse k start true x (h - 2)) (pulse k start true x (h - 1))
           (pulse k start true x h) (pulse k start true x (h + 1))
           (z ⟨h - 4, by omega⟩) (z ⟨h - 3, by omega⟩)
           (z ⟨h - 2, by omega⟩) (z ⟨h - 1, by omega⟩)
           (u2.testBit h) (u2.testBit (h + 1)) := by
    rw [← hs1, ← hs2, h0, h1, h2, h3]
  have hab := hinj _ _ _ _ hsim
  exact fiber_eq_of_top_eq hu1 hu2 hab.1 hab.2

lemma not_injOn_tail5_of_sim5 {h k start x : Nat} {z : Fin h → Bool} (hh : 5 ≤ h)
    {a1 b1 a2 b2 : Bool} (hne : ¬(a1 = a2 ∧ b1 = b2))
    (heq : sim5 (pulse k start false x (h - 5)) (pulse k start false x (h - 4))
                (pulse k start false x (h - 3)) (pulse k start false x (h - 2))
                (pulse k start false x (h - 1)) (pulse k start false x h)
                (pulse k start false x (h + 1))
                (z ⟨h - 5, by omega⟩) (z ⟨h - 4, by omega⟩) (z ⟨h - 3, by omega⟩)
                (z ⟨h - 2, by omega⟩) (z ⟨h - 1, by omega⟩) a1 b1 =
           sim5 (pulse k start false x (h - 5)) (pulse k start false x (h - 4))
                (pulse k start false x (h - 3)) (pulse k start false x (h - 2))
                (pulse k start false x (h - 1)) (pulse k start false x h)
                (pulse k start false x (h + 1))
                (z ⟨h - 5, by omega⟩) (z ⟨h - 4, by omega⟩) (z ⟨h - 3, by omega⟩)
                (z ⟨h - 2, by omega⟩) (z ⟨h - 1, by omega⟩) a2 b2) :
    ¬ Set.InjOn (tail h k start false x 5) (fiber h z) := by
  intro hinj
  let u1 := fiberVal h z a1 b1
  let u2 := fiberVal h z a2 b2
  have hu1 : u1 ∈ fiber h z := fiberVal_mem h z a1 b1
  have hu2 : u2 ∈ fiber h z := fiberVal_mem h z a2 b2
  have ht1h : u1.testBit h = a1 := by
    rw [fiberVal_testBit h z a1 b1 h (by omega), fiberBit_h]
  have ht1h1 : u1.testBit (h + 1) = b1 := by
    rw [fiberVal_testBit h z a1 b1 (h + 1) (by omega), fiberBit_h1]
  have ht2h : u2.testBit h = a2 := by
    rw [fiberVal_testBit h z a2 b2 h (by omega), fiberBit_h]
  have ht2h1 : u2.testBit (h + 1) = b2 := by
    rw [fiberVal_testBit h z a2 b2 (h + 1) (by omega), fiberBit_h1]
  have hs1 := tail5_eq_sim5 (k := k) (start := start) (x := x) hh hu1
  have hs2 := tail5_eq_sim5 (k := k) (start := start) (x := x) hh hu2
  rw [ht1h, ht1h1] at hs1
  rw [ht2h, ht2h1] at hs2
  have h5 : (chiFn (fun i => xor (u1.testBit i) (pulse k start false x i)) (h - 5 + 0),
     chiFn (fun i => xor (u1.testBit i) (pulse k start false x i)) (h - 5 + 1),
     chiFn (fun i => xor (u1.testBit i) (pulse k start false x i)) (h - 5 + 2),
     chiFn (fun i => xor (u1.testBit i) (pulse k start false x i)) (h - 5 + 3),
     chiFn (fun i => xor (u1.testBit i) (pulse k start false x i)) (h - 5 + 4)) =
    (chiFn (fun i => xor (u2.testBit i) (pulse k start false x i)) (h - 5 + 0),
     chiFn (fun i => xor (u2.testBit i) (pulse k start false x i)) (h - 5 + 1),
     chiFn (fun i => xor (u2.testBit i) (pulse k start false x i)) (h - 5 + 2),
     chiFn (fun i => xor (u2.testBit i) (pulse k start false x i)) (h - 5 + 3),
     chiFn (fun i => xor (u2.testBit i) (pulse k start false x i)) (h - 5 + 4)) := by
    rw [hs1, hs2, heq]
  simp only [Prod.mk.injEq] at h5
  rcases h5 with ⟨h50, h51, h52, h53, h54⟩
  have ht : tail h k start false x 5 u1 = tail h k start false x 5 u2 := by
    apply Finset.ext
    intro j
    unfold tail
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor <;> rintro ⟨hj, hp⟩ <;> refine ⟨hj, ?_⟩
    · have hcase : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl
      · rw [← h50]; exact hp
      · rw [← h51]; exact hp
      · rw [← h52]; exact hp
      · rw [← h53]; exact hp
      · rw [← h54]; exact hp
    · have hcase : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl
      · rw [h50]; exact hp
      · rw [h51]; exact hp
      · rw [h52]; exact hp
      · rw [h53]; exact hp
      · rw [h54]; exact hp
  have hu : u1 = u2 := hinj hu1 hu2 ht
  exact hne ⟨by rw [← ht1h, ← ht2h, hu], by rw [← ht1h1, ← ht2h1, hu]⟩

lemma not_injOn_tail4_of_sim4 {h k start x : Nat} {z : Fin h → Bool} (hh : 5 ≤ h)
    {a1 b1 a2 b2 : Bool} (hne : ¬(a1 = a2 ∧ b1 = b2))
    (heq : sim4 (pulse k start true x (h - 4)) (pulse k start true x (h - 3))
                (pulse k start true x (h - 2)) (pulse k start true x (h - 1))
                (pulse k start true x h) (pulse k start true x (h + 1))
                (z ⟨h - 4, by omega⟩) (z ⟨h - 3, by omega⟩)
                (z ⟨h - 2, by omega⟩) (z ⟨h - 1, by omega⟩) a1 b1 =
           sim4 (pulse k start true x (h - 4)) (pulse k start true x (h - 3))
                (pulse k start true x (h - 2)) (pulse k start true x (h - 1))
                (pulse k start true x h) (pulse k start true x (h + 1))
                (z ⟨h - 4, by omega⟩) (z ⟨h - 3, by omega⟩)
                (z ⟨h - 2, by omega⟩) (z ⟨h - 1, by omega⟩) a2 b2) :
    ¬ Set.InjOn (tail h k start true x 4) (fiber h z) := by
  intro hinj
  let u1 := fiberVal h z a1 b1
  let u2 := fiberVal h z a2 b2
  have hu1 : u1 ∈ fiber h z := fiberVal_mem h z a1 b1
  have hu2 : u2 ∈ fiber h z := fiberVal_mem h z a2 b2
  have ht1h : u1.testBit h = a1 := by
    rw [fiberVal_testBit h z a1 b1 h (by omega), fiberBit_h]
  have ht1h1 : u1.testBit (h + 1) = b1 := by
    rw [fiberVal_testBit h z a1 b1 (h + 1) (by omega), fiberBit_h1]
  have ht2h : u2.testBit h = a2 := by
    rw [fiberVal_testBit h z a2 b2 h (by omega), fiberBit_h]
  have ht2h1 : u2.testBit (h + 1) = b2 := by
    rw [fiberVal_testBit h z a2 b2 (h + 1) (by omega), fiberBit_h1]
  have hs1 := tail4_eq_sim4 (k := k) (start := start) (x := x) hh hu1
  have hs2 := tail4_eq_sim4 (k := k) (start := start) (x := x) hh hu2
  rw [ht1h, ht1h1] at hs1
  rw [ht2h, ht2h1] at hs2
  have h4 : (chiFn (fun i => xor (u1.testBit i) (pulse k start true x i)) (h - 4 + 0),
     chiFn (fun i => xor (u1.testBit i) (pulse k start true x i)) (h - 4 + 1),
     chiFn (fun i => xor (u1.testBit i) (pulse k start true x i)) (h - 4 + 2),
     chiFn (fun i => xor (u1.testBit i) (pulse k start true x i)) (h - 4 + 3)) =
    (chiFn (fun i => xor (u2.testBit i) (pulse k start true x i)) (h - 4 + 0),
     chiFn (fun i => xor (u2.testBit i) (pulse k start true x i)) (h - 4 + 1),
     chiFn (fun i => xor (u2.testBit i) (pulse k start true x i)) (h - 4 + 2),
     chiFn (fun i => xor (u2.testBit i) (pulse k start true x i)) (h - 4 + 3)) := by
    rw [hs1, hs2, heq]
  simp only [Prod.mk.injEq] at h4
  rcases h4 with ⟨h40, h41, h42, h43⟩
  have ht : tail h k start true x 4 u1 = tail h k start true x 4 u2 := by
    apply Finset.ext
    intro j
    unfold tail
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor <;> rintro ⟨hj, hp⟩ <;> refine ⟨hj, ?_⟩
    · have hcase : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · rw [← h40]; exact hp
      · rw [← h41]; exact hp
      · rw [← h42]; exact hp
      · rw [← h43]; exact hp
    · have hcase : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · rw [h40]; exact hp
      · rw [h41]; exact hp
      · rw [h42]; exact hp
      · rw [h43]; exact hp
  have hu : u1 = u2 := hinj hu1 hu2 ht
  exact hne ⟨by rw [← ht1h, ← ht2h, hu], by rw [← ht1h1, ← ht2h1, hu]⟩

def isInj5 (p0 p1 p2 p3 p4 p5 p6 z0 z1 z2 z3 z4 : Bool) : Bool :=
  let s00 := sim5 p0 p1 p2 p3 p4 p5 p6 z0 z1 z2 z3 z4 false false
  let s01 := sim5 p0 p1 p2 p3 p4 p5 p6 z0 z1 z2 z3 z4 false true
  let s10 := sim5 p0 p1 p2 p3 p4 p5 p6 z0 z1 z2 z3 z4 true false
  let s11 := sim5 p0 p1 p2 p3 p4 p5 p6 z0 z1 z2 z3 z4 true true
  (s00 != s01) && (s00 != s10) && (s00 != s11) &&
    (s01 != s10) && (s01 != s11) && (s10 != s11)

def isInj4 (p0 p1 p2 p3 p4 p5 z0 z1 z2 z3 : Bool) : Bool :=
  let s00 := sim4 p0 p1 p2 p3 p4 p5 z0 z1 z2 z3 false false
  let s01 := sim4 p0 p1 p2 p3 p4 p5 z0 z1 z2 z3 false true
  let s10 := sim4 p0 p1 p2 p3 p4 p5 z0 z1 z2 z3 true false
  let s11 := sim4 p0 p1 p2 p3 p4 p5 z0 z1 z2 z3 true true
  (s00 != s01) && (s00 != s10) && (s00 != s11) &&
    (s01 != s10) && (s01 != s11) && (s10 != s11)

lemma sim5_inj_of_isInj5 (p0 p1 p2 p3 p4 p5 p6 z0 z1 z2 z3 z4 : Bool)
    (h : isInj5 p0 p1 p2 p3 p4 p5 p6 z0 z1 z2 z3 z4 = true) :
    ∀ a1 b1 a2 b2 : Bool,
      sim5 p0 p1 p2 p3 p4 p5 p6 z0 z1 z2 z3 z4 a1 b1 =
        sim5 p0 p1 p2 p3 p4 p5 p6 z0 z1 z2 z3 z4 a2 b2 →
      a1 = a2 ∧ b1 = b2 := by
  intro a1 b1 a2 b2 heq
  unfold isInj5 at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  rcases h with ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
  cases a1 <;> cases b1 <;> cases a2 <;> cases b2
  · exact ⟨rfl, rfl⟩
  · exact absurd heq h1
  · exact absurd heq h2
  · exact absurd heq h3
  · exact absurd heq.symm h1
  · exact ⟨rfl, rfl⟩
  · exact absurd heq h4
  · exact absurd heq h5
  · exact absurd heq.symm h2
  · exact absurd heq.symm h4
  · exact ⟨rfl, rfl⟩
  · exact absurd heq h6
  · exact absurd heq.symm h3
  · exact absurd heq.symm h5
  · exact absurd heq.symm h6
  · exact ⟨rfl, rfl⟩

lemma sim4_inj_of_isInj4 (p0 p1 p2 p3 p4 p5 z0 z1 z2 z3 : Bool)
    (h : isInj4 p0 p1 p2 p3 p4 p5 z0 z1 z2 z3 = true) :
    ∀ a1 b1 a2 b2 : Bool,
      sim4 p0 p1 p2 p3 p4 p5 z0 z1 z2 z3 a1 b1 =
        sim4 p0 p1 p2 p3 p4 p5 z0 z1 z2 z3 a2 b2 →
      a1 = a2 ∧ b1 = b2 := by
  intro a1 b1 a2 b2 heq
  unfold isInj4 at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  rcases h with ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
  cases a1 <;> cases b1 <;> cases a2 <;> cases b2
  · exact ⟨rfl, rfl⟩
  · exact absurd heq h1
  · exact absurd heq h2
  · exact absurd heq h3
  · exact absurd heq.symm h1
  · exact ⟨rfl, rfl⟩
  · exact absurd heq h4
  · exact absurd heq h5
  · exact absurd heq.symm h2
  · exact absurd heq.symm h4
  · exact ⟨rfl, rfl⟩
  · exact absurd heq h6
  · exact absurd heq.symm h3
  · exact absurd heq.symm h5
  · exact absurd heq.symm h6
  · exact ⟨rfl, rfl⟩

lemma key0_row_ok (z0 z1 z2 z3 : Bool) :
    isInj5 false true false false true true false z0 z1 z2 z3 false = true := by
  cases z0 <;> cases z1 <;> cases z2 <;> cases z3 <;> rfl

lemma key0_col_ok (z0 z1 z2 z3 : Bool) (h : z3 = true ∨ z2 = false) :
    isInj4 true false true true true false z0 z1 z2 z3 = true := by
  rcases h with rfl | rfl
  · cases z0 <;> cases z1 <;> cases z2 <;> rfl
  · cases z0 <;> cases z1 <;> cases z3 <;> rfl

lemma key1_row_ok (z0 z1 z2 z3 z4 : Bool) (h : z4 = true ∨ z2 = false) :
    isInj5 true false true true true true false z0 z1 z2 z3 z4 = true := by
  rcases h with rfl | rfl
  · cases z0 <;> cases z1 <;> cases z2 <;> cases z3 <;> rfl
  · cases z0 <;> cases z1 <;> cases z3 <;> cases z4 <;> rfl

lemma key1_col_ok (z0 z1 z2 : Bool) :
    isInj4 true true false false true true z0 z1 z2 false = true := by
  cases z0 <;> cases z1 <;> cases z2 <;> rfl

lemma key2_row_ok (z0 z1 z2 z3 z4 : Bool) (h : z4 = true ∨ z2 = true) :
    isInj5 true true true true true true true z0 z1 z2 z3 z4 = true := by
  rcases h with rfl | rfl
  · cases z0 <;> cases z1 <;> cases z2 <;> cases z3 <;> rfl
  · cases z0 <;> cases z1 <;> cases z3 <;> cases z4 <;> rfl

lemma key2_col_ok (z0 z1 z2 z3 : Bool) (h : z3 = true ∨ z2 = true) :
    isInj4 false true true true true true z0 z1 z2 z3 = true := by
  rcases h with rfl | rfl
  · cases z0 <;> cases z1 <;> cases z2 <;> rfl
  · cases z0 <;> cases z1 <;> cases z3 <;> rfl

def badRowWit (p1 p2 p3 p4 p5 p6 : Bool) :
    (Bool × Bool × Bool × Bool × Bool) × (Bool × Bool) × (Bool × Bool) :=
  if !p5 then
    ((false, false, false, false, false), (p1 || p3, false), (p1 || p3, true))
  else if !p4 then
    ((false, false, false, false, p2), (false, false), (true, p6))
  else
    let z :=
      if !p3 then (false, false, false, p1, true)
      else if !p2 then (false, false, false, true, false)
      else if !p1 then (false, false, true, false, false)
      else (false, false, false, false, false)
    (z, (false, true), (true, !p6))

def badColWit (p1 p2 p3 p4 p5 : Bool) :
    (Bool × Bool × Bool × Bool) × (Bool × Bool) × (Bool × Bool) :=
  if !p4 then
    ((false, false, false, false), (p2, false), (p2, true))
  else if !p3 then
    ((false, false, false, p1), (false, false), (true, p5))
  else
    let z :=
      if !p2 then (false, false, false, true)
      else if !p1 then (false, false, true, false)
      else (false, false, false, false)
    (z, (false, true), (true, !p5))

lemma badRowWit_spec (p0 p1 p2 p3 p4 p5 p6 : Bool) :
    let w := badRowWit p1 p2 p3 p4 p5 p6
    (w.2.1 != w.2.2) &&
      (sim5 p0 p1 p2 p3 p4 p5 p6 w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2.1 w.1.2.2.2.2 w.2.1.1 w.2.1.2 ==
       sim5 p0 p1 p2 p3 p4 p5 p6 w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2.1 w.1.2.2.2.2 w.2.2.1 w.2.2.2) = true := by
  cases p0 <;> cases p1 <;> cases p2 <;> cases p3 <;> cases p4 <;> cases p5 <;> cases p6 <;> rfl

lemma badColWit_spec (p0 p1 p2 p3 p4 p5 : Bool) :
    let w := badColWit p1 p2 p3 p4 p5
    (w.2.1 != w.2.2) &&
      (sim4 p0 p1 p2 p3 p4 p5 w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2 w.2.1.1 w.2.1.2 ==
       sim4 p0 p1 p2 p3 p4 p5 w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2 w.2.2.1 w.2.2.2) = true := by
  cases p0 <;> cases p1 <;> cases p2 <;> cases p3 <;> cases p4 <;> cases p5 <;> rfl

def mkRowReply (h : Nat) (z : Bool × Bool × Bool × Bool × Bool) (i : Fin h) : Bool :=
  if i.val = h - 5 then z.1
  else if i.val = h - 4 then z.2.1
  else if i.val = h - 3 then z.2.2.1
  else if i.val = h - 2 then z.2.2.2.1
  else if i.val = h - 1 then z.2.2.2.2
  else false

def mkColReply (h : Nat) (z : Bool × Bool × Bool × Bool) (i : Fin h) : Bool :=
  if i.val = h - 4 then z.1
  else if i.val = h - 3 then z.2.1
  else if i.val = h - 2 then z.2.2.1
  else if i.val = h - 1 then z.2.2.2
  else false

def badRow (h k start x : Nat) : Fin h → Bool :=
  let w := badRowWit
    (pulse k start false x (h - 4)) (pulse k start false x (h - 3))
    (pulse k start false x (h - 2)) (pulse k start false x (h - 1))
    (pulse k start false x h) (pulse k start false x (h + 1))
  mkRowReply h w.1

def badCol (h k start x : Nat) : Fin h → Bool :=
  let w := badColWit
    (pulse k start true x (h - 3)) (pulse k start true x (h - 2))
    (pulse k start true x (h - 1)) (pulse k start true x h)
    (pulse k start true x (h + 1))
  mkColReply h w.1

lemma badRow_not_injOn (h k start x : Nat) (hh : 5 ≤ h) :
    ¬ Set.InjOn (tail h k start false x 5) (fiber h (badRow h k start x)) := by
  have hspec := badRowWit_spec
    (pulse k start false x (h - 5)) (pulse k start false x (h - 4))
    (pulse k start false x (h - 3)) (pulse k start false x (h - 2))
    (pulse k start false x (h - 1)) (pulse k start false x h)
    (pulse k start false x (h + 1))
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hspec
  let w := badRowWit
    (pulse k start false x (h - 4)) (pulse k start false x (h - 3))
    (pulse k start false x (h - 2)) (pulse k start false x (h - 1))
    (pulse k start false x h) (pulse k start false x (h + 1))
  have hne : ¬(w.2.1.1 = w.2.2.1 ∧ w.2.1.2 = w.2.2.2) := by
    intro hp
    apply hspec.1
    cases h1 : w.2.1
    cases h2 : w.2.2
    rw [h1, h2] at hp
    exact Prod.ext hp.1 hp.2
  have hz0 : badRow h k start x ⟨h - 5, by omega⟩ = w.1.1 := by
    simp [badRow, mkRowReply, w]
  have hz1 : badRow h k start x ⟨h - 4, by omega⟩ = w.1.2.1 := by
    unfold badRow mkRowReply
    have h1 : h - 4 ≠ h - 5 := by omega
    simp [h1, w]
  have hz2 : badRow h k start x ⟨h - 3, by omega⟩ = w.1.2.2.1 := by
    unfold badRow mkRowReply
    have h1 : h - 3 ≠ h - 5 := by omega
    have h2 : h - 3 ≠ h - 4 := by omega
    simp [h1, h2, w]
  have hz3 : badRow h k start x ⟨h - 2, by omega⟩ = w.1.2.2.2.1 := by
    unfold badRow mkRowReply
    have h1 : h - 2 ≠ h - 5 := by omega
    have h2 : h - 2 ≠ h - 4 := by omega
    have h3 : h - 2 ≠ h - 3 := by omega
    simp [h1, h2, h3, w]
  have hz4 : badRow h k start x ⟨h - 1, by omega⟩ = w.1.2.2.2.2 := by
    unfold badRow mkRowReply
    have h1 : h - 1 ≠ h - 5 := by omega
    have h2 : h - 1 ≠ h - 4 := by omega
    have h3 : h - 1 ≠ h - 3 := by omega
    have h4 : h - 1 ≠ h - 2 := by omega
    simp [h1, h2, h3, h4, w]
  apply not_injOn_tail5_of_sim5 hh hne
  rw [hz0, hz1, hz2, hz3, hz4]
  exact of_decide_eq_true hspec.2

lemma badCol_not_injOn (h k start x : Nat) (hh : 5 ≤ h) :
    ¬ Set.InjOn (tail h k start true x 4) (fiber h (badCol h k start x)) := by
  have hspec := badColWit_spec
    (pulse k start true x (h - 4)) (pulse k start true x (h - 3))
    (pulse k start true x (h - 2)) (pulse k start true x (h - 1))
    (pulse k start true x h) (pulse k start true x (h + 1))
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hspec
  let w := badColWit
    (pulse k start true x (h - 3)) (pulse k start true x (h - 2))
    (pulse k start true x (h - 1)) (pulse k start true x h)
    (pulse k start true x (h + 1))
  have hne : ¬(w.2.1.1 = w.2.2.1 ∧ w.2.1.2 = w.2.2.2) := by
    intro hp
    apply hspec.1
    cases h1 : w.2.1
    cases h2 : w.2.2
    rw [h1, h2] at hp
    exact Prod.ext hp.1 hp.2
  have hz0 : badCol h k start x ⟨h - 4, by omega⟩ = w.1.1 := by
    simp [badCol, mkColReply, w]
  have hz1 : badCol h k start x ⟨h - 3, by omega⟩ = w.1.2.1 := by
    unfold badCol mkColReply
    have h1 : h - 3 ≠ h - 4 := by omega
    simp [h1, w]
  have hz2 : badCol h k start x ⟨h - 2, by omega⟩ = w.1.2.2.1 := by
    unfold badCol mkColReply
    have h1 : h - 2 ≠ h - 4 := by omega
    have h2 : h - 2 ≠ h - 3 := by omega
    simp [h1, h2, w]
  have hz3 : badCol h k start x ⟨h - 1, by omega⟩ = w.1.2.2.2 := by
    unfold badCol mkColReply
    have h1 : h - 1 ≠ h - 4 := by omega
    have h2 : h - 1 ≠ h - 3 := by omega
    have h3 : h - 1 ≠ h - 2 := by omega
    simp [h1, h2, h3, w]
  apply not_injOn_tail4_of_sim4 hh hne
  rw [hz0, hz1, hz2, hz3]
  exact of_decide_eq_true hspec.2

def mkBits (ps : List Nat) : Nat :=
  ps.foldl (fun acc p => acc ||| (1 <<< p)) 0

lemma mkBits_foldl_lt (k acc : Nat) (ps : List Nat) (hacc : acc < 2 ^ k)
    (hps : ∀ p ∈ ps, p < k) :
    ps.foldl (fun a p => a ||| (1 <<< p)) acc < 2 ^ k := by
  induction ps generalizing acc with
  | nil => exact hacc
  | cons p ps ih =>
    simp only [List.foldl_cons]
    apply ih
    · apply Nat.or_lt_two_pow hacc
      rw [Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.pow_lt_pow_right (by omega) (hps p List.mem_cons_self)
    · intro q hq
      exact hps q (List.mem_cons_of_mem p hq)

lemma mkBits_lt (k : Nat) (ps : List Nat) (hps : ∀ p ∈ ps, p < k) :
    mkBits ps < 2 ^ k :=
  mkBits_foldl_lt k 0 ps (Nat.two_pow_pos k) hps

lemma testBit_mkBits_foldl (acc : Nat) (ps : List Nat) (i : Nat) :
    (ps.foldl (fun a p => a ||| (1 <<< p)) acc).testBit i =
      (acc.testBit i || ps.any (fun p => decide (p = i))) := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons, List.any_cons]
    rw [ih, Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow, Bool.or_assoc]

lemma testBit_mkBits (ps : List Nat) (i : Nat) :
    (mkBits ps).testBit i = ps.any (fun p => decide (p = i)) := by
  unfold mkBits
  rw [testBit_mkBits_foldl, Nat.zero_testBit, Bool.false_or]

lemma mod_add_eq_iff {base k t1 t2 : Nat} (ht1 : t1 < k) (ht2 : t2 < k) :
    (base + t1) % k = (base + t2) % k ↔ t1 = t2 := by
  constructor
  · intro h
    have haux : ∀ a b : Nat, a ≤ b → b < k → (base + a) % k = (base + b) % k → a = b := by
      intro a b hab hb heq
      have hk : 0 < k := by omega
      have hr : (base + a) % k < k := Nat.mod_lt _ hk
      have hba : (base + b) % k = ((base + a) % k + (b - a)) % k := by
        rw [Nat.mod_add_mod, show base + a + (b - a) = base + b by omega]
      rw [hba] at heq
      by_cases hs : (base + a) % k + (b - a) < k
      · rw [Nat.mod_eq_of_lt hs] at heq
        omega
      · have hlt : (base + a) % k + (b - a) - k < k := by omega
        have hrhs : ((base + a) % k + (b - a)) % k = (base + a) % k + (b - a) - k := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt]
        rw [hrhs] at heq
        omega
    by_cases hle : t1 ≤ t2
    · exact haux t1 t2 hle ht2 h
    · exact (haux t2 t1 (by omega) ht1 h.symm).symm
  · intro h
    rw [h]

def keySlots : Fin 3 → List Nat
  | ⟨0, _⟩ => [3, 4, 5, 7]
  | ⟨1, _⟩ => [4, 5, 6, 7, 8, 9]
  | ⟨2, _⟩ => [3, 6, 9]

def menuNat (h k start : Nat) (i : Fin 3) : Nat :=
  let base := start + h + k - 9
  mkBits ((keySlots i).map (fun t => (base + t) % k))

lemma menuNat_lt {h k start : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k) (i : Fin 3) :
    menuNat h k start i < 2 ^ k := by
  apply mkBits_lt
  intro p hp
  rcases List.mem_map.mp hp with ⟨t, _, rfl⟩
  exact Nat.mod_lt _ (by omega)

def menuVal (h k start : Nat) (hh : 5 ≤ h) (hk : h + 6 ≤ k) (i : Fin 3) : Fin (2 ^ k) :=
  ⟨menuNat h k start i, menuNat_lt hh hk i⟩

lemma keySlots_lt {k : Nat} (hk : 11 ≤ k) (i : Fin 3) :
    ∀ s ∈ keySlots i, s < k := by
  rcases i with ⟨v, hv⟩
  match v with
  | 0 => intro s hs; simp [keySlots] at hs; omega
  | 1 => intro s hs; simp [keySlots] at hs; omega
  | 2 => intro s hs; simp [keySlots] at hs; omega
  | _ + 3 => omega

lemma testBit_menuNat {h k start t : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k) (ht : t < 11) (i : Fin 3) :
    (menuNat h k start i).testBit ((start + h + k - 9 + t) % k) =
      (keySlots i).any (fun s => decide (s = t)) := by
  unfold menuNat
  rw [testBit_mkBits, List.any_map]
  have hts : ∀ s ∈ keySlots i, s < k := keySlots_lt (by omega) i
  have hcongr : ∀ (l : List Nat), (∀ s ∈ l, s < k) →
      l.any ((fun p => decide (p = (start + h + k - 9 + t) % k)) ∘
        fun s => (start + h + k - 9 + s) % k) =
      l.any (fun s => decide (s = t)) := by
    intro l hl
    induction l with
    | nil => rfl
    | cons s l ih =>
      simp only [List.any_cons, Function.comp_apply]
      have hs : s < k := hl s List.mem_cons_self
      have hiff := mod_add_eq_iff (base := start + h + k - 9) hs (by omega : t < k)
      have hdec : decide ((start + h + k - 9 + s) % k = (start + h + k - 9 + t) % k) =
          decide (s = t) := by
        by_cases he : s = t
        · subst he; simp
        · have hne : (start + h + k - 9 + s) % k ≠ (start + h + k - 9 + t) % k :=
            fun hc => he (hiff.mp hc)
          simp [he, hne]
      rw [hdec, ih (fun q hq => hl q (List.mem_cons_of_mem s hq))]
  exact hcongr (keySlots i) hts

lemma menuVal_injective {h k start : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k) :
    Function.Injective (menuVal h k start hh hk) := by
  intro i1 i2 heq
  have hval : menuNat h k start i1 = menuNat h k start i2 := congrArg Fin.val heq
  have hb3 := congrArg (fun x => x.testBit ((start + h + k - 9 + 3) % k)) hval
  have hb9 := congrArg (fun x => x.testBit ((start + h + k - 9 + 9) % k)) hval
  rw [testBit_menuNat hh hk (by omega) i1, testBit_menuNat hh hk (by omega) i2] at hb3
  rw [testBit_menuNat hh hk (by omega) i1, testBit_menuNat hh hk (by omega) i2] at hb9
  rcases i1 with ⟨v1, hv1⟩
  rcases i2 with ⟨v2, hv2⟩
  match v1, v2 with
  | 0, 0 => rfl
  | 0, 1 => simp [keySlots] at hb3
  | 0, 2 => simp [keySlots] at hb9
  | 1, 0 => simp [keySlots] at hb3
  | 1, 1 => rfl
  | 1, 2 => simp [keySlots] at hb3
  | 2, 0 => simp [keySlots] at hb9
  | 2, 1 => simp [keySlots] at hb3
  | 2, 2 => rfl
  | _ + 3, _ => omega
  | _, _ + 3 => omega

lemma tap_menuNat_row {h k start a back : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k)
    (ha : a ≤ 6) (hb : back ≤ 2) (i : Fin 3) :
    tap k start (menuNat h k start i) (h - 5 + a) back =
      (keySlots i).any (fun s => decide (s = 4 + a - back)) := by
  unfold tap
  have heq : start + (h - 5 + a) + k - back = start + h + k - 9 + (4 + a - back) := by omega
  rw [heq]
  exact testBit_menuNat hh hk (by omega) i

lemma tap_menuNat_col {h k start a back : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k)
    (ha : a ≤ 5) (hb : back ≤ 5) (i : Fin 3) :
    tap k start (menuNat h k start i) (h - 4 + a) back =
      (keySlots i).any (fun s => decide (s = 5 + a - back)) := by
  unfold tap
  have heq : start + (h - 4 + a) + k - back = start + h + k - 9 + (5 + a - back) := by omega
  rw [heq]
  exact testBit_menuNat hh hk (by omega) i

lemma pulse_row_menuNat {h k start a : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k) (ha : a ≤ 6) (i : Fin 3) :
    pulse k start false (menuNat h k start i) (h - 5 + a) =
      xor ((keySlots i).any (fun s => decide (s = 4 + a)))
        (xor ((keySlots i).any (fun s => decide (s = 3 + a)))
             ((keySlots i).any (fun s => decide (s = 2 + a)))) := by
  unfold pulse
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [tap_menuNat_row hh hk ha (by omega) i,
      tap_menuNat_row hh hk ha (by omega) i,
      tap_menuNat_row hh hk ha (by omega) i]
  have e0 : 4 + a - 0 = 4 + a := by omega
  have e1 : 4 + a - 1 = 3 + a := by omega
  have e2 : 4 + a - 2 = 2 + a := by omega
  rw [e0, e1, e2]

lemma pulse_col_menuNat {h k start a : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k) (ha : a ≤ 5) (i : Fin 3) :
    pulse k start true (menuNat h k start i) (h - 4 + a) =
      xor ((keySlots i).any (fun s => decide (s = 4 + a)))
        (xor ((keySlots i).any (fun s => decide (s = 2 + a)))
             ((keySlots i).any (fun s => decide (s = a)))) := by
  unfold pulse
  simp only [↓reduceIte]
  rw [tap_menuNat_col hh hk ha (by omega) i,
      tap_menuNat_col hh hk ha (by omega) i,
      tap_menuNat_col hh hk ha (by omega) i]
  have e1 : 5 + a - 1 = 4 + a := by omega
  have e3 : 5 + a - 3 = 2 + a := by omega
  have e5 : 5 + a - 5 = a := by omega
  rw [e1, e3, e5]

lemma menu0_ok {h k start : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k) (r c : Fin h → Bool)
    (hr : r ⟨h - 1, by omega⟩ = false)
    (hc : c ⟨h - 1, by omega⟩ = true ∨ c ⟨h - 2, by omega⟩ = false) :
    ok h k start (menuNat h k start 0) r c := by
  have pr0 : pulse k start false (menuNat h k start 0) (h - 5) = false := by
    have := pulse_row_menuNat (start := start) hh hk (a := 0) (by omega) 0
    have e : h - 5 + 0 = h - 5 := by omega
    rw [e] at this; rw [this]; rfl
  have pr1 : pulse k start false (menuNat h k start 0) (h - 4) = true := by
    have := pulse_row_menuNat (start := start) hh hk (a := 1) (by omega) 0
    have e : h - 5 + 1 = h - 4 := by omega
    rw [e] at this; rw [this]; rfl
  have pr2 : pulse k start false (menuNat h k start 0) (h - 3) = false := by
    have := pulse_row_menuNat (start := start) hh hk (a := 2) (by omega) 0
    have e : h - 5 + 2 = h - 3 := by omega
    rw [e] at this; rw [this]; rfl
  have pr3 : pulse k start false (menuNat h k start 0) (h - 2) = false := by
    have := pulse_row_menuNat (start := start) hh hk (a := 3) (by omega) 0
    have e : h - 5 + 3 = h - 2 := by omega
    rw [e] at this; rw [this]; rfl
  have pr4 : pulse k start false (menuNat h k start 0) (h - 1) = true := by
    have := pulse_row_menuNat (start := start) hh hk (a := 4) (by omega) 0
    have e : h - 5 + 4 = h - 1 := by omega
    rw [e] at this; rw [this]; rfl
  have pr5 : pulse k start false (menuNat h k start 0) h = true := by
    have := pulse_row_menuNat (start := start) hh hk (a := 5) (by omega) 0
    have e : h - 5 + 5 = h := by omega
    rw [e] at this; rw [this]; rfl
  have pr6 : pulse k start false (menuNat h k start 0) (h + 1) = false := by
    have := pulse_row_menuNat (start := start) hh hk (a := 6) (by omega) 0
    have e : h - 5 + 6 = h + 1 := by omega
    rw [e] at this; rw [this]; rfl
  have pc0 : pulse k start true (menuNat h k start 0) (h - 4) = true := by
    have := pulse_col_menuNat (start := start) hh hk (a := 0) (by omega) 0
    have e : h - 4 + 0 = h - 4 := by omega
    rw [e] at this; rw [this]; rfl
  have pc1 : pulse k start true (menuNat h k start 0) (h - 3) = false := by
    have := pulse_col_menuNat (start := start) hh hk (a := 1) (by omega) 0
    have e : h - 4 + 1 = h - 3 := by omega
    rw [e] at this; rw [this]; rfl
  have pc2 : pulse k start true (menuNat h k start 0) (h - 2) = true := by
    have := pulse_col_menuNat (start := start) hh hk (a := 2) (by omega) 0
    have e : h - 4 + 2 = h - 2 := by omega
    rw [e] at this; rw [this]; rfl
  have pc3 : pulse k start true (menuNat h k start 0) (h - 1) = true := by
    have := pulse_col_menuNat (start := start) hh hk (a := 3) (by omega) 0
    have e : h - 4 + 3 = h - 1 := by omega
    rw [e] at this; rw [this]; rfl
  have pc4 : pulse k start true (menuNat h k start 0) h = true := by
    have := pulse_col_menuNat (start := start) hh hk (a := 4) (by omega) 0
    have e : h - 4 + 4 = h := by omega
    rw [e] at this; rw [this]; rfl
  have pc5 : pulse k start true (menuNat h k start 0) (h + 1) = false := by
    have := pulse_col_menuNat (start := start) hh hk (a := 5) (by omega) 0
    have e : h - 4 + 5 = h + 1 := by omega
    rw [e] at this; rw [this]; rfl
  refine ⟨injOn_tail5_of_sim5 hh ?_, injOn_tail4_of_sim4 hh ?_⟩
  · rw [pr0, pr1, pr2, pr3, pr4, pr5, pr6, hr]
    exact sim5_inj_of_isInj5 _ _ _ _ _ _ _ _ _ _ _ _ (key0_row_ok _ _ _ _)
  · rw [pc0, pc1, pc2, pc3, pc4, pc5]
    exact sim4_inj_of_isInj4 _ _ _ _ _ _ _ _ _ _ (key0_col_ok _ _ _ _ hc)

lemma menu1_ok {h k start : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k) (r c : Fin h → Bool)
    (hr : r ⟨h - 1, by omega⟩ = true ∨ r ⟨h - 3, by omega⟩ = false)
    (hc : c ⟨h - 1, by omega⟩ = false) :
    ok h k start (menuNat h k start 1) r c := by
  have pr0 : pulse k start false (menuNat h k start 1) (h - 5) = true := by
    have := pulse_row_menuNat (start := start) hh hk (a := 0) (by omega) 1
    have e : h - 5 + 0 = h - 5 := by omega
    rw [e] at this; rw [this]; rfl
  have pr1 : pulse k start false (menuNat h k start 1) (h - 4) = false := by
    have := pulse_row_menuNat (start := start) hh hk (a := 1) (by omega) 1
    have e : h - 5 + 1 = h - 4 := by omega
    rw [e] at this; rw [this]; rfl
  have pr2 : pulse k start false (menuNat h k start 1) (h - 3) = true := by
    have := pulse_row_menuNat (start := start) hh hk (a := 2) (by omega) 1
    have e : h - 5 + 2 = h - 3 := by omega
    rw [e] at this; rw [this]; rfl
  have pr3 : pulse k start false (menuNat h k start 1) (h - 2) = true := by
    have := pulse_row_menuNat (start := start) hh hk (a := 3) (by omega) 1
    have e : h - 5 + 3 = h - 2 := by omega
    rw [e] at this; rw [this]; rfl
  have pr4 : pulse k start false (menuNat h k start 1) (h - 1) = true := by
    have := pulse_row_menuNat (start := start) hh hk (a := 4) (by omega) 1
    have e : h - 5 + 4 = h - 1 := by omega
    rw [e] at this; rw [this]; rfl
  have pr5 : pulse k start false (menuNat h k start 1) h = true := by
    have := pulse_row_menuNat (start := start) hh hk (a := 5) (by omega) 1
    have e : h - 5 + 5 = h := by omega
    rw [e] at this; rw [this]; rfl
  have pr6 : pulse k start false (menuNat h k start 1) (h + 1) = false := by
    have := pulse_row_menuNat (start := start) hh hk (a := 6) (by omega) 1
    have e : h - 5 + 6 = h + 1 := by omega
    rw [e] at this; rw [this]; rfl
  have pc0 : pulse k start true (menuNat h k start 1) (h - 4) = true := by
    have := pulse_col_menuNat (start := start) hh hk (a := 0) (by omega) 1
    have e : h - 4 + 0 = h - 4 := by omega
    rw [e] at this; rw [this]; rfl
  have pc1 : pulse k start true (menuNat h k start 1) (h - 3) = true := by
    have := pulse_col_menuNat (start := start) hh hk (a := 1) (by omega) 1
    have e : h - 4 + 1 = h - 3 := by omega
    rw [e] at this; rw [this]; rfl
  have pc2 : pulse k start true (menuNat h k start 1) (h - 2) = false := by
    have := pulse_col_menuNat (start := start) hh hk (a := 2) (by omega) 1
    have e : h - 4 + 2 = h - 2 := by omega
    rw [e] at this; rw [this]; rfl
  have pc3 : pulse k start true (menuNat h k start 1) (h - 1) = false := by
    have := pulse_col_menuNat (start := start) hh hk (a := 3) (by omega) 1
    have e : h - 4 + 3 = h - 1 := by omega
    rw [e] at this; rw [this]; rfl
  have pc4 : pulse k start true (menuNat h k start 1) h = true := by
    have := pulse_col_menuNat (start := start) hh hk (a := 4) (by omega) 1
    have e : h - 4 + 4 = h := by omega
    rw [e] at this; rw [this]; rfl
  have pc5 : pulse k start true (menuNat h k start 1) (h + 1) = true := by
    have := pulse_col_menuNat (start := start) hh hk (a := 5) (by omega) 1
    have e : h - 4 + 5 = h + 1 := by omega
    rw [e] at this; rw [this]; rfl
  refine ⟨injOn_tail5_of_sim5 hh ?_, injOn_tail4_of_sim4 hh ?_⟩
  · rw [pr0, pr1, pr2, pr3, pr4, pr5, pr6]
    exact sim5_inj_of_isInj5 _ _ _ _ _ _ _ _ _ _ _ _ (key1_row_ok _ _ _ _ _ hr)
  · rw [pc0, pc1, pc2, pc3, pc4, pc5, hc]
    exact sim4_inj_of_isInj4 _ _ _ _ _ _ _ _ _ _ (key1_col_ok _ _ _)

lemma menu2_ok {h k start : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k) (r c : Fin h → Bool)
    (hr : r ⟨h - 1, by omega⟩ = true ∨ r ⟨h - 3, by omega⟩ = true)
    (hc : c ⟨h - 1, by omega⟩ = true ∨ c ⟨h - 2, by omega⟩ = true) :
    ok h k start (menuNat h k start 2) r c := by
  have pr0 : pulse k start false (menuNat h k start 2) (h - 5) = true := by
    have := pulse_row_menuNat (start := start) hh hk (a := 0) (by omega) 2
    have e : h - 5 + 0 = h - 5 := by omega
    rw [e] at this; rw [this]; rfl
  have pr1 : pulse k start false (menuNat h k start 2) (h - 4) = true := by
    have := pulse_row_menuNat (start := start) hh hk (a := 1) (by omega) 2
    have e : h - 5 + 1 = h - 4 := by omega
    rw [e] at this; rw [this]; rfl
  have pr2 : pulse k start false (menuNat h k start 2) (h - 3) = true := by
    have := pulse_row_menuNat (start := start) hh hk (a := 2) (by omega) 2
    have e : h - 5 + 2 = h - 3 := by omega
    rw [e] at this; rw [this]; rfl
  have pr3 : pulse k start false (menuNat h k start 2) (h - 2) = true := by
    have := pulse_row_menuNat (start := start) hh hk (a := 3) (by omega) 2
    have e : h - 5 + 3 = h - 2 := by omega
    rw [e] at this; rw [this]; rfl
  have pr4 : pulse k start false (menuNat h k start 2) (h - 1) = true := by
    have := pulse_row_menuNat (start := start) hh hk (a := 4) (by omega) 2
    have e : h - 5 + 4 = h - 1 := by omega
    rw [e] at this; rw [this]; rfl
  have pr5 : pulse k start false (menuNat h k start 2) h = true := by
    have := pulse_row_menuNat (start := start) hh hk (a := 5) (by omega) 2
    have e : h - 5 + 5 = h := by omega
    rw [e] at this; rw [this]; rfl
  have pr6 : pulse k start false (menuNat h k start 2) (h + 1) = true := by
    have := pulse_row_menuNat (start := start) hh hk (a := 6) (by omega) 2
    have e : h - 5 + 6 = h + 1 := by omega
    rw [e] at this; rw [this]; rfl
  have pc0 : pulse k start true (menuNat h k start 2) (h - 4) = false := by
    have := pulse_col_menuNat (start := start) hh hk (a := 0) (by omega) 2
    have e : h - 4 + 0 = h - 4 := by omega
    rw [e] at this; rw [this]; rfl
  have pc1 : pulse k start true (menuNat h k start 2) (h - 3) = true := by
    have := pulse_col_menuNat (start := start) hh hk (a := 1) (by omega) 2
    have e : h - 4 + 1 = h - 3 := by omega
    rw [e] at this; rw [this]; rfl
  have pc2 : pulse k start true (menuNat h k start 2) (h - 2) = true := by
    have := pulse_col_menuNat (start := start) hh hk (a := 2) (by omega) 2
    have e : h - 4 + 2 = h - 2 := by omega
    rw [e] at this; rw [this]; rfl
  have pc3 : pulse k start true (menuNat h k start 2) (h - 1) = true := by
    have := pulse_col_menuNat (start := start) hh hk (a := 3) (by omega) 2
    have e : h - 4 + 3 = h - 1 := by omega
    rw [e] at this; rw [this]; rfl
  have pc4 : pulse k start true (menuNat h k start 2) h = true := by
    have := pulse_col_menuNat (start := start) hh hk (a := 4) (by omega) 2
    have e : h - 4 + 4 = h := by omega
    rw [e] at this; rw [this]; rfl
  have pc5 : pulse k start true (menuNat h k start 2) (h + 1) = true := by
    have := pulse_col_menuNat (start := start) hh hk (a := 5) (by omega) 2
    have e : h - 4 + 5 = h + 1 := by omega
    rw [e] at this; rw [this]; rfl
  refine ⟨injOn_tail5_of_sim5 hh ?_, injOn_tail4_of_sim4 hh ?_⟩
  · rw [pr0, pr1, pr2, pr3, pr4, pr5, pr6]
    exact sim5_inj_of_isInj5 _ _ _ _ _ _ _ _ _ _ _ _ (key2_row_ok _ _ _ _ _ hr)
  · rw [pc0, pc1, pc2, pc3, pc4, pc5]
    exact sim4_inj_of_isInj4 _ _ _ _ _ _ _ _ _ _ (key2_col_ok _ _ _ _ hc)

def askFn (h n : Nat) (hh : 5 ≤ h) (hist : List Bool) : Option (Fin n × Bool × Fin h) :=
  let t := hist.length
  if ht : t / 3 < n then
    let j : Fin n := ⟨t / 3, ht⟩
    match t % 3 with
    | 0 => some (j, true, ⟨h - 1, by omega⟩)
    | 1 =>
      if hist.getD 0 false then
        some (j, false, ⟨h - 1, by omega⟩)
      else
        some (j, true, ⟨h - 2, by omega⟩)
    | _ =>
      if hist.getD 1 false then
        none
      else if hist.getD 0 false then
        some (j, false, ⟨h - 3, by omega⟩)
      else
        some (j, false, ⟨h - 1, by omega⟩)
  else
    none

def outFn (n : Nat) (hist : List Bool) (j : Fin n) : Fin 3 :=
  let rev := hist.reverse
  let b0 := rev.getD (3 * j.val) false
  let b1 := rev.getD (3 * j.val + 1) false
  let b2 := rev.getD (3 * j.val + 2) false
  if b0 then (if b1 then 2 else 0)
  else if b1 then (if b2 then 2 else 1)
  else (if b2 then 1 else 0)

def stepBit (h n : Nat) (hh : 5 ≤ h) (r c : Fin n → Fin h → Bool) (t : Nat) : Bool :=
  if ht : t / 3 < n then
    let j : Fin n := ⟨t / 3, ht⟩
    match t % 3 with
    | 0 => c j ⟨h - 1, by omega⟩
    | 1 => if c j ⟨h - 1, by omega⟩ then r j ⟨h - 1, by omega⟩ else c j ⟨h - 2, by omega⟩
    | _ => if c j ⟨h - 1, by omega⟩ then false
           else if c j ⟨h - 2, by omega⟩ then r j ⟨h - 3, by omega⟩
           else r j ⟨h - 1, by omega⟩
  else
    false

lemma rev_map_range_succ (f : Nat → Bool) (m : Nat) :
    ((List.range (m + 1)).map f).reverse = f m :: ((List.range m).map f).reverse := by
  rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.reverse_append]
  rfl

lemma runTrace_askFn (h n : Nat) (hh : 5 ≤ h) (r c : Fin n → Fin h → Bool) (m : Nat) :
    runTrace n h (askFn h n hh) r c m = ((List.range m).map (stepBit h n hh r c)).reverse := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [runTrace_succ, ih, rev_map_range_succ]
    congr 1
    set hist := ((List.range m).map (stepBit h n hh r c)).reverse with hhist
    have hlen : hist.length = m := by
      simp [hhist]
    unfold askFn stepBit
    simp only [hlen]
    by_cases ht : m / 3 < n
    · simp only [ht, ↓reduceDIte]
      have hmod : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases hmod with hm0 | hm1 | hm2
      · simp [hm0]
      · obtain ⟨m1, rfl⟩ : ∃ m1, m = m1 + 1 := ⟨m - 1, by omega⟩
        have hhist1 : hist = stepBit h n hh r c m1 :: ((List.range m1).map (stepBit h n hh r c)).reverse := by
          rw [hhist, rev_map_range_succ]
        have hget0 : hist.getD 0 false = stepBit h n hh r c m1 := by
          rw [hhist1]; rfl
        have hd1 : m1 / 3 = (m1 + 1) / 3 := by omega
        have hmo1 : m1 % 3 = 0 := by omega
        have hsb0 : stepBit h n hh r c m1 = c ⟨(m1 + 1) / 3, ht⟩ ⟨h - 1, by omega⟩ := by
          unfold stepBit
          have ht1 : m1 / 3 < n := by omega
          simp only [ht1, ↓reduceDIte, hmo1]
          congr 1
          exact Fin.ext hd1
        simp only [hm1, hget0, hsb0]
        cases c ⟨(m1 + 1) / 3, ht⟩ ⟨h - 1, by omega⟩ <;> rfl
      · obtain ⟨m2, rfl⟩ : ∃ m2, m = m2 + 2 := ⟨m - 2, by omega⟩
        have hhist2 : hist = stepBit h n hh r c (m2 + 1) :: stepBit h n hh r c m2 ::
            ((List.range m2).map (stepBit h n hh r c)).reverse := by
          rw [hhist, rev_map_range_succ, rev_map_range_succ]
        have hget0 : hist.getD 0 false = stepBit h n hh r c (m2 + 1) := by
          rw [hhist2]; rfl
        have hget1 : hist.getD 1 false = stepBit h n hh r c m2 := by
          rw [hhist2]; rfl
        have hd1 : (m2 + 1) / 3 = (m2 + 2) / 3 := by omega
        have hd2 : m2 / 3 = (m2 + 2) / 3 := by omega
        have hmo1 : (m2 + 1) % 3 = 1 := by omega
        have hmo2 : m2 % 3 = 0 := by omega
        have hsb0 : stepBit h n hh r c m2 = c ⟨(m2 + 2) / 3, ht⟩ ⟨h - 1, by omega⟩ := by
          unfold stepBit
          have ht2 : m2 / 3 < n := by omega
          simp only [ht2, ↓reduceDIte, hmo2]
          congr 1
          exact Fin.ext hd2
        have hsb1 : stepBit h n hh r c (m2 + 1) =
            if c ⟨(m2 + 2) / 3, ht⟩ ⟨h - 1, by omega⟩ then r ⟨(m2 + 2) / 3, ht⟩ ⟨h - 1, by omega⟩
            else c ⟨(m2 + 2) / 3, ht⟩ ⟨h - 2, by omega⟩ := by
          unfold stepBit
          have ht1 : (m2 + 1) / 3 < n := by omega
          simp only [ht1, ↓reduceDIte, hmo1]
          have hfin : (⟨(m2 + 1) / 3, ht1⟩ : Fin n) = ⟨(m2 + 2) / 3, ht⟩ := Fin.ext hd1
          rw [hfin]
        simp only [hm2, hget0, hget1, hsb0, hsb1]
        cases c ⟨(m2 + 2) / 3, ht⟩ ⟨h - 1, by omega⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases c ⟨(m2 + 2) / 3, ht⟩ ⟨h - 2, by omega⟩ <;> rfl
        · rfl
    · simp [ht]

lemma getD_map_range (f : Nat → Bool) (q i : Nat) (hi : i < q) :
    ((List.range q).map f).getD i false = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma upper_bound (h k start n q : Nat) (hh : 5 ≤ h) (hk : h + 6 ≤ k) (hq : 3 * n ≤ q) :
    ∃ (menu : Fin 3 → Fin (2 ^ k)) (ask : List Bool → Option (Fin n × Bool × Fin h))
      (out : List Bool → Fin n → Fin 3),
      Function.Injective menu ∧ ∀ (r c : Fin n → Fin h → Bool),
        ∀ j, ok h k start (menu (out (runTrace n h ask r c q) j)).val (r j) (c j) := by
  refine ⟨menuVal h k start hh hk, askFn h n hh, outFn n, menuVal_injective hh hk, ?_⟩
  intro r c j
  rw [runTrace_askFn]
  dsimp only [outFn]
  rw [List.reverse_reverse]
  have hlt0 : 3 * j.val < q := by omega
  have hlt1 : 3 * j.val + 1 < q := by omega
  have hlt2 : 3 * j.val + 2 < q := by omega
  rw [getD_map_range _ q _ hlt0, getD_map_range _ q _ hlt1, getD_map_range _ q _ hlt2]
  have hb0 : stepBit h n hh r c (3 * j.val) = c j ⟨h - 1, by omega⟩ := by
    unfold stepBit
    have hd : (3 * j.val) / 3 = j.val := by omega
    have hm : (3 * j.val) % 3 = 0 := by omega
    have ht : (3 * j.val) / 3 < n := by omega
    simp only [ht, ↓reduceDIte, hm]
    congr 1
    exact Fin.ext hd
  have hb1 : stepBit h n hh r c (3 * j.val + 1) =
      if c j ⟨h - 1, by omega⟩ then r j ⟨h - 1, by omega⟩ else c j ⟨h - 2, by omega⟩ := by
    unfold stepBit
    have hd : (3 * j.val + 1) / 3 = j.val := by omega
    have hm : (3 * j.val + 1) % 3 = 1 := by omega
    have ht : (3 * j.val + 1) / 3 < n := by omega
    simp only [ht, ↓reduceDIte, hm]
    have hfin : (⟨(3 * j.val + 1) / 3, ht⟩ : Fin n) = j := Fin.ext hd
    rw [hfin]
  have hb2 : stepBit h n hh r c (3 * j.val + 2) =
      if c j ⟨h - 1, by omega⟩ then false
      else if c j ⟨h - 2, by omega⟩ then r j ⟨h - 3, by omega⟩
      else r j ⟨h - 1, by omega⟩ := by
    unfold stepBit
    have hd : (3 * j.val + 2) / 3 = j.val := by omega
    have hm : (3 * j.val + 2) % 3 = 2 := by omega
    have ht : (3 * j.val + 2) / 3 < n := by omega
    simp only [ht, ↓reduceDIte, hm]
    have hfin : (⟨(3 * j.val + 2) / 3, ht⟩ : Fin n) = j := Fin.ext hd
    rw [hfin]
  rw [hb0, hb1, hb2]
  cases hc1 : c j ⟨h - 1, by omega⟩
  · cases hc2 : c j ⟨h - 2, by omega⟩
    · cases hr1 : r j ⟨h - 1, by omega⟩
      · exact menu0_ok hh hk (r j) (c j) hr1 (Or.inr hc2)
      · exact menu1_ok hh hk (r j) (c j) (Or.inl hr1) hc1
    · cases hr3 : r j ⟨h - 3, by omega⟩
      · exact menu1_ok hh hk (r j) (c j) (Or.inr hr3) hc1
      · exact menu2_ok hh hk (r j) (c j) (Or.inr hr3) (Or.inr hc2)
  · cases hr1 : r j ⟨h - 1, by omega⟩
    · exact menu0_ok hh hk (r j) (c j) hr1 (Or.inl hc1)
    · exact menu2_ok hh hk (r j) (c j) (Or.inl hr1) (Or.inl hc1)

def mem3 (s : Bool × Bool × Bool) (i : Fin 3) : Bool :=
  match i with
  | ⟨0, _⟩ => s.1
  | ⟨1, _⟩ => s.2.1
  | ⟨2, _⟩ => s.2.2

lemma mem3_triple (g : Fin 3 → Bool) (i : Fin 3) :
    mem3 (g 0, g 1, g 2) i = g i := by
  rcases i with ⟨v, hv⟩
  match v with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => omega

def nonempty3 (s : Bool × Bool × Bool) : Bool :=
  s.1 || s.2.1 || s.2.2

def pick3 (s : Bool × Bool × Bool) : Fin 3 :=
  if s.1 then 0 else if s.2.1 then 1 else 2

lemma mem3_pick3 (s : Bool × Bool × Bool) (hs : nonempty3 s = true) :
    mem3 s (pick3 s) = true := by
  rcases s with ⟨a0, a1, a2⟩
  cases a0 <;> cases a1 <;> cases a2 <;> simp [nonempty3, pick3, mem3] at hs ⊢

def card3 (s : Bool × Bool × Bool) : Nat :=
  s.1.toNat + s.2.1.toNat + s.2.2.toNat

def fullUnion3 (a b : Bool × Bool × Bool) : Bool :=
  (a.1 || b.1) && (a.2.1 || b.2.1) && (a.2.2 || b.2.2)

def phi (a b : Bool × Bool × Bool) : Nat :=
  if card3 a = 3 ∧ card3 b = 3 then 3
  else if fullUnion3 a b = true ∧ 2 ≤ card3 a ∧ 2 ≤ card3 b then 2
  else if fullUnion3 a b = true then 1
  else 0

def split3 (s f : Bool × Bool × Bool) (bit : Bool) : Bool × Bool × Bool :=
  (s.1 && (f.1 == bit), s.2.1 && (f.2.1 == bit), s.2.2 && (f.2.2 == bit))

lemma mem3_split3_iff (s f : Bool × Bool × Bool) (bit : Bool) (i : Fin 3) :
    mem3 (split3 s f bit) i = true ↔ mem3 s i = true ∧ mem3 f i = bit := by
  rcases s with ⟨s0, s1, s2⟩
  rcases f with ⟨f0, f1, f2⟩
  rcases i with ⟨v, hv⟩
  match v with
  | 0 => simp [mem3, split3]
  | 1 => simp [mem3, split3]
  | 2 => simp [mem3, split3]
  | _ + 3 => omega

lemma nonempty3_of_mem3 {s : Bool × Bool × Bool} {i : Fin 3} (h : mem3 s i = true) :
    nonempty3 s = true := by
  rcases s with ⟨s0, s1, s2⟩
  rcases i with ⟨v, hv⟩
  match v with
  | 0 => simp [mem3] at h; simp [nonempty3, h]
  | 1 => simp [mem3] at h; simp [nonempty3, h]
  | 2 => simp [mem3] at h; simp [nonempty3, h]
  | _ + 3 => omega

lemma phi_symm (a b : Bool × Bool × Bool) : phi a b = phi b a := by
  rcases a with ⟨a0, a1, a2⟩
  rcases b with ⟨b0, b1, b2⟩
  cases a0 <;> cases a1 <;> cases a2 <;> cases b0 <;> cases b1 <;> cases b2 <;> rfl

lemma fullUnion3_of_phi_pos (a b : Bool × Bool × Bool) (h : 0 < phi a b) :
    fullUnion3 a b = true := by
  rcases a with ⟨a0, a1, a2⟩
  rcases b with ⟨b0, b1, b2⟩
  cases a0 <;> cases a1 <;> cases a2 <;> cases b0 <;> cases b1 <;> cases b2 <;>
    simp [phi, card3, fullUnion3] at h ⊢

lemma phi_ge_one_of_fullUnion3 (a b : Bool × Bool × Bool) (h : fullUnion3 a b = true) :
    1 ≤ phi a b := by
  unfold phi
  by_cases h3 : card3 a = 3 ∧ card3 b = 3
  · simp [h3]
  · by_cases h2 : fullUnion3 a b = true ∧ 2 ≤ card3 a ∧ 2 ≤ card3 b
    · simp [h3, h2]
    · have h2' : ¬(2 ≤ card3 a ∧ 2 ≤ card3 b) := fun hc => h2 ⟨h, hc⟩
      simp [h3, h2', h]

lemma mem3_or_of_fullUnion3 (a b : Bool × Bool × Bool) (h : fullUnion3 a b = true) (i : Fin 3) :
    mem3 a i = true ∨ mem3 b i = true := by
  rcases a with ⟨a0, a1, a2⟩
  rcases b with ⟨b0, b1, b2⟩
  rcases i with ⟨v, hv⟩
  match v with
  | 0 =>
    simp [fullUnion3] at h
    exact h.1.1
  | 1 =>
    simp [fullUnion3] at h
    exact h.1.2
  | 2 =>
    simp [fullUnion3] at h
    exact h.2
  | _ + 3 => omega

lemma split3_nonempty_exists (a f : Bool × Bool × Bool) (ha : nonempty3 a = true) :
    ∃ bit : Bool, nonempty3 (split3 a f bit) = true := by
  refine ⟨mem3 f (pick3 a), ?_⟩
  exact nonempty3_of_mem3 ((mem3_split3_iff a f _ _).mpr ⟨mem3_pick3 a ha, rfl⟩)

lemma phi_split_left (a b f : Bool × Bool × Bool) (ha : nonempty3 a = true) :
    ∃ bit : Bool, nonempty3 (split3 a f bit) = true ∧ phi a b ≤ phi (split3 a f bit) b + 1 := by
  by_cases h3 : card3 a = 3 ∧ card3 b = 3
  · have ha1 : a = (true, true, true) := by
      rcases a with ⟨a0, a1, a2⟩
      cases a0 <;> cases a1 <;> cases a2 <;> simp [card3] at h3 <;> rfl
    have hb1 : b = (true, true, true) := by
      rcases b with ⟨b0, b1, b2⟩
      cases b0 <;> cases b1 <;> cases b2 <;> simp [card3] at h3 <;> rfl
    subst ha1; subst hb1
    rcases f with ⟨f0, f1, f2⟩
    have hmaj : ∃ bit : Bool, 2 ≤ card3 (split3 (true, true, true) (f0, f1, f2) bit) := by
      cases f0 <;> cases f1 <;> cases f2
      · exact ⟨false, by decide⟩
      · exact ⟨false, by decide⟩
      · exact ⟨false, by decide⟩
      · exact ⟨true, by decide⟩
      · exact ⟨false, by decide⟩
      · exact ⟨true, by decide⟩
      · exact ⟨true, by decide⟩
      · exact ⟨true, by decide⟩
    rcases hmaj with ⟨bit, hcard⟩
    refine ⟨bit, ?_, ?_⟩
    · rcases hx : split3 (true, true, true) (f0, f1, f2) bit with ⟨x0, x1, x2⟩
      rw [hx] at hcard
      cases x0 <;> cases x1 <;> cases x2 <;> simp [card3, nonempty3] at hcard ⊢
    · have hfu : fullUnion3 (split3 (true, true, true) (f0, f1, f2) bit) (true, true, true) = true := by
        simp [fullUnion3]
      have hcb : card3 (true, true, true) = 3 := rfl
      have hphi1 : phi (true, true, true) (true, true, true) = 3 := rfl
      have hphi2 : 2 ≤ phi (split3 (true, true, true) (f0, f1, f2) bit) (true, true, true) := by
        unfold phi
        by_cases hc3 : card3 (split3 (true, true, true) (f0, f1, f2) bit) = 3 ∧ card3 (true, true, true) = 3
        · simp [hc3]
        · have hc3' : card3 (split3 (true, true, true) (f0, f1, f2) bit) ≠ 3 := fun hc => hc3 ⟨hc, hcb⟩
          simp [hc3', hfu, hcard, hcb]
      omega
  · by_cases h2 : fullUnion3 a b = true ∧ 2 ≤ card3 a ∧ 2 ≤ card3 b
    · have hphi_eq : phi a b = 2 := by
        unfold phi
        simp [h3, h2]
      by_cases hb3 : card3 b = 3
      · have hb1 : b = (true, true, true) := by
          rcases b with ⟨b0, b1, b2⟩
          cases b0 <;> cases b1 <;> cases b2 <;> simp [card3] at hb3 <;> rfl
        subst hb1
        rcases split3_nonempty_exists a f ha with ⟨bit, hne⟩
        refine ⟨bit, hne, ?_⟩
        have hfu : fullUnion3 (split3 a f bit) (true, true, true) = true := by
          simp [fullUnion3]
        have hge1 := phi_ge_one_of_fullUnion3 (split3 a f bit) (true, true, true) hfu
        omega
      · have hex : ∃ i : Fin 3, mem3 b i = false ∧ ∀ j : Fin 3, j ≠ i → mem3 b j = true := by
          have hcb := h2.2.2
          rcases b with ⟨b0, b1, b2⟩
          cases b0 <;> cases b1 <;> cases b2 <;> simp [card3] at hcb hb3
          · refine ⟨0, rfl, ?_⟩
            intro j hj
            rcases j with ⟨v, hv⟩
            match v with
            | 0 => exact absurd rfl hj
            | 1 => rfl
            | 2 => rfl
            | _ + 3 => omega
          · refine ⟨1, rfl, ?_⟩
            intro j hj
            rcases j with ⟨v, hv⟩
            match v with
            | 0 => rfl
            | 1 => exact absurd rfl hj
            | 2 => rfl
            | _ + 3 => omega
          · refine ⟨2, rfl, ?_⟩
            intro j hj
            rcases j with ⟨v, hv⟩
            match v with
            | 0 => rfl
            | 1 => rfl
            | 2 => exact absurd rfl hj
            | _ + 3 => omega
        rcases hex with ⟨i, hbi, hbj⟩
        have hai : mem3 a i = true := by
          rcases mem3_or_of_fullUnion3 a b h2.1 i with ha' | hb'
          · exact ha'
          · rw [hbi] at hb'; cases hb'
        have hmem : mem3 (split3 a f (mem3 f i)) i = true :=
          (mem3_split3_iff a f _ i).mpr ⟨hai, rfl⟩
        refine ⟨mem3 f i, nonempty3_of_mem3 hmem, ?_⟩
        have hfu : fullUnion3 (split3 a f (mem3 f i)) b = true := by
          have hc0 : mem3 (split3 a f (mem3 f i)) 0 = true ∨ mem3 b 0 = true := by
            by_cases h0 : (0 : Fin 3) = i
            · left; rw [h0]; exact hmem
            · right; exact hbj 0 h0
          have hc1 : mem3 (split3 a f (mem3 f i)) 1 = true ∨ mem3 b 1 = true := by
            by_cases h1 : (1 : Fin 3) = i
            · left; rw [h1]; exact hmem
            · right; exact hbj 1 h1
          have hc2 : mem3 (split3 a f (mem3 f i)) 2 = true ∨ mem3 b 2 = true := by
            by_cases h2' : (2 : Fin 3) = i
            · left; rw [h2']; exact hmem
            · right; exact hbj 2 h2'
          rcases hx : split3 a f (mem3 f i) with ⟨x0, x1, x2⟩
          rw [hx] at hc0 hc1 hc2
          rcases b with ⟨b0, b1, b2⟩
          simp [mem3] at hc0 hc1 hc2
          simp [fullUnion3, hc0, hc1, hc2]
        have hge1 := phi_ge_one_of_fullUnion3 (split3 a f (mem3 f i)) b hfu
        omega
    · rcases split3_nonempty_exists a f ha with ⟨bit, hne⟩
      refine ⟨bit, hne, ?_⟩
      have hle1 : phi a b ≤ 1 := by
        unfold phi
        by_cases hfu : fullUnion3 a b = true
        · have h2' : ¬(2 ≤ card3 a ∧ 2 ≤ card3 b) := fun hc => h2 ⟨hfu, hc⟩
          simp [h3, h2', hfu]
        · simp [h3, hfu]
      omega

lemma phi_split_right (a b f : Bool × Bool × Bool) (hb : nonempty3 b = true) :
    ∃ bit : Bool, nonempty3 (split3 b f bit) = true ∧ phi a b ≤ phi a (split3 b f bit) + 1 := by
  rcases phi_split_left b a f hb with ⟨bit, hne, hle⟩
  refine ⟨bit, hne, ?_⟩
  rw [phi_symm a b, phi_symm a (split3 b f bit)]
  exact hle

def sumFin : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f 0 + sumFin n (fun i => f i.succ)

lemma sumFin_const3 (n : Nat) : sumFin n (fun _ => 3) = 3 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold sumFin
    dsimp only
    rw [ih]
    omega

lemma sumFin_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i = g i) :
    sumFin n f = sumFin n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold sumFin
    rw [h 0, ih (fun i => h i.succ)]

lemma sumFin_update_le {n : Nat} {f g : Fin n → Nat} (j : Fin n)
    (heq : ∀ i, i ≠ j → f i = g i) (hj : f j ≤ g j + 1) :
    sumFin n f ≤ sumFin n g + 1 := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    revert heq hj
    refine Fin.cases ?_ ?_ j
    · intro heq0 hj0
      unfold sumFin
      have hrest : sumFin n (fun i => f i.succ) = sumFin n (fun i => g i.succ) :=
        sumFin_congr (fun i => heq0 i.succ (Fin.succ_ne_zero i))
      rw [hrest]
      omega
    · intro j' heqs hjs
      unfold sumFin
      have h0 : f 0 = g 0 := heqs 0 (Fin.succ_ne_zero j').symm
      have hrest := ih j' (fun i hi => heqs i.succ (fun hc => hi (Fin.succ_inj.mp hc))) hjs
      rw [h0]
      omega

lemma exists_pos_of_sumFin_pos {n : Nat} {f : Fin n → Nat} (h : 0 < sumFin n f) :
    ∃ j : Fin n, 0 < f j := by
  induction n with
  | zero => simp [sumFin] at h
  | succ n ih =>
    unfold sumFin at h
    by_cases h0 : 0 < f 0
    · exact ⟨0, h0⟩
    · have hrest : 0 < sumFin n (fun i => f i.succ) := by omega
      rcases ih hrest with ⟨j, hj⟩
      exact ⟨j.succ, hj⟩

lemma adversary_step (h n : Nat) (ask : List Bool → Option (Fin n × Bool × Fin h))
    (rBad cBad : Fin 3 → Fin h → Bool) (m : Nat) :
    ∃ (hist : List Bool) (A B : Fin n → Bool × Bool × Bool),
      (∀ j, nonempty3 (A j) = true ∧ nonempty3 (B j) = true) ∧
      3 * n ≤ sumFin n (fun j => phi (A j) (B j)) + m ∧
      ∀ (a b : Fin n → Fin 3),
        (∀ j, mem3 (A j) (a j) = true ∧ mem3 (B j) (b j) = true) →
        runTrace n h ask (fun j => rBad (a j)) (fun j => cBad (b j)) m = hist := by
  induction m with
  | zero =>
    refine ⟨[], fun _ => (true, true, true), fun _ => (true, true, true), ?_, ?_, ?_⟩
    · intro _; exact ⟨rfl, rfl⟩
    · have hphi : ∀ _ : Fin n, phi (true, true, true) (true, true, true) = 3 := fun _ => rfl
      rw [sumFin_congr hphi, sumFin_const3]
      omega
    · intro _ _ _; rfl
  | succ m ih =>
    rcases ih with ⟨hist, A, B, hne, hpot, htrace⟩
    cases hask : ask hist with
    | none =>
      refine ⟨false :: hist, A, B, hne, by omega, ?_⟩
      intro a b hab
      rw [runTrace_succ, htrace a b hab, hask]
      rfl
    | some q0 =>
      rcases q0 with ⟨j, isCol, pos⟩
      cases isCol with
      | false =>
        let f : Bool × Bool × Bool := (rBad 0 pos, rBad 1 pos, rBad 2 pos)
        rcases phi_split_left (A j) (B j) f (hne j).1 with ⟨bit, hneBit, hphiBit⟩
        let A' : Fin n → Bool × Bool × Bool := fun i => if i = j then split3 (A j) f bit else A i
        refine ⟨bit :: hist, A', B, ?_, ?_, ?_⟩
        · intro i
          by_cases hij : i = j
          · subst hij; exact ⟨by simp [A', hneBit], (hne i).2⟩
          · simp [A', hij, hne i]
        · have hup := sumFin_update_le
            (f := fun i => phi (A i) (B i)) (g := fun i => phi (A' i) (B i)) j
            (fun i hij => by simp [A', hij])
            (by simp [A']; exact hphiBit)
          omega
        · intro a b hab
          have habOld : ∀ i, mem3 (A i) (a i) = true ∧ mem3 (B i) (b i) = true := by
            intro i
            by_cases hij : i = j
            · subst hij
              have hsp := (hab i).1
              simp only [A', ↓reduceIte] at hsp
              exact ⟨((mem3_split3_iff (A i) f bit (a i)).mp hsp).1, (hab i).2⟩
            · have hi := hab i
              simp only [A', hij, ↓reduceIte] at hi
              exact hi
          have hbit : rBad (a j) pos = bit := by
            have hsp := (hab j).1
            simp only [A', ↓reduceIte] at hsp
            have hmf := ((mem3_split3_iff (A j) f bit (a j)).mp hsp).2
            rw [mem3_triple (fun x => rBad x pos) (a j)] at hmf
            exact hmf
          rw [runTrace_succ, htrace a b habOld, hask]
          simp [hbit]
      | true =>
        let f : Bool × Bool × Bool := (cBad 0 pos, cBad 1 pos, cBad 2 pos)
        rcases phi_split_right (A j) (B j) f (hne j).2 with ⟨bit, hneBit, hphiBit⟩
        let B' : Fin n → Bool × Bool × Bool := fun i => if i = j then split3 (B j) f bit else B i
        refine ⟨bit :: hist, A, B', ?_, ?_, ?_⟩
        · intro i
          by_cases hij : i = j
          · subst hij; exact ⟨(hne i).1, by simp [B', hneBit]⟩
          · simp [B', hij, hne i]
        · have hup := sumFin_update_le
            (f := fun i => phi (A i) (B i)) (g := fun i => phi (A i) (B' i)) j
            (fun i hij => by simp [B', hij])
            (by simp [B']; exact hphiBit)
          omega
        · intro a b hab
          have habOld : ∀ i, mem3 (A i) (a i) = true ∧ mem3 (B i) (b i) = true := by
            intro i
            by_cases hij : i = j
            · subst hij
              have hsp := (hab i).2
              simp only [B', ↓reduceIte] at hsp
              exact ⟨(hab i).1, ((mem3_split3_iff (B i) f bit (b i)).mp hsp).1⟩
            · have hi := hab i
              simp only [B', hij, ↓reduceIte] at hi
              exact hi
          have hbit : cBad (b j) pos = bit := by
            have hsp := (hab j).2
            simp only [B', ↓reduceIte] at hsp
            have hmf := ((mem3_split3_iff (B j) f bit (b j)).mp hsp).2
            rw [mem3_triple (fun x => cBad x pos) (b j)] at hmf
            exact hmf
          rw [runTrace_succ, htrace a b habOld, hask]
          simp [hbit]

lemma lower_bound (h k start n q : Nat) (hh : 5 ≤ h)
    (hex : ∃ (menu : Fin 3 → Fin (2 ^ k)) (ask : List Bool → Option (Fin n × Bool × Fin h))
        (out : List Bool → Fin n → Fin 3),
      Function.Injective menu ∧ ∀ (r c : Fin n → Fin h → Bool),
        ∀ j, ok h k start (menu (out (runTrace n h ask r c q) j)).val (r j) (c j)) :
    3 * n ≤ q := by
  by_contra hlt
  have hq : q < 3 * n := by omega
  rcases hex with ⟨menu, ask, out, _, hvalid⟩
  let rBad : Fin 3 → Fin h → Bool := fun i => badRow h k start (menu i).val
  let cBad : Fin 3 → Fin h → Bool := fun i => badCol h k start (menu i).val
  rcases adversary_step h n ask rBad cBad q with ⟨hist, A, B, hne, hpot, htrace⟩
  have hsumPos : 0 < sumFin n (fun j => phi (A j) (B j)) := by omega
  rcases exists_pos_of_sumFin_pos hsumPos with ⟨j0, hj0⟩
  have hfu : fullUnion3 (A j0) (B j0) = true := fullUnion3_of_phi_pos (A j0) (B j0) hj0
  let m0 : Fin 3 := out hist j0
  rcases mem3_or_of_fullUnion3 (A j0) (B j0) hfu m0 with hA | hB
  · let a : Fin n → Fin 3 := fun j => if j = j0 then m0 else pick3 (A j)
    let b : Fin n → Fin 3 := fun j => pick3 (B j)
    have hab : ∀ j, mem3 (A j) (a j) = true ∧ mem3 (B j) (b j) = true := by
      intro j
      refine ⟨?_, mem3_pick3 (B j) (hne j).2⟩
      by_cases hjj : j = j0
      · subst hjj; simp [a, hA]
      · simp [a, hjj, mem3_pick3 (A j) (hne j).1]
    have htr := htrace a b hab
    have hok := hvalid (fun j => rBad (a j)) (fun j => cBad (b j)) j0
    rw [htr] at hok
    have haj0 : a j0 = m0 := by simp [a]
    rw [haj0] at hok
    exact badRow_not_injOn h k start (menu m0).val hh hok.1
  · let a : Fin n → Fin 3 := fun j => pick3 (A j)
    let b : Fin n → Fin 3 := fun j => if j = j0 then m0 else pick3 (B j)
    have hab : ∀ j, mem3 (A j) (a j) = true ∧ mem3 (B j) (b j) = true := by
      intro j
      refine ⟨mem3_pick3 (A j) (hne j).1, ?_⟩
      by_cases hjj : j = j0
      · subst hjj; simp [b, hB]
      · simp [b, hjj, mem3_pick3 (B j) (hne j).2]
    have htr := htrace a b hab
    have hok := hvalid (fun j => rBad (a j)) (fun j => cBad (b j)) j0
    rw [htr] at hok
    have hbj0 : b j0 = m0 := by simp [b]
    rw [hbj0] at hok
    exact badCol_not_injOn h k start (menu m0).val hh hok.2

end PEqualNP.Outside.L_meta_39005

theorem PEqualNP.Outside.L_meta_39005 : ∀ (h k start n q : Nat), 5 ≤ h → h+6 ≤ k →
  let tap := fun (x j back : Nat) => x.testBit ((start+j+k-back) % k)
  let pulse := fun (col : Bool) (x j : Nat) =>
    if col then xor (tap x j 1) (xor (tap x j 3) (tap x j 5))
    else xor (tap x j 0) (xor (tap x j 1) (tap x j 2))
  let chi := fun (bits : Nat → Bool) (j : Nat) =>
    xor (bits j) (!(bits (j+1)) && bits (j+2))
  let fiber := fun (z : Fin h → Bool) =>
    {u : Nat | u < 2^(h+2) ∧ ∀ j : Fin h, chi (fun i => u.testBit i) j = z j}
  let tail := fun (col : Bool) (x len u : Nat) =>
    (Finset.range len).filter (fun j =>
      chi (fun i => xor (u.testBit i) (pulse col x i)) (h-len+j))
  let ok := fun (x : Nat) (r c : Fin h → Bool) =>
    Set.InjOn (tail false x 5) (fiber r) ∧ Set.InjOn (tail true x 4) (fiber c)
  let Query := Option (Fin n × Bool × Fin h)
  (∃ (menu : Fin 3 → Fin (2^k)) (ask : List Bool → Query)
      (out : List Bool → Fin n → Fin 3),
    Function.Injective menu ∧ ∀ (r c : Fin n → Fin h → Bool),
      let trace := (List.range q).foldl (fun (hist : List Bool) _ =>
        let bit := ((ask hist).map (fun u =>
          if u.2.1 then c u.1 u.2.2 else r u.1 u.2.2)).getD false
        bit :: hist) []
      ∀ j, ok (menu (out trace j)).val (r j) (c j)) ↔ 3*n ≤ q := by
  intro h k start n q hh hk
  exact ⟨PEqualNP.Outside.L_meta_39005.lower_bound h k start n q hh,
         PEqualNP.Outside.L_meta_39005.upper_bound h k start n q hh hk⟩
