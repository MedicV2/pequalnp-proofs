import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_549

def wordMap {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {q : ℕ}
    (A : Fin q → V →ₗ[K] V) : List (Fin q) → (V →ₗ[K] V)
  | [] => LinearMap.id
  | a :: w => (wordMap A w).comp (A a)

lemma wordMap_apply {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {q : ℕ}
    (A : Fin q → V →ₗ[K] V) (w : List (Fin q)) (x : V) :
    wordMap A w x = w.foldl (fun y a => A a y) x := by
  induction w generalizing x with
  | nil => rfl
  | cons a ws ih => exact ih (A a x)

def obsMap {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {q : ℕ}
    (A : Fin q → V →ₗ[K] V) (f : V →ₗ[K] K) : V →ₗ[K] (List (Fin q) → K) where
  toFun x w := f (w.foldl (fun y a => A a y) x)
  map_add' x y := by
    funext w
    simp only [← wordMap_apply, map_add, Pi.add_apply]
  map_smul' c x := by
    funext w
    simp only [← wordMap_apply, map_smul, Pi.smul_apply, RingHom.id_apply]

def dualStep {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (T : V →ₗ[K] V) : (V →ₗ[K] K) →ₗ[K] (V →ₗ[K] K) where
  toFun g := g.comp T
  map_add' g₁ g₂ := by ext x; rfl
  map_smul' c g := by ext x; rfl

def dualEquiv (K : Type) [Field K] (d : ℕ) : ((Fin d → K) →ₗ[K] K) ≃ₗ[K] (Fin d → K) where
  toFun g i := g (Pi.single i 1)
  invFun y :=
    { toFun := fun x => ∑ i : Fin d, x i * y i
      map_add' := fun x₁ x₂ => by
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv g := by
    ext x
    simp [Pi.single_apply]
  right_inv y := by
    ext i
    simp [Pi.single_apply]

lemma foldl_dual {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {q : ℕ}
    (A : Fin q → V →ₗ[K] V) (g : V →ₗ[K] K) (v : List (Fin q)) (x : V) :
    g (v.foldl (fun y a => A a y) x) =
      (v.reverse.foldl (fun h a => dualStep (A a) h) g) x := by
  induction v generalizing x with
  | nil => rfl
  | cons a vs ih =>
    simp only [List.foldl_cons, List.reverse_cons, List.foldl_append, List.foldl_nil]
    exact ih (A a x)

lemma exists_stabilize {K : Type} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
    [Module.Finite K W] (F : ℕ → Submodule K W) (hmono : ∀ k, F k ≤ F (k + 1)) :
    ∃ k ≤ Module.finrank K W, F k = F (k + 1) := by
  by_contra h
  push Not at h
  have hlt : ∀ k ≤ Module.finrank K W, F k < F (k + 1) := fun k hk =>
    lt_of_le_of_ne (hmono k) (h k hk)
  have hfin : ∀ n ≤ Module.finrank K W + 1, n ≤ Module.finrank K (F n) := by
    intro n
    induction n with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have h1 : k ≤ Module.finrank K (F k) := ih (by omega)
      have h2 : Module.finrank K (F k) < Module.finrank K (F (k + 1)) :=
        Submodule.finrank_lt_finrank_of_lt (hlt k (by omega))
      omega
  have htop := hfin (Module.finrank K W + 1) le_rfl
  have hle := Submodule.finrank_le (F (Module.finrank K W + 1))
  omega

lemma span_range_foldl_eq_short {K : Type} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
    [Module.Finite K W] {q : ℕ} (T : Fin q → W →ₗ[K] W) (x0 : W) :
    Submodule.span K (Set.range (fun w : List (Fin q) => w.foldl (fun x a => T a x) x0)) =
      Submodule.span K { y : W | ∃ w : List (Fin q), w.length < Module.finrank K W ∧
        w.foldl (fun x a => T a x) x0 = y } := by
  let F : ℕ → Submodule K W := fun k =>
    Submodule.span K { y : W | ∃ w : List (Fin q), w.length < k ∧
      w.foldl (fun x a => T a x) x0 = y }
  have hmono : ∀ k, F k ≤ F (k + 1) := fun k =>
    Submodule.span_mono (fun y ⟨w, hw, hy⟩ => ⟨w, by omega, hy⟩)
  have hle_mono : ∀ {a b}, a ≤ b → F a ≤ F b := fun {a b} hab =>
    Submodule.span_mono (fun y ⟨w, hw, hy⟩ => ⟨w, lt_of_lt_of_le hw hab, hy⟩)
  obtain ⟨k, hk, heq⟩ := exists_stabilize F hmono
  have hinv : ∀ a : Fin q, ∀ x ∈ F k, T a x ∈ F k := by
    intro a x hx
    have hsub : F k ≤ (F k).comap (T a) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨w, hw, rfl⟩
      change T a (w.foldl (fun y b => T b y) x0) ∈ F k
      rw [heq]
      refine Submodule.subset_span ⟨w ++ [a], by simp; omega, ?_⟩
      simp [List.foldl_append]
    exact hsub hx
  have hmem_foldl : ∀ (w : List (Fin q)) (x : W), x ∈ F k →
      w.foldl (fun y a => T a y) x ∈ F k := by
    intro w
    induction w with
    | nil => intro x hx; exact hx
    | cons a ws ih => intro x hx; exact ih (T a x) (hinv a x hx)
  have hx0 : x0 ∈ F k := by
    have hx1 : x0 ∈ F 1 := Submodule.subset_span ⟨[], by simp, rfl⟩
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [heq]; exact hx1
    · exact hle_mono hpos hx1
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨w, rfl⟩
    exact hle_mono hk (hmem_foldl w x0 hx0)
  · exact Submodule.span_mono (fun y ⟨w, _, hy⟩ => ⟨w, hy⟩)

lemma exists_linearIndependent_of_span_eq_top {K : Type} [Field K] {M : Type*}
    [AddCommGroup M] [Module K M] [Module.Finite K M]
    (S : Set M) (hspan : Submodule.span K S = ⊤) :
    ∀ k ≤ Module.finrank K M, ∃ u : Fin k → M, (∀ i, u i ∈ S) ∧ LinearIndependent K u := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, linearIndependent_empty_type⟩
  | succ k ih =>
    intro hk
    obtain ⟨u, huS, huInd⟩ := ih (by omega)
    have hne : Submodule.span K (Set.range u) ≠ ⊤ := by
      intro htop
      have hcard := finrank_span_eq_card huInd
      rw [htop, finrank_top, Fintype.card_fin] at hcard
      omega
    have hex : ∃ x ∈ S, x ∉ Submodule.span K (Set.range u) := by
      by_contra h
      push Not at h
      have htop : (⊤ : Submodule K M) ≤ Submodule.span K (Set.range u) := by
        rw [← hspan]
        exact Submodule.span_le.mpr h
      exact hne (top_unique htop)
    obtain ⟨x, hxS, hxnot⟩ := hex
    refine ⟨Fin.cons x u, fun i => Fin.cases hxS huS i, ?_⟩
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fin.sum_univ_succ] at hc
    have hc0 : c 0 = 0 := by
      by_contra h0
      have hxmem : x ∈ Submodule.span K (Set.range u) := by
        have hxeq : x = ∑ i : Fin k, -(((c 0)⁻¹ * c i.succ) • u i) := by
          have h1 : c 0 • x = -(∑ i : Fin k, c i.succ • u i) := eq_neg_of_add_eq_zero_left hc
          have h2 := congrArg (fun z => (c 0)⁻¹ • z) h1
          simp only [smul_smul, inv_mul_cancel₀ h0, one_smul, smul_neg, Finset.smul_sum,
            ← Finset.sum_neg_distrib] at h2
          exact h2
        rw [hxeq]
        exact Submodule.sum_mem _ fun i _ =>
          Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
      exact hxnot hxmem
    rw [hc0, zero_smul, zero_add] at hc
    have hctail := (Fintype.linearIndependent_iff.mp huInd) (fun i => c i.succ) hc
    intro i
    exact Fin.cases hc0 hctail i

lemma exists_nonzero_ortho_of_ne_top {K : Type} [Field K] {r : ℕ}
    (P : Submodule K (Fin r → K)) (hP : P ≠ ⊤) :
    ∃ c : Fin r → K, c ≠ 0 ∧ ∀ y ∈ P, ∑ i : Fin r, c i * y i = 0 := by
  let m := Module.finrank K P
  have hlt : m < r := by
    have h1 : m < Module.finrank K (Fin r → K) := Submodule.finrank_lt hP
    simpa [Module.finrank_fin_fun] using h1
  let b := Module.finBasis K P
  let L : (Fin r → K) →ₗ[K] (Fin m → K) :=
    { toFun := fun c t => ∑ i : Fin r, c i * (b t : Fin r → K) i
      map_add' := fun c₁ c₂ => by
        ext t; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun a c => by
        ext t; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hker : LinearMap.ker L ≠ ⊥ := by
    intro hbot
    have hsum := LinearMap.finrank_range_add_finrank_ker L
    rw [hbot, finrank_bot, add_zero] at hsum
    have hle : Module.finrank K (LinearMap.range L) ≤ Module.finrank K (Fin m → K) :=
      Submodule.finrank_le _
    rw [Module.finrank_fin_fun] at hsum hle
    omega
  obtain ⟨c, hc_ker, hc_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨c, hc_ne, ?_⟩
  let φ : (Fin r → K) →ₗ[K] K :=
    { toFun := fun y => ∑ i : Fin r, c i * y i
      map_add' := fun y₁ y₂ => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun a y => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring }
  intro y hy
  change (φ.comp P.subtype) ⟨y, hy⟩ = 0
  rw [← b.sum_repr ⟨y, hy⟩, map_sum]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [map_smul, smul_eq_mul]
  have ht : (φ.comp P.subtype) (b t) = 0 := congrFun (LinearMap.mem_ker.mp hc_ker) t
  rw [ht, mul_zero]

end PEqualNP.Outside.L_lib_549

theorem PEqualNP.Outside.L_lib_549 : ∀ (K : Type) [Field K] (q d : ℕ),
  let V := Fin d → K
  ∀ (s : V) (A : Fin q → V →ₗ[K] V),
    let run := fun (w : List (Fin q)) => w.foldl (fun x a => A a x) s
    ∀ f : V →ₗ[K] K,
      let val := fun w => f (run w)
      let R := Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => val (u ++ v)))
      let r := Module.finrank K R
      ∃ U W : Fin r → List (Fin q),
        (∀ i, (U i).length < d ∧ (W i).length < d) ∧
        (Matrix.of (fun i j : Fin r => val (U i ++ W j))).det ≠ 0 := by
  intro K _ q d V s A run f val R r
  let obs := PEqualNP.Outside.L_lib_549.obsMap A f
  have hobs_run : ∀ u : List (Fin q), obs (run u) = fun v : List (Fin q) => val (u ++ v) := by
    intro u
    funext v
    change f (v.foldl (fun y a => A a y) (u.foldl (fun y a => A a y) s)) =
      f ((u ++ v).foldl (fun y a => A a y) s)
    rw [List.foldl_append]
  have hR_map : R = Submodule.map obs (Submodule.span K (Set.range run)) := by
    change Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => val (u ++ v))) = _
    rw [Submodule.map_span]
    congr 1
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨run u, ⟨u, rfl⟩, hobs_run u⟩
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, (hobs_run u).symm⟩
  have : Module.Finite K R := by
    rw [hR_map]
    exact Module.Finite.map _ _
  have hfwd : Submodule.span K (Set.range run) =
      Submodule.span K { y : V | ∃ u : List (Fin q), u.length < d ∧ run u = y } := by
    simpa [V, Module.finrank_fin_fun] using
      PEqualNP.Outside.L_lib_549.span_range_foldl_eq_short A s
  have hR_short : R = Submodule.span K
      { g : List (Fin q) → K | ∃ u : List (Fin q), u.length < d ∧
        (fun v : List (Fin q) => val (u ++ v)) = g } := by
    rw [hR_map, hfwd, Submodule.map_span]
    congr 1
    ext g
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, (hobs_run u).symm⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨run u, ⟨u, hu, rfl⟩, hobs_run u⟩
  have hR_mem : ∀ u : List (Fin q), (fun v : List (Fin q) => val (u ++ v)) ∈ R := fun u =>
    Submodule.subset_span ⟨u, rfl⟩
  let S_R : Set R :=
    { z : R | ∃ u : List (Fin q), u.length < d ∧ (z : List (Fin q) → K) = fun v => val (u ++ v) }
  have hspanR : Submodule.span K S_R = ⊤ := by
    apply Submodule.map_injective_of_injective R.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    have himg : R.subtype '' S_R =
        { g : List (Fin q) → K | ∃ u : List (Fin q), u.length < d ∧
          (fun v : List (Fin q) => val (u ++ v)) = g } := by
      ext g
      constructor
      · rintro ⟨z, ⟨u, hu, hz⟩, rfl⟩
        exact ⟨u, hu, hz.symm⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨⟨fun v => val (u ++ v), hR_mem u⟩, ⟨u, hu, rfl⟩, rfl⟩
    rw [himg]
    exact hR_short.symm
  obtain ⟨z, hzS, hzInd⟩ :=
    PEqualNP.Outside.L_lib_549.exists_linearIndependent_of_span_eq_top S_R hspanR r le_rfl
  let U : Fin r → List (Fin q) := fun i => Classical.choose (hzS i)
  have hU_len : ∀ i : Fin r, (U i).length < d := fun i => (Classical.choose_spec (hzS i)).1
  have hU_eq : ∀ i : Fin r, (z i : List (Fin q) → K) = fun v => val (U i ++ v) := fun i =>
    (Classical.choose_spec (hzS i)).2
  have hU_ind : LinearIndependent K (fun i : Fin r => fun v : List (Fin q) => val (U i ++ v)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    refine (Fintype.linearIndependent_iff.mp hzInd) c ?_
    apply Subtype.ext
    simpa [Submodule.coe_sum, Submodule.coe_smul, hU_eq] using hc
  let eDual := PEqualNP.Outside.L_lib_549.dualEquiv K d
  have : Module.Finite K (V →ₗ[K] K) := Module.Finite.equiv eDual.symm
  have hfinDual : Module.finrank K (V →ₗ[K] K) = d := by
    rw [LinearEquiv.finrank_eq eDual, Module.finrank_fin_fun]
  have hbwd := PEqualNP.Outside.L_lib_549.span_range_foldl_eq_short
    (fun a => PEqualNP.Outside.L_lib_549.dualStep (A a)) f
  rw [hfinDual] at hbwd
  have hsep : ∀ φ ∈ R, (∀ v : List (Fin q), v.length < d → φ v = 0) → φ = 0 := by
    intro φ hφ hzero
    rw [hR_map] at hφ
    obtain ⟨x, _, rfl⟩ := hφ
    let evalX : (V →ₗ[K] K) →ₗ[K] K :=
      { toFun := fun g => g x
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let Ann : Submodule K (V →ₗ[K] K) := LinearMap.ker evalX
    have hshort_le : Submodule.span K { g : V →ₗ[K] K | ∃ w : List (Fin q), w.length < d ∧
        w.foldl (fun h a => PEqualNP.Outside.L_lib_549.dualStep (A a) h) f = g } ≤ Ann := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨w, hw, rfl⟩
      change (w.foldl (fun h a => PEqualNP.Outside.L_lib_549.dualStep (A a) h) f) x = 0
      have hrev := PEqualNP.Outside.L_lib_549.foldl_dual A f w.reverse x
      rw [List.reverse_reverse] at hrev
      rw [← hrev]
      exact hzero w.reverse (by simpa using hw)
    have hall_le : Submodule.span K (Set.range (fun w : List (Fin q) =>
        w.foldl (fun h a => PEqualNP.Outside.L_lib_549.dualStep (A a) h) f)) ≤ Ann := by
      rw [hbwd]
      exact hshort_le
    funext v
    change f (v.foldl (fun y a => A a y) x) = 0
    rw [PEqualNP.Outside.L_lib_549.foldl_dual]
    exact hall_le (Submodule.subset_span ⟨v.reverse, rfl⟩)
  let S_col : Set (Fin r → K) :=
    { y : Fin r → K | ∃ v : List (Fin q), v.length < d ∧ y = fun i => val (U i ++ v) }
  have hspanCol : Submodule.span K S_col = ⊤ := by
    by_contra hne
    obtain ⟨c, hc_ne, hc_ortho⟩ :=
      PEqualNP.Outside.L_lib_549.exists_nonzero_ortho_of_ne_top (Submodule.span K S_col) hne
    let φ : List (Fin q) → K := ∑ i : Fin r, c i • (fun v : List (Fin q) => val (U i ++ v))
    have hφR : φ ∈ R :=
      Submodule.sum_mem R fun i _ => Submodule.smul_mem R (c i) (hR_mem (U i))
    have hφ0 : φ = 0 := by
      refine hsep φ hφR fun v hv => ?_
      have hv_mem : (fun i => val (U i ++ v)) ∈ Submodule.span K S_col :=
        Submodule.subset_span ⟨v, hv, rfl⟩
      simpa [φ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hc_ortho _ hv_mem
    have hc0 : ∀ i : Fin r, c i = 0 := (Fintype.linearIndependent_iff.mp hU_ind) c hφ0
    exact hc_ne (funext hc0)
  obtain ⟨y, hyS, hyInd⟩ :=
    PEqualNP.Outside.L_lib_549.exists_linearIndependent_of_span_eq_top S_col hspanCol r
      (by rw [Module.finrank_fin_fun])
  let W : Fin r → List (Fin q) := fun j => Classical.choose (hyS j)
  have hW_len : ∀ j : Fin r, (W j).length < d := fun j => (Classical.choose_spec (hyS j)).1
  have hW_eq : ∀ j : Fin r, y j = fun i => val (U i ++ W j) := fun j =>
    (Classical.choose_spec (hyS j)).2
  refine ⟨U, W, fun i => ⟨hU_len i, hW_len i⟩, ?_⟩
  let M : Matrix (Fin r) (Fin r) K := Matrix.of (fun i j : Fin r => val (U i ++ W j))
  have hcol : M.col = y := by
    ext j i
    exact (congrFun (hW_eq j) i).symm
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det M).mp
    (Matrix.linearIndependent_col_iff_isUnit.mp (hcol ▸ hyInd)))
