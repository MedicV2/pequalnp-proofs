import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_lib_1498 : letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let cover := fun {N : Nat} (G : Finset (Fin N × Fin N)) (C : Finset (Fin N)) =>
  ∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C
let opt := fun {N : Nat} (G : Finset (Fin N × Fin N)) (w : Fin N → Nat) (C : Finset (Fin N)) =>
  cover G C ∧ ∀ B, cover G B → C.sum w ≤ B.sum w
let bip := fun {N : Nat} (G : Finset (Fin N × Fin N)) (D S : Finset (Fin N)) =>
  ∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ S ↔ e.2 ∉ S)
let view := fun {k N : Nat} (p : Fin k → Fin N) (C : Finset (Fin N)) =>
  Finset.univ.filter (fun i => p i ∈ C)
let meet := fun {k : Nat} (P X Y : Finset (Fin k)) => ((X ∩ Y) \ P) ∪ ((X ∪ Y) ∩ P)
let join := fun {k : Nat} (P X Y : Finset (Fin k)) => ((X ∪ Y) \ P) ∪ ((X ∩ Y) ∩ P)
∀ (k N : Nat) (G : Finset (Fin N × Fin N)) (w : Fin N → Nat) (p : Fin k → Fin N)
  (D S I O : Finset (Fin N)), bip G D S →
let sel := fun (C : Finset (Fin N)) => opt G w C ∧ I ⊆ C ∧ Disjoint O C
let F := fun (Z : Finset (Fin N)) =>
  Finset.univ.filter (fun X : Finset (Fin k) => ∃ C, sel C ∧ C ∩ D=Z ∧ view p C=X)
let P := Finset.univ.filter (fun i => p i ∈ S \ D)
(∀ X : Finset (Fin k), (∃ C, sel C ∧ view p C=X) ↔ ∃ Z ∈ D.powerset, X ∈ F Z) ∧
(∀ Z ∈ D.powerset, ∀ X ∈ F Z, ∀ Y ∈ F Z, meet P X Y ∈ F Z ∧ join P X Y ∈ F Z) ∧
((∀ C B, sel C → sel B → view p C=view p B → C=B) →
  ∀ Z ∈ D.powerset, ∀ T ∈ D.powerset, Z ≠ T → Disjoint (F Z) (F T)) := by
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  intro cover opt bip view meet join k N G w p D S I O hbip sel F P
  refine ⟨?_, ?_, ?_⟩
  · intro X
    constructor
    · rintro ⟨C, hC, rfl⟩
      refine ⟨C ∩ D, Finset.mem_powerset.2 Finset.inter_subset_right, ?_⟩
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨C, hC, rfl, rfl⟩
    · rintro ⟨Z, -, hX⟩
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hX
      obtain ⟨C, hC, -, h⟩ := hX
      exact ⟨C, hC, h⟩
  · intro Z _ X hX Y hY
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hX hY ⊢
    obtain ⟨C, hC, hCZ, rfl⟩ := hX
    obtain ⟨B, hB, hBZ, rfl⟩ := hY
    obtain ⟨⟨hCc, hCo⟩, hCI, hCO⟩ := hC
    obtain ⟨⟨hBc, hBo⟩, hBI, hBO⟩ := hB
    have hD : ∀ x ∈ D, (x ∈ C ↔ x ∈ B) := by
      intro x hx
      have h1 : x ∈ C ∩ D ↔ x ∈ B ∩ D := by rw [hCZ, hBZ]
      simp only [Finset.mem_inter] at h1
      tauto
    have hZ : ∀ x, x ∈ Z ↔ x ∈ C ∧ x ∈ D := by
      intro x; rw [← hCZ, Finset.mem_inter]
    let M := ((C ∩ B) \ S) ∪ ((C ∪ B) ∩ S)
    let J := ((C ∪ B) \ S) ∪ ((C ∩ B) ∩ S)
    have mM : ∀ x, x ∈ M ↔ ((x ∈ C ∧ x ∈ B) ∧ x ∉ S) ∨ ((x ∈ C ∨ x ∈ B) ∧ x ∈ S) := by
      intro x; simp only [M, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    have mJ : ∀ x, x ∈ J ↔ ((x ∈ C ∨ x ∈ B) ∧ x ∉ S) ∨ ((x ∈ C ∧ x ∈ B) ∧ x ∈ S) := by
      intro x; simp only [J, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    have covM : cover G M := by
      intro e he
      have h1 := hCc e he
      have h2 := hBc e he
      have hb := hbip e he
      have d1 := hD e.1
      have d2 := hD e.2
      rw [mM, mM]
      by_cases a1 : e.1 ∈ D <;> by_cases a2 : e.2 ∈ D <;> by_cases s1 : e.1 ∈ S <;>
        by_cases s2 : e.2 ∈ S <;> simp_all <;> tauto
    have covJ : cover G J := by
      intro e he
      have h1 := hCc e he
      have h2 := hBc e he
      have hb := hbip e he
      have d1 := hD e.1
      have d2 := hD e.2
      rw [mJ, mJ]
      by_cases a1 : e.1 ∈ D <;> by_cases a2 : e.2 ∈ D <;> by_cases s1 : e.1 ∈ S <;>
        by_cases s2 : e.2 ∈ S <;> simp_all <;> tauto
    have u1 : M ∪ J = C ∪ B := by
      ext x; simp only [Finset.mem_union, mM, mJ]; tauto
    have u2 : M ∩ J = C ∩ B := by
      ext x; simp only [Finset.mem_inter, mM, mJ]; tauto
    have hs : M.sum w + J.sum w = C.sum w + B.sum w := by
      rw [← Finset.sum_union_inter, u1, u2, Finset.sum_union_inter]
    have e1 := hCo M covM
    have e2 := hBo J covJ
    have vw : ∀ (T : Finset (Fin N)) i, i ∈ view p T ↔ p i ∈ T := by
      intro T i; simp [view]
    have Pm : ∀ i, i ∈ P ↔ p i ∈ S ∧ p i ∉ D := by
      intro i; simp [P]
    refine ⟨⟨M, ⟨⟨covM, fun B' hB' => ?_⟩, ?_, ?_⟩, ?_, ?_⟩,
      ⟨J, ⟨⟨covJ, fun B' hB' => ?_⟩, ?_, ?_⟩, ?_, ?_⟩⟩
    · exact (Nat.le_of_add_le_add_right (hs.trans_le (Nat.add_le_add_left e2 _))).trans (hCo B' hB')
    · intro x hx; rw [mM]; have := hCI hx; have := hBI hx; tauto
    · rw [Finset.disjoint_left]; intro x hx hxM; rw [mM] at hxM
      have := Finset.disjoint_left.1 hCO hx; have := Finset.disjoint_left.1 hBO hx; tauto
    · ext x; rw [Finset.mem_inter, mM, hZ]; have := hD x; tauto
    · ext i; simp only [meet, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, vw, Pm, mM]
      have := hD (p i)
      by_cases a : p i ∈ D <;> by_cases b : p i ∈ S <;> by_cases c : p i ∈ C <;>
        by_cases d : p i ∈ B <;> simp_all
    · exact (Nat.le_of_add_le_add_left (hs.trans_le (Nat.add_le_add_right e1 _))).trans (hBo B' hB')
    · intro x hx; rw [mJ]; have := hCI hx; have := hBI hx; tauto
    · rw [Finset.disjoint_left]; intro x hx hxM; rw [mJ] at hxM
      have := Finset.disjoint_left.1 hCO hx; have := Finset.disjoint_left.1 hBO hx; tauto
    · ext x; rw [Finset.mem_inter, mJ, hZ]; have := hD x; tauto
    · ext i; simp only [join, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, vw, Pm, mJ]
      have := hD (p i)
      by_cases a : p i ∈ D <;> by_cases b : p i ∈ S <;> by_cases c : p i ∈ C <;>
        by_cases d : p i ∈ B <;> simp_all
  · intro hinj Z _ T _ hZT
    rw [Finset.disjoint_left]
    intro X hX hY
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hX hY
    obtain ⟨C, hC, hCZ, rfl⟩ := hX
    obtain ⟨B, hB, hBT, hv⟩ := hY
    exact hZT (by rw [← hCZ, ← hBT, hinj C B hC hB hv.symm])
