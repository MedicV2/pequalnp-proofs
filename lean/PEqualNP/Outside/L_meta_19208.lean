import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19208

open PEqualNP.CircuitLowerBounds

def A : Fin 4 → Fin 4 → Bool :=
  fun u v : Fin 4 => (311 : ℕ).testBit (4 * u.val + v.val)

def upperC : Circuit :=
  { gates :=
      [
        { op := GateOp.or, inputs := [0, 4] },
        { op := GateOp.and, inputs := [1, 5] },
        { op := GateOp.or, inputs := [3, 7] },
        { op := GateOp.or, inputs := [8, 9] },
        { op := GateOp.not, inputs := [10] },
        { op := GateOp.and, inputs := [11, 12] }
      ],
    output := 13 }

theorem upper_fanInTwo : PEqualNP.MetaComplexity.FanInTwo upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_19208

theorem PEqualNP.Outside.L_meta_19208 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (311 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19208.upperC, PEqualNP.Outside.L_meta_19208.upper_fanInTwo, by decide,
    PEqualNP.Outside.L_meta_19208.upper_rep⟩
