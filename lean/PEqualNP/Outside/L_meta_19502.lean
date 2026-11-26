import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19502

open PEqualNP.CircuitLowerBounds

def A : Fin 5 → Fin 5 → Bool :=
  fun u v : Fin 5 => (7641305 : ℕ).testBit (5 * u.val + v.val)

def upperC : Circuit :=
  { gates :=
      [
        { op := GateOp.or, inputs := [6, 7] },
        { op := GateOp.or, inputs := [0, 3] },
        { op := GateOp.and, inputs := [4, 5] },
        { op := GateOp.and, inputs := [10, 11] },
        { op := GateOp.or, inputs := [11, 12] },
        { op := GateOp.and, inputs := [3, 9] },
        { op := GateOp.or, inputs := [13, 15] },
        { op := GateOp.not, inputs := [16] },
        { op := GateOp.or, inputs := [10, 14] },
        { op := GateOp.and, inputs := [17, 18] }
      ],
    output := 19 }

theorem upper_fanInTwo : PEqualNP.MetaComplexity.FanInTwo upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_19502

theorem PEqualNP.Outside.L_meta_19502 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7641305 : ℕ).testBit (5 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19502.upperC, PEqualNP.Outside.L_meta_19502.upper_fanInTwo, by decide,
    PEqualNP.Outside.L_meta_19502.upper_rep⟩
