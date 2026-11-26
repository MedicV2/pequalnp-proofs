import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19476

open PEqualNP.CircuitLowerBounds

def A : Fin 5 → Fin 5 → Bool :=
  fun u v : Fin 5 => (16221750 : ℕ).testBit (5 * u.val + v.val)

def upperC : Circuit :=
  { gates :=
      [
        { op := GateOp.or, inputs := [4, 5] },
        { op := GateOp.or, inputs := [3, 10] },
        { op := GateOp.or, inputs := [0, 11] },
        { op := GateOp.or, inputs := [9, 12] },
        { op := GateOp.or, inputs := [2, 8] },
        { op := GateOp.or, inputs := [0, 9] },
        { op := GateOp.or, inputs := [11, 14] },
        { op := GateOp.and, inputs := [15, 16] },
        { op := GateOp.not, inputs := [17] },
        { op := GateOp.and, inputs := [13, 18] }
      ],
    output := 19 }

theorem upper_fanInTwo : PEqualNP.MetaComplexity.FanInTwo upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_19476

theorem PEqualNP.Outside.L_meta_19476 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16221750 : ℕ).testBit (5 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19476.upperC, PEqualNP.Outside.L_meta_19476.upper_fanInTwo, by decide,
    PEqualNP.Outside.L_meta_19476.upper_rep⟩
