import Mathlib.Data.ZMod.Units
import Mathlib.Logic.Equiv.Fin.Basic

/-! Coprime integers as a unit residue and an actual Euclidean quotient. -/

namespace GapFamily.Analytic.PoincareFourierArithmetic

/-- The ordinary residue and quotient decomposition, restricted to integers
coprime to the positive modulus. Modulus one is included. -/
def coprimeResidueEquiv (c : ℕ) [NeZero c] :
    {d : ℤ // IsCoprime (c : ℤ) d} ≃ (ZMod c)ˣ × ℤ where
  toFun d := (ZMod.unitOfIsCoprime d.val d.property.symm, d.val / (c : ℤ))
  invFun p := ⟨((p.1 : ZMod c).val : ℤ) + p.2 * (c : ℤ), by
    apply (ZMod.coe_int_isUnit_iff_isCoprime _ c).mp
    convert p.1.isUnit using 1
    simp⟩
  left_inv d := by
    apply Subtype.ext
    change ((ZMod.unitOfIsCoprime d.val d.property.symm : ZMod c).val : ℤ) +
      d.val / (c : ℤ) * (c : ℤ) = d.val
    rw [ZMod.coe_unitOfIsCoprime, ZMod.val_intCast, Int.mul_comm]
    exact Int.emod_add_mul_ediv d.val (c : ℤ)
  right_inv p := by
    apply Prod.ext
    · apply Units.ext
      simp
    · change (((p.1 : ZMod c).val : ℤ) + p.2 * (c : ℤ)) / (c : ℤ) = p.2
      rw [Int.add_mul_ediv_right _ _ (Int.natCast_ne_zero.mpr (NeZero.ne c)),
        Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _)
          (Int.ofNat_lt.mpr (ZMod.val_lt (p.1 : ZMod c))), zero_add]

@[simp] theorem coprimeResidueEquiv_apply (c : ℕ) [NeZero c]
    (d : {d : ℤ // IsCoprime (c : ℤ) d}) :
    coprimeResidueEquiv c d =
      (ZMod.unitOfIsCoprime d.val d.property.symm, d.val / (c : ℤ)) := rfl

@[simp] theorem coprimeResidueEquiv_apply_fst_coe (c : ℕ) [NeZero c]
    (d : {d : ℤ // IsCoprime (c : ℤ) d}) :
    ((coprimeResidueEquiv c d).1 : ZMod c) = (d.val : ZMod c) := rfl

@[simp] theorem coprimeResidueEquiv_apply_snd (c : ℕ) [NeZero c]
    (d : {d : ℤ // IsCoprime (c : ℤ) d}) :
    (coprimeResidueEquiv c d).2 = d.val / (c : ℤ) := rfl

@[simp] theorem coprimeResidueEquiv_symm_apply_val (c : ℕ) [NeZero c]
    (u : (ZMod c)ˣ) (k : ℤ) :
    ((coprimeResidueEquiv c).symm (u, k)).val =
      ((u : ZMod c).val : ℤ) + k * (c : ℤ) := rfl

end GapFamily.Analytic.PoincareFourierArithmetic
