import GapFamily.Analytic.Transform.CosRoot
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Finite Kloosterman sums and the higher kernel

Denominators are indexed by `n : ℕ` and have value `n + 1`, so zero never
occurs. The arithmetic phase uses the actual standard additive character of
`ZMod (n + 1)`, summed over its units.

Only the intact product-minus-one part of the kernel is defined here. No value
for the continued zero-order Kloosterman zeta term, or for a continued Poincaré
series, is supplied by this module.
-/

noncomputable section

namespace GapFamily.Analytic

open scoped Real
open Complex

/-- A Kloosterman phase at the positive denominator `n + 1`. -/
def kloostermanPhase (j J : ℤ) (n : ℕ) (d : (ZMod (n + 1))ˣ) : ℂ :=
  ZMod.stdAddChar ((j : ZMod (n + 1)) * (d : ZMod (n + 1)) +
    (J : ZMod (n + 1)) * ((d⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1)))

/-- The actual finite Kloosterman sum `S(j,J;n+1)`. -/
def kloostermanSum (j J : ℤ) (n : ℕ) : ℂ :=
  ∑ d : (ZMod (n + 1))ˣ, kloostermanPhase j J n d

@[simp] theorem norm_kloostermanPhase (j J : ℤ) (n : ℕ) (d : (ZMod (n + 1))ˣ) :
    ‖kloostermanPhase j J n d‖ = 1 := by
  simp [kloostermanPhase]

/-- The elementary arithmetic bound, without cancellation. -/
theorem norm_kloostermanSum_le (j J : ℤ) (n : ℕ) :
    ‖kloostermanSum j J n‖ ≤ (n + 1 : ℝ) := by
  calc
    ‖kloostermanSum j J n‖ ≤ ∑ d : (ZMod (n + 1))ˣ, ‖kloostermanPhase j J n d‖ :=
      norm_sum_le _ _
    _ = (Fintype.card (ZMod (n + 1))ˣ : ℝ) := by simp
    _ ≤ (Fintype.card (ZMod (n + 1)) : ℝ) := by
      exact_mod_cast Fintype.card_le_of_injective
        (fun d : (ZMod (n + 1))ˣ => (d : ZMod (n + 1))) Units.val_injective
    _ = (n + 1 : ℝ) := by rw [ZMod.card]; push_cast; rfl

/-- The normalized arithmetic weights used in the higher kernel are bounded by one. -/
theorem norm_kloostermanSum_div_le_one (j J : ℤ) (n : ℕ) :
    ‖kloostermanSum j J n / ((n + 1 : ℕ) : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast norm_kloostermanSum_le j J n

/-- The denominator-one phase is exactly one for every pair of spins. -/
@[simp] theorem kloostermanPhase_zero (j J : ℤ) (d : (ZMod (0 + 1))ˣ) :
    kloostermanPhase j J 0 d = 1 := by
  let : Subsingleton (ZMod (0 + 1)) := inferInstanceAs (Subsingleton (ZMod 1))
  have h : (j : ZMod (0 + 1)) * (d : ZMod (0 + 1)) +
      (J : ZMod (0 + 1)) * ((d⁻¹ : (ZMod (0 + 1))ˣ) : ZMod (0 + 1)) = 0 :=
    Subsingleton.elim _ _
  simp [kloostermanPhase, h]

/-- The denominator-one Kloosterman sum is exactly one. -/
@[simp] theorem kloostermanSum_zero (j J : ℤ) : kloostermanSum j J 0 = 1 := by
  simp [kloostermanSum]

/-- The phase written with integer representatives, fixing its normalization. -/
theorem kloostermanPhase_eq_exp (j J : ℤ) (n : ℕ) (d : (ZMod (n + 1))ˣ) :
    kloostermanPhase j J n d =
      Complex.exp (2 * π * I *
        (j * ((d : ZMod (n + 1)).val : ℂ) +
          J * (((d⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1)).val : ℂ)) / (n + 1)) := by
  have h := ZMod.stdAddChar_coe (N := n + 1)
    (j * ((d : ZMod (n + 1)).val : ℤ) +
      J * (((d⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1)).val : ℤ))
  simpa [kloostermanPhase, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_zmod_val, Nat.cast_add, Nat.cast_one] using h

/-- The entire energy argument in the plus chiral factor. -/
def higherKernelArgPlus (j J : ℤ) (e E : ℂ) : ℂ :=
  4 * (π : ℂ) ^ 2 * (E + J) * (e + j)

/-- The entire energy argument in the minus chiral factor. -/
def higherKernelArgMinus (j J : ℤ) (e E : ℂ) : ℂ :=
  4 * (π : ℂ) ^ 2 * (E - J) * (e - j)

/-- One intact higher-kernel summand, before the overall factor two. -/
def higherKernelTerm (j J : ℤ) (e E : ℂ) (n : ℕ) : ℂ :=
  (kloostermanSum j J n / ((n + 1 : ℕ) : ℂ)) *
    (cosRoot (higherKernelArgPlus j J e E / ((n + 1 : ℕ) : ℂ) ^ 2) *
      cosRoot (higherKernelArgMinus j J e E / ((n + 1 : ℕ) : ℂ) ^ 2) - 1)

/-- The nonzero-order entire part of the Fourier kernel. -/
def higherKernel (j J : ℤ) (e E : ℂ) : ℂ :=
  2 * ∑' n : ℕ, higherKernelTerm j J e E n

/-- Genuine convergence using the bound for the actual finite arithmetic sums. -/
theorem summable_higherKernelTerm (j J : ℤ) (e E : ℂ) :
    Summable (higherKernelTerm j J e E) :=
  summable_weighted_cosRoot_mul_sub_one
    (higherKernelArgPlus j J e E) (higherKernelArgMinus j J e E)
    (fun n => kloostermanSum j J n / ((n + 1 : ℕ) : ℂ))
    (norm_kloostermanSum_div_le_one j J)

/-- The higher-kernel series converges absolutely at every complex energy pair. -/
theorem summable_norm_higherKernelTerm (j J : ℤ) (e E : ℂ) :
    Summable (fun n => ‖higherKernelTerm j J e E n‖) :=
  (summable_higherKernelTerm j J e E).norm

/-- The defined higher kernel is the limit of its actual summands. -/
theorem higherKernel_hasSum (j J : ℤ) (e E : ℂ) :
    HasSum (fun n => 2 * higherKernelTerm j J e E n) (higherKernel j J e E) :=
  (summable_higherKernelTerm j J e E).hasSum.mul_left 2

/-- The first higher-kernel term retains the full denominator-one bracket. -/
@[simp] theorem higherKernelTerm_zero (j J : ℤ) (e E : ℂ) :
    higherKernelTerm j J e E 0 =
      cosRoot (higherKernelArgPlus j J e E) * cosRoot (higherKernelArgMinus j J e E) - 1 := by
  simp [higherKernelTerm]

/-- The direct real-cosine expression agrees with the entire summand on the physical cone. -/
theorem higherKernelTerm_physical (j J : ℤ) (e E : ℝ)
    (he : |(j : ℝ)| ≤ e) (hE : |(J : ℝ)| ≤ E) (n : ℕ) :
    higherKernelTerm j J e E n =
      (kloostermanSum j J n / ((n + 1 : ℕ) : ℂ)) *
        (((Real.cos (Real.sqrt
          (4 * π ^ 2 * (E + J) * (e + j) / ((n + 1 : ℕ) : ℝ) ^ 2))) : ℂ) *
          ((Real.cos (Real.sqrt
          (4 * π ^ 2 * (E - J) * (e - j) / ((n + 1 : ℕ) : ℝ) ^ 2))) : ℂ) - 1) := by
  obtain ⟨hej, hje⟩ := abs_le.mp he
  obtain ⟨hEJ, hJE⟩ := abs_le.mp hE
  have hp : 0 ≤ 4 * π ^ 2 * (E + J) * (e + j) / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
    · positivity
  have hm : 0 ≤ 4 * π ^ 2 * (E - J) * (e - j) / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
    · positivity
  have hpc := cosRoot_ofReal_nonneg hp
  have hmc := cosRoot_ofReal_nonneg hm
  push_cast at hpc hmc
  unfold higherKernelTerm higherKernelArgPlus higherKernelArgMinus
  push_cast
  rw [hpc, hmc]

@[simp] theorem higherKernelTerm_scalar_input_zero (j : ℤ) (e : ℂ) (n : ℕ) :
    higherKernelTerm j 0 e 0 n = 0 := by
  simp [higherKernelTerm, higherKernelArgPlus, higherKernelArgMinus]

@[simp] theorem higherKernel_scalar_input_zero (j : ℤ) (e : ℂ) :
    higherKernel j 0 e 0 = 0 := by
  simp [higherKernel]

@[simp] theorem higherKernelTerm_scalar_output_zero (J : ℤ) (E : ℂ) (n : ℕ) :
    higherKernelTerm 0 J 0 E n = 0 := by
  simp [higherKernelTerm, higherKernelArgPlus, higherKernelArgMinus]

@[simp] theorem higherKernel_scalar_output_zero (J : ℤ) (E : ℂ) :
    higherKernel 0 J 0 E = 0 := by
  simp [higherKernel]

end GapFamily.Analytic
