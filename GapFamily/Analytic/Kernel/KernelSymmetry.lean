import GapFamily.Analytic.Arithmetic.KloostermanReality

/-!
# Symmetry and reality of the higher kernel

Complex conjugation commutes with the entire power-series factors. Consequently
the intact higher kernel is real at every pair of real energies, including below
the physical threshold. Interchanging input and output preserves the kernel.
-/

noncomputable section

namespace GapFamily.Analytic

open Complex
open scoped ComplexConjugate

/-- The entire power series has real coefficients. -/
theorem cosRoot_conj (z : ℂ) : cosRoot (conj z) = conj (cosRoot z) := by
  simp only [cosRoot, Complex.conj_tsum, map_div₀, map_mul, map_pow,
    map_neg, map_one, map_natCast]

/-- Reality holds on the whole real axis without a sign restriction. -/
@[simp] theorem conj_cosRoot_ofReal (x : ℝ) :
    conj (cosRoot (x : ℂ)) = cosRoot (x : ℂ) := by
  rw [← cosRoot_conj, Complex.conj_ofReal]

theorem cosRoot_ofReal_im (x : ℝ) : (cosRoot (x : ℂ)).im = 0 := by
  exact Complex.conj_eq_iff_im.mp (conj_cosRoot_ofReal x)

theorem higherKernelArgPlus_symm (j J : ℤ) (e E : ℂ) :
    higherKernelArgPlus j J e E = higherKernelArgPlus J j E e := by
  unfold higherKernelArgPlus
  ring

theorem higherKernelArgMinus_symm (j J : ℤ) (e E : ℂ) :
    higherKernelArgMinus j J e E = higherKernelArgMinus J j E e := by
  unfold higherKernelArgMinus
  ring

@[simp] theorem conj_higherKernelArgPlus (j J : ℤ) (e E : ℂ) :
    conj (higherKernelArgPlus j J e E) =
      higherKernelArgPlus j J (conj e) (conj E) := by
  simp [higherKernelArgPlus, map_ofNat]

@[simp] theorem conj_higherKernelArgMinus (j J : ℤ) (e E : ℂ) :
    conj (higherKernelArgMinus j J e E) =
      higherKernelArgMinus j J (conj e) (conj E) := by
  simp [higherKernelArgMinus, map_ofNat]

/-- Each intact summand is symmetric under exchange of input and output. -/
theorem higherKernelTerm_symm (j J : ℤ) (e E : ℂ) (n : ℕ) :
    higherKernelTerm j J e E n = higherKernelTerm J j E e n := by
  simp only [higherKernelTerm, kloostermanSum_symm j J,
    higherKernelArgPlus_symm j J, higherKernelArgMinus_symm j J]

/-- Symmetry of the actual convergent higher-kernel sum. -/
theorem higherKernel_symm (j J : ℤ) (e E : ℂ) :
    higherKernel j J e E = higherKernel J j E e := by
  simp only [higherKernel, higherKernelTerm_symm j J e E]

/-- Complex conjugation reflects both energy variables in every summand. -/
@[simp] theorem conj_higherKernelTerm (j J : ℤ) (e E : ℂ) (n : ℕ) :
    conj (higherKernelTerm j J e E n) =
      higherKernelTerm j J (conj e) (conj E) n := by
  simp [higherKernelTerm, ← cosRoot_conj, conj_kloostermanSum]

/-- Schwarz reflection for the entire higher kernel in both energy variables. -/
theorem conj_higherKernel (j J : ℤ) (e E : ℂ) :
    conj (higherKernel j J e E) = higherKernel j J (conj e) (conj E) := by
  simp [higherKernel, Complex.conj_tsum, map_ofNat]

/-- The higher kernel is real at all real energies. -/
@[simp] theorem conj_higherKernel_ofReal (j J : ℤ) (e E : ℝ) :
    conj (higherKernel j J e E) = higherKernel j J e E := by
  simpa only [Complex.conj_ofReal] using conj_higherKernel j J (e : ℂ) (E : ℂ)

theorem higherKernel_ofReal_im (j J : ℤ) (e E : ℝ) :
    (higherKernel j J e E).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_higherKernel_ofReal j J e E)

/-- Reality and symmetry give the Hermitian identity for the physical kernel. -/
theorem higherKernel_hermitian (j J : ℤ) (e E : ℝ) :
    conj (higherKernel J j E e) = higherKernel j J e E := by
  rw [conj_higherKernel_ofReal, higherKernel_symm]

/-- The real part of each physical summand has the literal real-cosine formula. -/
theorem higherKernelTerm_physical_re (j J : ℤ) (e E : ℝ)
    (he : |(j : ℝ)| ≤ e) (hE : |(J : ℝ)| ≤ E) (n : ℕ) :
    (higherKernelTerm j J e E n).re =
      (kloostermanSum j J n).re / ((n + 1 : ℕ) : ℝ) *
        (Real.cos (Real.sqrt
          (4 * Real.pi ^ 2 * (E + J) * (e + j) / ((n + 1 : ℕ) : ℝ) ^ 2)) *
          Real.cos (Real.sqrt
          (4 * Real.pi ^ 2 * (E - J) * (e - j) / ((n + 1 : ℕ) : ℝ) ^ 2)) - 1) := by
  rw [higherKernelTerm_physical j J e E he hE n]
  rw [← Complex.ofReal_natCast]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    mul_zero, zero_mul, sub_zero, add_zero, Complex.div_ofReal_re]

/-- The physical real-cosine summands form an ordinary convergent series. -/
theorem summable_higherKernel_physical (j J : ℤ) (e E : ℝ)
    (he : |(j : ℝ)| ≤ e) (hE : |(J : ℝ)| ≤ E) :
    Summable (fun n : ℕ => (kloostermanSum j J n).re / ((n + 1 : ℕ) : ℝ) *
      (Real.cos (Real.sqrt
        (4 * Real.pi ^ 2 * (E + J) * (e + j) / ((n + 1 : ℕ) : ℝ) ^ 2)) *
        Real.cos (Real.sqrt
        (4 * Real.pi ^ 2 * (E - J) * (e - j) / ((n + 1 : ℕ) : ℝ) ^ 2)) - 1)) := by
  simpa only [higherKernelTerm_physical_re j J e E he hE] using
    (Complex.hasSum_re (summable_higherKernelTerm j J (e : ℂ) (E : ℂ)).hasSum).summable

/-- On the physical cone, the higher kernel is the convergent real-cosine series. -/
theorem higherKernel_physical_re (j J : ℤ) (e E : ℝ)
    (he : |(j : ℝ)| ≤ e) (hE : |(J : ℝ)| ≤ E) :
    (higherKernel j J e E).re =
      2 * ∑' n : ℕ, (kloostermanSum j J n).re / ((n + 1 : ℕ) : ℝ) *
        (Real.cos (Real.sqrt
          (4 * Real.pi ^ 2 * (E + J) * (e + j) / ((n + 1 : ℕ) : ℝ) ^ 2)) *
          Real.cos (Real.sqrt
          (4 * Real.pi ^ 2 * (E - J) * (e - j) / ((n + 1 : ℕ) : ℝ) ^ 2)) - 1) := by
  simp only [higherKernel, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero, Complex.re_tsum (summable_higherKernelTerm j J (e : ℂ) (E : ℂ)),
    higherKernelTerm_physical_re j J e E he hE]

end GapFamily.Analytic
