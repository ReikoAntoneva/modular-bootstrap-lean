import GapFamily.Analytic.Kernel.FullKernel
import GapFamily.Analytic.Kernel.KernelSymmetry
import GapFamily.Analytic.Poincare.Arithmetic.PoincareCentralReality

/-! The physical real kernel and Hermitian symmetry of its rank correction. -/
noncomputable section
namespace GapFamily.Analytic
open Complex PoincareCentralZeta
open scoped ComplexConjugate

/-- The physical numerator `Q_phys` is the real restriction of the actual
entire-energy formula. The equality with that complex formula is proved below. -/
def fullKernelPhys (j J : ℤ) (e E : ℝ) : ℝ :=
  (fullKernelHol j J (e : ℂ) (E : ℂ)).re

@[simp] theorem conj_centralKernel (j J : ℤ) :
    conj (centralKernel j J) = centralKernel j J := by
  by_cases h : j = 0 ∨ J = 0
  · simp only [centralKernel, ite_eq_left h, map_zero]
  · simp only [centralKernel, ite_eq_right h, map_mul, map_ofNat,
      conj_centralZeta_zero j J (fun hj => h (Or.inl hj))]

theorem centralKernel_symm (j J : ℤ) : centralKernel j J = centralKernel J j := by
  by_cases h : j = 0 ∨ J = 0
  · simp only [centralKernel, ite_eq_left h, ite_eq_left h.symm]
  · have h' : ¬ (J = 0 ∨ j = 0) := fun h' => h h'.symm
    simp only [centralKernel, ite_eq_right h, ite_eq_right h',
      centralZeta_zero_symm j J (fun hj => h (Or.inl hj)) (fun hJ => h (Or.inr hJ))]

/-- Input-output exchange preserves the full entire formula. -/
theorem fullKernelHol_symm (j J : ℤ) (e E : ℂ) :
    fullKernelHol j J e E = fullKernelHol J j E e := by
  rw [fullKernelHol, fullKernelHol, centralKernel_symm, higherKernel_symm]

/-- The full entire kernel has the Schwarz reflection property. -/
theorem conj_fullKernelHol (j J : ℤ) (e E : ℂ) :
    conj (fullKernelHol j J e E) = fullKernelHol j J (conj e) (conj E) := by
  simp only [fullKernelHol, map_add, conj_centralKernel, conj_higherKernel]

@[simp] theorem conj_fullKernelHol_ofReal (j J : ℤ) (e E : ℝ) :
    conj (fullKernelHol j J e E) = fullKernelHol j J e E := by
  simpa only [Complex.conj_ofReal] using conj_fullKernelHol j J (e : ℂ) (E : ℂ)

@[simp] theorem fullKernelHol_ofReal_im (j J : ℤ) (e E : ℝ) :
    (fullKernelHol j J e E).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_fullKernelHol_ofReal j J e E)

/-- Restricting to the real numerator loses no information, even below
physical threshold. -/
@[simp] theorem fullKernelPhys_coe_eq (j J : ℤ) (e E : ℝ) :
    (fullKernelPhys j J e E : ℂ) = fullKernelHol j J e E := by
  apply Complex.ext
  · rfl
  · simp

theorem fullKernelPhys_symm (j J : ℤ) (e E : ℝ) :
    fullKernelPhys j J e E = fullKernelPhys J j E e := by
  unfold fullKernelPhys
  rw [fullKernelHol_symm]

/-- On the physical cone, the real restriction is exactly the central value
plus the convergent cosine product-minus-one series. -/
theorem fullKernelPhys_eq_cosine (j J : ℤ) (e E : ℝ)
    (he : |(j : ℝ)| ≤ e) (hE : |(J : ℝ)| ≤ E) :
    fullKernelPhys j J e E =
      (if j = 0 ∨ J = 0 then 0 else 2 * (PoincareCentralZeta.centralZeta j J 0).re) +
        2 * ∑' n : ℕ, (kloostermanSum j J n).re / ((n + 1 : ℕ) : ℝ) *
          (Real.cos (Real.sqrt
            (4 * Real.pi ^ 2 * (E + J) * (e + j) / ((n + 1 : ℕ) : ℝ) ^ 2)) *
            Real.cos (Real.sqrt
            (4 * Real.pi ^ 2 * (E - J) * (e - j) / ((n + 1 : ℕ) : ℝ) ^ 2)) - 1) := by
  simp only [fullKernelPhys, fullKernelHol, Complex.add_re,
    higherKernel_physical_re j J e E he hE]
  congr 1
  unfold centralKernel
  split_ifs <;> simp

theorem scalarRankKernel_symm (j J : ℤ) (e E : ℝ) :
    scalarRankKernel j J e E = scalarRankKernel J j E e := by
  unfold scalarRankKernel
  by_cases h : j = 0 ∧ J = 0
  · rw [ite_eq_left h, ite_eq_left h.symm]
    ring
  · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.symm)]

theorem correctedKernel_symm (j J : ℤ) (e E : ℝ) :
    correctedKernel j J e E = correctedKernel J j E e := by
  rw [correctedKernel, correctedKernel, fullKernelHol_symm, scalarRankKernel_symm]

@[simp] theorem conj_correctedKernel (j J : ℤ) (e E : ℝ) :
    conj (correctedKernel j J e E) = correctedKernel j J e E := by
  simp only [correctedKernel, map_add, conj_fullKernelHol_ofReal, Complex.conj_ofReal]

@[simp] theorem correctedKernel_im (j J : ℤ) (e E : ℝ) :
    (correctedKernel j J e E).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_correctedKernel j J e E)

/-- The exact Hermitian identity needed by the low-band integral operator. -/
theorem correctedKernel_hermitian (j J : ℤ) (e E : ℝ) :
    conj (correctedKernel J j E e) = correctedKernel j J e E := by
  rw [conj_correctedKernel, correctedKernel_symm]

/-- The corrected complex numerator equals the physical numerator plus its
explicit real rank-one term. -/
theorem correctedKernel_eq_phys_add_rank (j J : ℤ) (e E : ℝ) :
    correctedKernel j J e E =
      ((fullKernelPhys j J e E + scalarRankKernel j J e E : ℝ) : ℂ) := by
  rw [Complex.ofReal_add, fullKernelPhys_coe_eq]
  rfl

end GapFamily.Analytic
