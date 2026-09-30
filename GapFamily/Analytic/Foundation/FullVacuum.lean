import GapFamily.Analytic.Foundation.VacuumRemainder
import GapFamily.Analytic.Kernel.FullKernel

/-!
# The complete four-seed vacuum numerator

The four terms use the actual entire kernel, including its continued central
coefficient. Their denominator-one factor and normally convergent higher
remainder are the same ones already isolated in `VacuumRemainder`.
-/

noncomputable section

namespace GapFamily.Analytic

/-- The full continuum numerator of the signed vacuum seed combination. -/
def vacuumFullKernel (a e : ℝ) (j : ℤ) : ℂ :=
  fullKernelHol j 0 e (-a) - fullKernelHol j 1 e (1 - a) -
    fullKernelHol j (-1) e (1 - a) + fullKernelHol j 0 e (2 - a)

/-- The two nonzero input-spin central coefficients survive the null subtraction. -/
def vacuumCentralKernel (j : ℤ) : ℂ :=
  -centralKernel j 1 - centralKernel j (-1)

/-- The full vacuum has exactly its actual central coefficient and higher series. -/
theorem vacuumFullKernel_eq_central_add_higher (a e : ℝ) (j : ℤ) :
    vacuumFullKernel a e j = vacuumCentralKernel j + vacuumHigherKernel a e j := by
  simp only [vacuumFullKernel, fullKernelHol, centralKernel_scalar_input,
    vacuumCentralKernel, vacuumHigherKernel, zero_add]
  ring

@[simp] theorem vacuumCentralKernel_zero : vacuumCentralKernel 0 = 0 := by
  simp [vacuumCentralKernel]

/-- There is no central reference density in the scalar output. -/
theorem vacuumFullKernel_scalar_eq_higher (a e : ℝ) :
    vacuumFullKernel a e 0 = vacuumHigherKernel a e 0 := by
  rw [vacuumFullKernel_eq_central_add_higher, vacuumCentralKernel_zero, zero_add]

/-- The complete vacuum remainder includes the continued arithmetic term. -/
def vacuumFullRemainder (a e : ℝ) (j : ℤ) : ℂ :=
  vacuumFullKernel a e j - (vacuumLeading a e j : ℂ)

theorem vacuumFullRemainder_eq_central_add_higher (a e : ℝ) (j : ℤ) :
    vacuumFullRemainder a e j =
      vacuumCentralKernel j + vacuumHigherRemainder a e j := by
  rw [vacuumFullRemainder, vacuumFullKernel_eq_central_add_higher,
    vacuumHigherRemainder]
  ring

/-- The full continuum retains the exact denominator-one vacuum factor. -/
theorem vacuumFullKernel_eq_leading_add_remainder (a e : ℝ) (j : ℤ) :
    vacuumFullKernel a e j =
      (vacuumLeading a e j : ℂ) + vacuumFullRemainder a e j := by
  simp [vacuumFullRemainder]

/-- The scalar vacuum density has the required endpoint cancellation. -/
@[simp] theorem vacuumFullKernel_scalar_endpoint (a : ℝ) :
    vacuumFullKernel a 0 0 = 0 := by
  simp [vacuumFullKernel]

end GapFamily.Analytic
