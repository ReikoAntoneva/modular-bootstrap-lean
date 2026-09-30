import GapFamily.Analytic.Transform.LaplaceKernelPairing
import GapFamily.Analytic.Transform.FiniteLaplaceDensity
import GapFamily.Analytic.Elliptic.WeakKernelForm

/-! Finite Laplace combinations have literal, absolutely convergent
sesquilinear pairings for the actual corrected physical kernel. -/

noncomputable section
namespace GapFamily.Analytic

open MeasureTheory
open scoped BigOperators ComplexConjugate

/-- Pointwise finite expansion of the actual corrected weak integrand. -/
theorem weakKernelIntegrand_correctedKernel_finiteLaplaceSum
    (j J : ℤ) {n m : ℕ} (c : Fin n → ℂ) (d : Fin m → ℂ) (p : ℝ × ℝ) :
    weakKernelIntegrand (fun p => correctedKernel j J p.1 p.2)
        (finiteLaplaceSum c) (finiteLaplaceSum d) p =
      ∑ k, ∑ l, star (c k) * ((laplaceTest k.val p.1 : ℂ) *
        correctedKernel j J p.1 p.2 * (laplaceTest l.val p.2 : ℂ)) * d l := by
  simp only [weakKernelIntegrand, finiteLaplaceSum, map_sum, map_mul,
    Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [starRingEnd_apply]
  ring

/-- Actual finite Laplace rows have integrable corrected-kernel pairing,
without any additional moment or integrability premise. -/
theorem integrable_correctedKernel_finiteLaplaceSum_pair
    (j J : ℤ) {n m : ℕ} (c : Fin n → ℂ) (d : Fin m → ℂ) :
    Integrable
      (weakKernelIntegrand (fun p => correctedKernel j J p.1 p.2)
        (finiteLaplaceSum c) (finiteLaplaceSum d))
      ((referenceMeasure j).prod (referenceMeasure J)) := by
  have heq :
      weakKernelIntegrand (fun p => correctedKernel j J p.1 p.2)
          (finiteLaplaceSum c) (finiteLaplaceSum d) =
        fun p => ∑ k, ∑ l, star (c k) * ((laplaceTest k.val p.1 : ℂ) *
          correctedKernel j J p.1 p.2 * (laplaceTest l.val p.2 : ℂ)) * d l := by
    funext p
    exact weakKernelIntegrand_correctedKernel_finiteLaplaceSum j J c d p
  rw [heq]
  exact integrable_finsetSum Finset.univ fun k _ =>
    integrable_finsetSum Finset.univ fun l _ =>
      ((integrable_laplaceTest_correctedKernel_pair j J k.val l.val).const_mul
        (star (c k))).mul_const (d l)

/-- The ordinary product-energy weak pairing is exactly the finite
coefficient pairing of the actual corrected-kernel Laplace integrals. -/
theorem weakKernelPairing_correctedKernel_finiteLaplaceSum
    (j J : ℤ) {n m : ℕ} (c : Fin n → ℂ) (d : Fin m → ℂ) :
    weakKernelPairing j J (fun p => correctedKernel j J p.1 p.2)
        (finiteLaplaceSum c) (finiteLaplaceSum d) =
      ∑ k, ∑ l, star (c k) *
        (∫ p : ℝ × ℝ, (laplaceTest k.val p.1 : ℂ) *
          correctedKernel j J p.1 p.2 * (laplaceTest l.val p.2 : ℂ)
            ∂((referenceMeasure j).prod (referenceMeasure J))) * d l := by
  have hi (k : Fin n) (l : Fin m) :
      Integrable (fun p : ℝ × ℝ => star (c k) * ((laplaceTest k.val p.1 : ℂ) *
        correctedKernel j J p.1 p.2 * (laplaceTest l.val p.2 : ℂ)) * d l)
        ((referenceMeasure j).prod (referenceMeasure J)) :=
    ((integrable_laplaceTest_correctedKernel_pair j J k.val l.val).const_mul
      (star (c k))).mul_const (d l)
  unfold weakKernelPairing
  simp_rw [weakKernelIntegrand_correctedKernel_finiteLaplaceSum]
  rw [integral_finsetSum Finset.univ (fun k _ =>
    integrable_finsetSum Finset.univ (fun l _ => hi k l))]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finsetSum Finset.univ (fun l _ => hi k l)]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_mul_const, integral_const_mul]

end GapFamily.Analytic
