import GapFamily.Contract
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Spectrum convention for Theorem 2.2

The support in `Spectrum` records distinct weight pairs. A primary counted with
multiplicity is a support point together with a label in the finite type whose
size is its natural multiplicity. The unweighted thermal sum over these copies
is summable exactly when the multiplicity-weighted sum over support is summable.
-/

noncomputable section

namespace GapFamily

/-- Individual primary copies, including their finite multiplicity label. -/
def Spectrum.PrimaryCopy (s : Spectrum) :=
  (p : s.support) × Fin (s.multiplicity p)

/-- Summing over the primary copies is exactly the multiplicity-weighted
thermal summability condition. -/
theorem summable_primary_copy_iff (s : Spectrum) (t : ℝ) :
    Summable (fun p : s.PrimaryCopy => Real.exp (-t * dimension p.1)) ↔
      Summable (fun p : s.support =>
        (s.multiplicity p : ℝ) * Real.exp (-t * dimension p)) := by
  unfold Spectrum.PrimaryCopy
  rw [summable_sigma_of_nonneg (fun p => (Real.exp_pos _).le)]
  simp [Summable.of_finite, tsum_fintype, nsmul_eq_mul]

end GapFamily
