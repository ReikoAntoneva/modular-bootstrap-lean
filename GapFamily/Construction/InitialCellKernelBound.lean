import GapFamily.Analytic.Poincare.Repair.PoincareTailExteriorEstimate
import GapFamily.Analytic.Poincare.Repair.PoincareInitialExteriorEstimate
import GapFamily.Construction.InitialCellDiskGeometry

/-! The initial analytic disk has a polynomial charge cost, with the same
universal kernel coefficient as the short-cell estimate. -/

noncomputable section
open Real Set MeasureTheory
open GapFamily.Analytic
namespace GapFamily.Construction

/-- The initial disk coefficient is linear in charge plus cutoff. -/
theorem inputColumnStripPolynomial_initialDisk_le
    (B a r : ℝ) (hB : 1 ≤ B) (ha : 0 ≤ a) (hr : 0 ≤ r) (hra : r ≤ sqrt a)
    (jin : ℤ) (L V : ℝ) (hL : |(jin : ℝ)| ≤ L) (hLV : L ≤ V) (hVB : V ≤ B) :
    inputColumnStripPolynomial jin (|sqrtInputCenter jin L V| + r) ≤
      canonicalRepairCellCoefficient * (1 + a + B) := by
  have hc0 := sqrtInputCenter_nonneg jin L V
  have hc := sqrtInputCenter_le_sqrt jin L V B hLV hVB
  have hB0 : 0 ≤ B := by linarith
  have hcsq : (sqrtInputCenter jin L V)^2 ≤ B := by
    simpa only [sq_sqrt hB0] using (sq_le_sq₀ hc0 (sqrt_nonneg B)).mpr hc
  have hrsq : r^2 ≤ a := by
    simpa only [sq_sqrt ha] using (sq_le_sq₀ hr (sqrt_nonneg a)).mpr hra
  have hRsq : (sqrtInputCenter jin L V + r)^2 ≤ 2 * (a + B) := by
    nlinarith [sq_nonneg (sqrtInputCenter jin L V - r)]
  have hsa : sqrt a ≤ a + 1 := (sqrt_le_iff).mpr ⟨by positivity, by nlinarith [sq_nonneg a]⟩
  have hcB := hc.trans (sqrt_le_self_iff.mpr (Or.inr hB))
  have hR : sqrtInputCenter jin L V + r ≤ 1 + a + B := by linarith
  have hj : |(jin : ℝ)| ≤ B := hL.trans (hLV.trans hVB)
  have hcentral : centralKernelBound * |(jin : ℝ)| ≤ centralKernelBound * (1 + a + B) :=
    mul_le_mul_of_nonneg_left (by linarith) centralKernelBound_pos.le
  have hhigh : 16 * π^2 * ((sqrtInputCenter jin L V + r)^2 + 2 * |(jin : ℝ)|) ≤
      96 * π^2 * (1 + a + B) := by
    have h := mul_le_mul_of_nonneg_left
      (show (sqrtInputCenter jin L V + r)^2 + 2 * |(jin : ℝ)| ≤ 6 * (1 + a + B) by linarith)
      (by positivity : 0 ≤ 16 * π^2)
    nlinarith
  have hrank : 12 * (sqrtInputCenter jin L V + r) + 1 ≤ 25 * (1 + a + B) := by
    linarith
  rw [abs_of_nonneg hc0]
  unfold inputColumnStripPolynomial canonicalRepairCellCoefficient
  nlinarith

end GapFamily.Construction
