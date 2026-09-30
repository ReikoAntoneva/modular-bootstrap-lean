import GapFamily.Analytic.Cusp.Profile.CuspWeightedTailAnalytic
import GapFamily.Analytic.Cusp.CuspPoincareDirectRemnant
import GapFamily.Analytic.Cusp.CuspPoincareResidualSplit
import GapFamily.Analytic.Cusp.Fourier.CuspFourierCutoffWeighted

/-!
# The actual shifted Fourier residual source

This assembles the genuine shifted Poincaré series, its low-height direct
remainder, and the compact cutoff commutator. The source is an actual weighted
modular L² vector, analytic near the threshold. The identification as the weak
Laplacian residual of the unshifted Poincaré series is a separate obligation.
-/
noncomputable section
namespace GapFamily.Analytic
open MeasureTheory CuspFourierCutoff

/-- The ordinary full shifted residual expression, with the actual cusp series. -/
def cuspPoincareResidualFunction (J : ℤ) (κ : ℂ) (τ : UpperHalfPlane) : ℂ :=
  ((2 * Real.pi * (J : ℝ)) ^ 2 : ℝ) *
    (complexPoincareSeries 0 J (exponent κ + 2) τ -
      (cutoff τ.im : ℂ) * complexPointSeed 0 J (exponent κ + 2) τ) +
    profile κ τ.im * cuspFourierMode J τ.re

/-- The concrete height-weighted source, including the low-height direct term. -/
def cuspPoincareResidualSource (J : ℤ) (α : ℝ) (hα : 0 ≤ α) (κ : ℂ) : ModularHilbert :=
  (((2 * Real.pi * (J : ℝ)) ^ 2 : ℝ) : ℂ) •
    (cuspWeightedTailAnalytic J α hα (exponent κ + 2) +
      cuspPoincareDirectRemnant J α (exponent κ + 2)) + weightedForcing J α κ

/-- The completed source is holomorphic in actual weighted L² norm on this half-plane. -/
theorem cuspPoincareResidualSource_analyticAt (J : ℤ) (α : ℝ) (hα : 0 ≤ α)
    {κ : ℂ} (hκ : α - 1 / 2 < κ.re) :
    AnalyticAt ℂ (cuspPoincareResidualSource J α hα) κ := by
  have hgap : 2 < (exponent κ + 2).re - α := by
    norm_num [exponent, Complex.add_re] at *
    linarith
  have hp : 0 < (exponent κ + 2).re + α := by linarith
  have ht : AnalyticAt ℂ (fun z : ℂ => cuspWeightedTailAnalytic J α hα (exponent z + 2)) κ :=
    (cuspWeightedTailAnalytic_analyticAt J α hα hgap).comp_of_eq
      (show AnalyticAt ℂ (fun z : ℂ => exponent z + 2) κ by unfold exponent; fun_prop) rfl
  have hd : AnalyticAt ℂ (fun z : ℂ => cuspPoincareDirectRemnant J α (exponent z + 2)) κ :=
    (cuspPoincareDirectRemnant_analyticAt J α hp).comp_of_eq
      (show AnalyticAt ℂ (fun z : ℂ => exponent z + 2) κ by unfold exponent; fun_prop) rfl
  exact ((ht.add hd).const_smul (c := (((2 * Real.pi * (J : ℝ)) ^ 2 : ℝ) : ℂ))).add
    (weightedForcing_analyticAt J α κ)

/-- Its ordinary representative is precisely the full shifted residual expression. -/
theorem cuspPoincareResidualSource_ae (J : ℤ) (α : ℝ) (hα : 0 ≤ α)
    {κ : ℂ} (hκ : α - 1 / 2 < κ.re) :
    cuspPoincareResidualSource J α hα κ =ᵐ[modularMeasure]
      (fun τ => ((τ.im ^ α : ℝ) : ℂ) * cuspPoincareResidualFunction J κ τ) := by
  have hgap : 2 < (exponent κ + 2).re - α := by
    norm_num [exponent, Complex.add_re] at *
    linarith
  have hp : 0 < (exponent κ + 2).re + α := by linarith
  have hs : 1 < (exponent κ + 2).re := by linarith
  let A := cuspWeightedTailAnalytic J α hα (exponent κ + 2)
  let B := cuspPoincareDirectRemnant J α (exponent κ + 2)
  let C := weightedForcing J α κ
  let c : ℂ := (((2 * Real.pi * (J : ℝ)) ^ 2 : ℝ) : ℂ)
  filter_upwards [Lp.coeFn_add (c • (A + B)) C, Lp.coeFn_smul c (A + B),
    Lp.coeFn_add A B, cuspWeightedTailAnalytic_ae J α hα hgap,
    cuspPoincareDirectRemnant_ae J α hp, weightedForcing_ae J α κ] with τ habc hsm hab ha hb hc
  change (c • (A + B) + C) τ = (c • (A + B)) τ + C τ at habc
  change (c • (A + B)) τ = c * (A + B) τ at hsm
  change (A + B) τ = A τ + B τ at hab
  change A τ = _ at ha
  change B τ = _ at hb
  change C τ = _ at hc
  rw [show cuspPoincareResidualSource J α hα κ = c • (A + B) + C from rfl,
    habc, hsm, hab, ha, hb, hc]
  simp only [cuspWeightedTailTerm, cuspPoincareDirectRemnantTerm]
  rw [tsum_mul_left]
  rw [cuspPoincareResidualFunction,
    complexPoincareSeries_residual_split 0 J hs τ (cutoff τ.im : ℂ)]
  dsimp [c]
  push_cast
  ring

/-- The ordinary residual expression has the genuine claimed weighted L² membership. -/
theorem memLp_weighted_cuspPoincareResidualFunction (J : ℤ) (α : ℝ) (hα : 0 ≤ α)
    {κ : ℂ} (hκ : α - 1 / 2 < κ.re) :
    MemLp (fun τ => ((τ.im ^ α : ℝ) : ℂ) * cuspPoincareResidualFunction J κ τ)
      2 modularMeasure :=
  (memLp_congr_ae (cuspPoincareResidualSource_ae J α hα hκ)).mp
    (Lp.memLp (cuspPoincareResidualSource J α hα κ))

theorem cuspPoincareResidualSource_analyticOnNhd (J : ℤ) (α : ℝ) (hα : 0 ≤ α) :
    AnalyticOnNhd ℂ (cuspPoincareResidualSource J α hα) {κ : ℂ | α - 1 / 2 < κ.re} :=
  fun _ hκ => cuspPoincareResidualSource_analyticAt J α hα hκ

/-- The actual quarter-weighted residual source is analytic through the threshold. -/
theorem cuspPoincareResidualSource_quarter_analyticAt_zero (J : ℤ) :
    AnalyticAt ℂ (cuspPoincareResidualSource J (1 / 4) (by norm_num)) 0 :=
  cuspPoincareResidualSource_analyticAt J (1 / 4) (by norm_num) (by norm_num)

/-- Its unweighted counterpart is also an actual analytic modular L² source. -/
theorem cuspPoincareResidualSource_zero_weight_analyticAt_zero (J : ℤ) :
    AnalyticAt ℂ (cuspPoincareResidualSource J 0 (by norm_num)) 0 :=
  cuspPoincareResidualSource_analyticAt J 0 (by norm_num) (by norm_num)

end GapFamily.Analytic
