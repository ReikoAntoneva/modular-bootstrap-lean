import GapFamily.Analytic.Cusp.Profile.CuspLogCoordinateDeriv
import GapFamily.Analytic.Cusp.Profile.CuspProfileLaplacianSource

/-!
# Exact complex pairings in the logarithmic cusp coordinate

The exponential change of variables preserves ordinary integrability and
identifies the literal physical spectral test with its test-first half-line form.
-/

noncomputable section

namespace GapFamily.Analytic
open Set MeasureTheory
open scoped ContDiff

/-- Exact square-root/Jacobian cancellation in a complex test-first pairing. -/
theorem cuspLift_inner_exp (u v : ℝ → ℂ) (t : ℝ) :
    Real.exp t • (inner ℂ (cuspLift u (Real.exp t)) (cuspLift v (Real.exp t)) /
      ((Real.exp t : ℝ) : ℂ)^2) = inner ℂ (u t) (v t) := by
  have hs : (Real.sqrt (Real.exp t) : ℂ)^2 = (Real.exp t : ℝ) := by
    exact_mod_cast Real.sq_sqrt (Real.exp_pos t).le
  have he : ((Real.exp t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero t
  simp only [cuspLift, Real.log_exp]
  rw [inner_smul_left_eq_smul, inner_smul_right_eq_smul]
  simp only [Complex.real_smul]
  calc
    _ = (((Real.sqrt (Real.exp t) : ℂ)^2 / (Real.exp t : ℝ)) *
      inner ℂ (u t) (v t)) := by field_simp
    _ = _ := by rw [hs, div_self he, one_mul]

/-- Exact mass pairing for a physical compact test and an arbitrary logarithmic response. -/
theorem cuspLogCoordinate_inner_exp (b v : ℝ → ℂ) (t : ℝ) :
    Real.exp t • (inner ℂ (b (Real.exp t)) (cuspLift v (Real.exp t)) /
      ((Real.exp t : ℝ) : ℂ)^2) = inner ℂ (cuspLogCoordinate b t) (v t) := by
  rw [← cuspLift_cuspLogCoordinate (b := b) (Real.exp_pos t)]
  exact cuspLift_inner_exp _ _ t

/-- Actual exponential substitution preserves convergence of the test-first mass pairing. -/
theorem integrableOn_cuspLogCoordinate_inner_iff (b v : ℝ → ℂ) :
    IntegrableOn (fun y => inner ℂ (b y) (cuspLift v y) / (y : ℂ)^2) (Ioi 1) ↔
      IntegrableOn (fun t => inner ℂ (cuspLogCoordinate b t) (v t)) (Ioi 0) := by
  have h := integrableOn_comp_exp_Ioi
    (fun y => inner ℂ (b y) (cuspLift v y) / (y : ℂ)^2) 0
  simpa only [Real.exp_zero, cuspLogCoordinate_inner_exp] using h.symm

/-- The ordinary mass pairing agrees with its logarithmic representative.
The companion equivalence transports actual integrability in either direction. -/
theorem integral_cuspLogCoordinate_inner (b v : ℝ → ℂ) :
    (∫ y in Ioi (1 : ℝ), inner ℂ (b y) (cuspLift v y) / (y : ℂ)^2) =
      ∫ t in Ioi (0 : ℝ), inner ℂ (cuspLogCoordinate b t) (v t) := by
  have h := integral_comp_exp_Ioi
    (fun y => inner ℂ (b y) (cuspLift v y) / (y : ℂ)^2) 0
  simpa only [Real.exp_zero, cuspLogCoordinate_inner_exp] using h.symm

/-- The literal physical Laplacian test becomes the shifted ordinary second derivative. -/
theorem cuspLogCoordinate_spectral_inner_exp {b : ℝ → ℂ} (hb : ContDiff ℝ ∞ b)
    (v : ℝ → ℂ) (κ : ℂ) (t : ℝ) :
    Real.exp t • ((inner ℂ (cuspProfileSecondOrder b (Real.exp t))
      (cuspLift v (Real.exp t)) - (1/4 - κ^2) *
        inner ℂ (b (Real.exp t)) (cuspLift v (Real.exp t))) /
        ((Real.exp t : ℝ) : ℂ)^2) =
      inner ℂ (-deriv (deriv (cuspLogCoordinate b)) t) (v t) +
        κ^2 * inner ℂ (cuspLogCoordinate b t) (v t) := by
  have hL : cuspProfileSecondOrder b (Real.exp t) =
      cuspLift (fun t => -deriv (deriv (cuspLogCoordinate b)) t +
        (1/4 : ℝ) • cuspLogCoordinate b t) (Real.exp t) := by
    have h := cuspLogCoordinate_laplacian hb (Real.exp_pos t)
    simpa only [cuspProfileSecondOrder, cuspLift, Complex.real_smul,
      Complex.ofReal_neg, Complex.ofReal_pow, Real.log_exp] using h
  rw [sub_div, smul_sub, hL, cuspLift_inner_exp]
  have hmass := cuspLogCoordinate_inner_exp b v t
  have hscalar : Real.exp t • ((1/4 - κ^2) *
      inner ℂ (b (Real.exp t)) (cuspLift v (Real.exp t)) /
      ((Real.exp t : ℝ) : ℂ)^2) = (1/4 - κ^2) *
        inner ℂ (cuspLogCoordinate b t) (v t) := by
    rw [← hmass]
    simp only [Complex.real_smul]
    ring
  rw [hscalar, inner_add_left, inner_smul_left_eq_smul]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

/-- Convergence is preserved for the literal physical spectral test. -/
theorem integrableOn_cuspLogCoordinate_spectral_inner_iff {b : ℝ → ℂ}
    (hb : ContDiff ℝ ∞ b) (v : ℝ → ℂ) (κ : ℂ) :
    IntegrableOn (fun y => (inner ℂ (cuspProfileSecondOrder b y) (cuspLift v y) -
      (1/4 - κ^2) * inner ℂ (b y) (cuspLift v y)) / (y : ℂ)^2) (Ioi 1) ↔
      IntegrableOn (fun t => inner ℂ (-deriv (deriv (cuspLogCoordinate b)) t) (v t) +
        κ^2 * inner ℂ (cuspLogCoordinate b t) (v t)) (Ioi 0) := by
  have h := integrableOn_comp_exp_Ioi
    (fun y => (inner ℂ (cuspProfileSecondOrder b y) (cuspLift v y) -
      (1/4 - κ^2) * inner ℂ (b y) (cuspLift v y)) / (y : ℂ)^2) 0
  simpa only [Real.exp_zero, cuspLogCoordinate_spectral_inner_exp hb] using h.symm

/-- Exact ordinary logarithmic transport of the spectral test-first pairing. -/
theorem integral_cuspLogCoordinate_spectral_inner {b : ℝ → ℂ}
    (hb : ContDiff ℝ ∞ b) (v : ℝ → ℂ) (κ : ℂ) :
    (∫ y in Ioi (1 : ℝ), (inner ℂ (cuspProfileSecondOrder b y) (cuspLift v y) -
      (1/4 - κ^2) * inner ℂ (b y) (cuspLift v y)) / (y : ℂ)^2) =
      ∫ t in Ioi (0 : ℝ), inner ℂ (-deriv (deriv (cuspLogCoordinate b)) t) (v t) +
        κ^2 * inner ℂ (cuspLogCoordinate b t) (v t) := by
  have h := integral_comp_exp_Ioi
    (fun y => (inner ℂ (cuspProfileSecondOrder b y) (cuspLift v y) -
      (1/4 - κ^2) * inner ℂ (b y) (cuspLift v y)) / (y : ℂ)^2) 0
  simpa only [Real.exp_zero, cuspLogCoordinate_spectral_inner_exp hb] using h.symm

end GapFamily.Analytic
