import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecificLimits.Normed
import GapFamily.Analytic.Foundation.MomentIntegral
import GapFamily.Analytic.Foundation.SignedMomentIntegral

/-!
# Holomorphic Taylor bounds for finite-moment cancellation

The coefficients and the remainder estimate are derived from the actual complex
derivatives and Cauchy's estimate. They are not approximation hypotheses.
-/

open Set Metric MeasureTheory

namespace GapFamily.Analytic

noncomputable def taylorCoefficient (F : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ * iteratedDeriv n F c

noncomputable def taylorPolynomial (F : ℂ → ℂ) (c : ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (k + 1), taylorCoefficient F c n * (z - c) ^ n

/-- Cauchy's derivative estimate, normalized to Taylor coefficients. -/
theorem norm_taylorCoefficient_le {F : ℂ → ℂ} {c : ℂ} {R A : ℝ}
    (hR : 0 < R) (hf : DiffContOnCl ℂ F (ball c R))
    (hA : ∀ z ∈ sphere c R, ‖F z‖ ≤ A) (n : ℕ) :
    ‖taylorCoefficient F c n‖ ≤ A / R ^ n := by
  have hfact : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  calc
    _ = (n.factorial : ℝ)⁻¹ * ‖iteratedDeriv n F c‖ := by
      simp only [taylorCoefficient, norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (n.factorial : ℝ)⁻¹ * (n.factorial * A / R ^ n) :=
      mul_le_mul_of_nonneg_left
        (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hf hA)
        (by positivity)
    _ = _ := by rw [← mul_div_assoc, inv_mul_cancel_left₀ hfact]

/-- Every Taylor term is bounded by the corresponding geometric term on a
smaller concentric disk. -/
theorem norm_taylor_term_le {F : ℂ → ℂ} {c z : ℂ} {R A θ : ℝ}
    (hR : 0 < R) (hA : 0 ≤ A)
    (hf : DiffContOnCl ℂ F (ball c R))
    (hbound : ∀ w ∈ sphere c R, ‖F w‖ ≤ A)
    (hz : ‖z - c‖ ≤ θ * R) (n : ℕ) :
    ‖taylorCoefficient F c n * (z - c) ^ n‖ ≤ A * θ ^ n := by
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (A / R ^ n) * (θ * R) ^ n :=
      mul_le_mul (norm_taylorCoefficient_le hR hf hbound n)
        (pow_le_pow_left₀ (norm_nonneg _) hz n) (by positivity) (by positivity)
    _ = _ := by rw [mul_pow]; field_simp

/-- The actual holomorphic remainder after degree `k` is bounded by the
geometric Cauchy tail, with the constant in construction C2. -/
theorem norm_taylor_remainder_le {F : ℂ → ℂ} {c z : ℂ} {R A θ : ℝ}
    (hR : 0 < R) (hA : 0 ≤ A) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hf : DiffContOnCl ℂ F (ball c R))
    (hbound : ∀ w ∈ sphere c R, ‖F w‖ ≤ A)
    (hz : ‖z - c‖ ≤ θ * R) (k : ℕ) :
    ‖F z - taylorPolynomial F c k z‖ ≤ A * θ ^ (k + 1) / (1 - θ) := by
  have hzball : z ∈ ball c R := by
    rw [mem_ball_iff_norm]
    exact hz.trans_lt (by nlinarith)
  have hsum : HasSum (fun n => taylorCoefficient F c n * (z - c) ^ n) (F z) := by
    convert Complex.hasSum_taylorSeries_on_ball hf.differentiableOn hzball using 1
    ext n
    simp only [taylorCoefficient, smul_eq_mul]
    ring
  have htail : HasSum
      (fun n => taylorCoefficient F c (n + (k + 1)) * (z - c) ^ (n + (k + 1)))
      (F z - taylorPolynomial F c k z) :=
    (hasSum_nat_add_iff' (k + 1)).mpr hsum
  have hgeom : HasSum (fun n : ℕ => A * θ ^ (n + (k + 1)))
      (A * θ ^ (k + 1) / (1 - θ)) := by
    convert (hasSum_geometric_of_lt_one hθ hθ1).mul_left (A * θ ^ (k + 1)) using 1
    · ext n
      rw [pow_add]
      ring
    · ring
  exact htail.norm_le_of_bounded hgeom
    (fun n => norm_taylor_term_le hR hA hf hbound hz (n + (k + 1)))

/-- The disk estimate on a real interval of length `d` centered at `c`, with
the source's ratio `θ = d / (2*R)`. -/
theorem norm_taylor_remainder_le_on_real_interval {F : ℂ → ℂ} {c x R A d : ℝ}
    (hR : 0 < R) (hA : 0 ≤ A) (hd : 0 ≤ d) (hdr : d / (2 * R) < 1)
    (hf : DiffContOnCl ℂ F (ball (c : ℂ) R))
    (hbound : ∀ z ∈ sphere (c : ℂ) R, ‖F z‖ ≤ A)
    (hx : x ∈ Icc (c - d / 2) (c + d / 2)) (k : ℕ) :
    ‖F (x : ℂ) - taylorPolynomial F (c : ℂ) k (x : ℂ)‖ ≤
      A * (d / (2 * R)) ^ (k + 1) / (1 - d / (2 * R)) := by
  apply norm_taylor_remainder_le hR hA (by positivity) hdr hf hbound
  have hx' : |x - c| ≤ d / 2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  calc
    ‖(x : ℂ) - (c : ℂ)‖ = |x - c| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ d / 2 := hx'
    _ = (d / (2 * R)) * R := by field_simp

/-- A finite measure concentrated on a compact real interval integrates every
function continuous on that interval. -/
theorem integrable_of_continuousOn_interval_of_ae_mem {E : Type*}
    [NormedAddCommGroup E] {μ : Measure ℝ}
    [IsFiniteMeasure μ] {f : ℝ → E} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) :
    Integrable f μ := by
  have h : IntegrableOn f (Icc a b) μ := hf.integrableOn_Icc
  simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] using h

theorem continuousOn_real_interval_of_holomorphic {F : ℂ → ℂ} {c R d : ℝ}
    (hR : 0 < R) (hdr : d / (2 * R) < 1)
    (hf : DiffContOnCl ℂ F (ball (c : ℂ) R)) :
    ContinuousOn (fun x : ℝ => F (x : ℂ)) (Icc (c - d / 2) (c + d / 2)) := by
  apply hf.continuousOn_ball.comp Complex.continuous_ofReal.continuousOn
  intro x hx
  rw [mem_closedBall_iff_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hx' : |x - c| ≤ d / 2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hdR : d < 2 * R := by
    simpa only [one_mul] using (div_lt_iff₀ (by positivity : 0 < 2 * R)).mp hdr
  linarith

/-- C2 for a difference of finite positive measures. Raw moments through `k`
cancel the actual Taylor polynomial; compact support and analyticity prove all
integrability facts. The mass factor is the sum of the two positive masses,
which is the total variation mass when they are the Jordan parts. -/
theorem norm_integral_sub_le_of_holomorphic_moments {μ η : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure η] {F : ℂ → ℂ} {c R A d : ℝ} {k : ℕ}
    (hR : 0 < R) (hA : 0 ≤ A) (hd : 0 ≤ d) (hdr : d / (2 * R) < 1)
    (hf : DiffContOnCl ℂ F (ball (c : ℂ) R))
    (hbound : ∀ z ∈ sphere (c : ℂ) R, ‖F z‖ ≤ A)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (c - d / 2) (c + d / 2))
    (hη : ∀ᵐ x ∂η, x ∈ Icc (c - d / 2) (c + d / 2))
    (hm : ∀ j ≤ k, (∫ x : ℝ, (x : ℂ) ^ j ∂μ) = ∫ x : ℝ, (x : ℂ) ^ j ∂η) :
    ‖(∫ x : ℝ, F (x : ℂ) ∂μ) - ∫ x : ℝ, F (x : ℂ) ∂η‖ ≤
      (μ.real univ + η.real univ) * A * (d / (2 * R)) ^ (k + 1) /
        (1 - d / (2 * R)) := by
  have hcont := continuousOn_real_interval_of_holomorphic hR hdr hf
  have hμmom (j : ℕ) (_hj : j ≤ k) : Integrable (fun x : ℝ => (x : ℂ) ^ j) μ :=
    integrable_of_continuousOn_interval_of_ae_mem
      (Complex.continuous_ofReal.pow j).continuousOn hμ
  have hηmom (j : ℕ) (_hj : j ≤ k) : Integrable (fun x : ℝ => (x : ℂ) ^ j) η :=
    integrable_of_continuousOn_interval_of_ae_mem
      (Complex.continuous_ofReal.pow j).continuousOn hη
  have hεμ := hμ.mono (fun x hx =>
    norm_taylor_remainder_le_on_real_interval hR hA hd hdr hf hbound hx k)
  have hεη := hη.mono (fun x hx =>
    norm_taylor_remainder_le_on_real_interval hR hA hd hdr hf hbound hx k)
  have h := norm_integral_sub_le_of_moment_approximation hμmom hηmom hm
    (integrable_of_continuousOn_interval_of_ae_mem hcont hμ)
    (integrable_of_continuousOn_interval_of_ae_mem hcont hη)
    (c : ℂ) (taylorCoefficient F (c : ℂ)) hεμ hεη
  simpa only [mul_div_assoc, mul_assoc] using h

/-- The same C2 estimate using ordinary real moments, as in the construction
contract. The conversion to complex moments is proved by scalar extension of
the Bochner integral. -/
theorem norm_integral_sub_le_of_holomorphic_real_moments {μ η : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure η] {F : ℂ → ℂ} {c R A d : ℝ} {k : ℕ}
    (hR : 0 < R) (hA : 0 ≤ A) (hd : 0 ≤ d) (hdr : d / (2 * R) < 1)
    (hf : DiffContOnCl ℂ F (ball (c : ℂ) R))
    (hbound : ∀ z ∈ sphere (c : ℂ) R, ‖F z‖ ≤ A)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (c - d / 2) (c + d / 2))
    (hη : ∀ᵐ x ∂η, x ∈ Icc (c - d / 2) (c + d / 2))
    (hm : ∀ j ≤ k, (∫ x : ℝ, x ^ j ∂μ) = ∫ x : ℝ, x ^ j ∂η) :
    ‖(∫ x : ℝ, F (x : ℂ) ∂μ) - ∫ x : ℝ, F (x : ℂ) ∂η‖ ≤
      (μ.real univ + η.real univ) * A * (d / (2 * R)) ^ (k + 1) /
        (1 - d / (2 * R)) :=
  norm_integral_sub_le_of_holomorphic_moments hR hA hd hdr hf hbound hμ hη
    (fun j hj => integral_complex_pow_eq_of_real (hm j hj))

/-- The holomorphic cancellation estimate for an actual finite signed measure,
with its actual total variation. All integrability is derived from compact
support and continuity; the only moment assumption is vanishing of raw moments. -/
theorem norm_signedIntegral_le_of_holomorphic_moments {ν : SignedMeasure ℝ}
    {F : ℂ → ℂ} {c R A d : ℝ} {k : ℕ}
    (hR : 0 < R) (hA : 0 ≤ A) (hd : 0 ≤ d) (hdr : d / (2 * R) < 1)
    (hf : DiffContOnCl ℂ F (ball (c : ℂ) R))
    (hbound : ∀ z ∈ sphere (c : ℂ) R, ‖F z‖ ≤ A)
    (hν : ∀ᵐ x ∂ν.totalVariation, x ∈ Icc (c - d / 2) (c + d / 2))
    (hm : ∀ j ≤ k, (∫ᵛ x : ℝ, (x : ℂ) ^ j ∂<•ν) = 0) :
    ‖∫ᵛ x : ℝ, F (x : ℂ) ∂<•ν‖ ≤
      ν.totalVariation.real univ * A * (d / (2 * R)) ^ (k + 1) /
        (1 - d / (2 * R)) := by
  have himom (j : ℕ) (_hj : j ≤ k) : ν.Integrable (fun x : ℝ => (x : ℂ) ^ j) := by
    have hi : Integrable (fun x : ℝ => (x : ℂ) ^ j) ν.totalVariation :=
      integrable_of_continuousOn_interval_of_ae_mem
        (Complex.continuous_ofReal.pow j).continuousOn hν
    simpa only [VectorMeasure.Integrable, ← SignedMeasure.totalVariation_eq_variation] using hi
  have hfi : ν.Integrable (fun x : ℝ => F (x : ℂ)) := by
    simpa only [VectorMeasure.Integrable, ← SignedMeasure.totalVariation_eq_variation] using
      integrable_of_continuousOn_interval_of_ae_mem
        (continuousOn_real_interval_of_holomorphic hR hdr hf) hν
  have hε := hν.mono (fun x hx =>
    norm_taylor_remainder_le_on_real_interval hR hA hd hdr hf hbound hx k)
  have h := norm_signedIntegral_le_of_moment_approximation himom hm hfi
    (c : ℂ) (taylorCoefficient F (c : ℂ)) hε
  simpa only [mul_div_assoc, mul_assoc] using h

/-- C2 in its signed-measure form with ordinary real raw moments. The norm on
the right is exactly the mass of mathlib's Hahn–Jordan total variation. -/
theorem norm_signedIntegral_le_of_holomorphic_real_moments {ν : SignedMeasure ℝ}
    {F : ℂ → ℂ} {c R A d : ℝ} {k : ℕ}
    (hR : 0 < R) (hA : 0 ≤ A) (hd : 0 ≤ d) (hdr : d / (2 * R) < 1)
    (hf : DiffContOnCl ℂ F (ball (c : ℂ) R))
    (hbound : ∀ z ∈ sphere (c : ℂ) R, ‖F z‖ ≤ A)
    (hν : ∀ᵐ x ∂ν.totalVariation, x ∈ Icc (c - d / 2) (c + d / 2))
    (hm : ∀ j ≤ k, (∫ᵛ x : ℝ, x ^ j ∂<•ν) = 0) :
    ‖∫ᵛ x : ℝ, F (x : ℂ) ∂<•ν‖ ≤
      ν.totalVariation.real univ * A * (d / (2 * R)) ^ (k + 1) /
        (1 - d / (2 * R)) := by
  apply norm_signedIntegral_le_of_holomorphic_moments hR hA hd hdr hf hbound hν
  intro j hj
  have hi : ν.Integrable (fun x : ℝ => x ^ j) := by
    have hi' : Integrable (fun x : ℝ => x ^ j) ν.totalVariation :=
      integrable_of_continuousOn_interval_of_ae_mem
        (continuous_id.pow j).continuousOn hν
    simpa only [VectorMeasure.Integrable, ← SignedMeasure.totalVariation_eq_variation] using hi'
  exact signedIntegral_complex_pow_eq_of_real hi (hm j hj)

end GapFamily.Analytic
