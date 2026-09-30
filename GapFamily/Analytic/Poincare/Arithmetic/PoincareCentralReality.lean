import GapFamily.Analytic.Poincare.Arithmetic.PoincareCentralQuotient
import GapFamily.Analytic.Arithmetic.KloostermanDirichletReality
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Reality and frequency symmetry of the actual threshold central value.
The reflection identity is continued from the literal Dirichlet series after
cross multiplication; only the proved nonzero threshold factor is cancelled. -/
noncomputable section
namespace GapFamily.Analytic.PoincareCentralZeta
open Set Complex CuspFourierCutoff PoincareFourierContinuation
open PoincareCanonical PoincareCentralFactor
open scoped ComplexConjugate

private theorem conj_mem_continuationRegion {r : ℝ} {κ : ℂ}
    (hκ : κ ∈ continuationRegion r) : conj κ ∈ continuationRegion r := by
  rcases hκ with hκ | ⟨hp, hn⟩
  · left
    simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_conj] using hκ
  · right
    refine ⟨by simpa using hp, ?_⟩
    intro h
    apply hn
    have hh := congrArg conj h
    simpa [map_ofNat] using hh

private theorem analyticOnNhd_conj_reflect {r : ℝ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (continuationRegion r)) :
    AnalyticOnNhd ℂ (fun κ => conj (f (conj κ))) (continuationRegion r) := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_continuationRegion r)
  intro κ hκ
  have h := (hf (conj κ) (conj_mem_continuationRegion hκ)).differentiableAt.conj_conj
  have hh : DifferentiableAt ℂ (fun κ => conj (f (conj κ))) κ := by
    simpa only [Function.comp_def, map_star, Complex.conj_conj] using h
  exact hh.differentiableWithinAt

/-- Reflection of the actual quotient, stated without dividing at possible
zeros of the Fourier factor away from threshold. -/
theorem centralNumerator_conj_cross_eqOn (y : ℝ) (hy : 0 < y)
    (j J : ℤ) (hj : j ≠ 0) :
    EqOn (fun κ => centralNumerator y hy j J κ *
        conj (centralFourierFactor y j (conj κ)))
      (fun κ => conj (centralNumerator y hy j J (conj κ)) *
        centralFourierFactor y j κ) (horizontalFourierDomain y hy) := by
  have hN := analyticOnNhd_centralNumerator y hy j J
  have hD : AnalyticOnNhd ℂ (centralFourierFactor y j)
      (horizontalFourierDomain y hy) := fun κ _ => centralFourierFactor_analyticAt hy hj κ
  apply eqOn_continuationRegion_of_common (horizontalContinuation y hy).radius_pos
    (hN.mul (analyticOnNhd_conj_reflect hD))
    ((analyticOnNhd_conj_reflect hN).mul hD)
  intro κ hκ
  rw [centralNumerator_eq_factor_mul_dirichlet y hy j J hj (by linarith),
    centralNumerator_eq_factor_mul_dirichlet y hy j J hj (by simpa using
      (show (1 / 2 : ℝ) < κ.re by linarith)), map_mul]
  have he : exponent (conj κ) = conj (exponent κ) := by simp [exponent, map_ofNat]
  rw [he, conj_kloostermanDirichlet j J (exponent κ) (by
    norm_num [exponent, Complex.add_re]
    linarith)]
  ring

/-- The explicit threshold denominator is real. -/
@[simp] theorem conj_centralFourierFactor_zero (y : ℝ) (j : ℤ) :
    conj (centralFourierFactor y j 0) = centralFourierFactor y j 0 := by
  rw [centralFourierFactor_zero]
  simp [map_ofNat]

/-- Reflection and cancellation of the nonzero K0 factor make the actual
threshold numerator real. -/
@[simp] theorem conj_centralNumerator_zero (y : ℝ) (hy : 0 < y)
    (j J : ℤ) (hj : j ≠ 0) :
    conj (centralNumerator y hy j J 0) = centralNumerator y hy j J 0 := by
  have h := centralNumerator_conj_cross_eqOn y hy j J hj
    (zero_mem_horizontalFourierDomain y hy)
  simp only [map_zero, conj_centralFourierFactor_zero] at h
  exact (mul_right_cancel₀ (centralFourierFactor_zero_ne_zero hy hj) h).symm

/-- The canonical central threshold zeta value is real; this is a theorem
about its actual analytic continuation, with no supplied reality premise. -/
@[simp] theorem conj_centralZeta_zero (j J : ℤ) (hj : j ≠ 0) :
    conj (centralZeta j J 0) = centralZeta j J 0 := by
  unfold centralZeta centralQuotient
  rw [map_div₀, conj_centralNumerator_zero 1 zero_lt_one j J hj,
    conj_centralFourierFactor_zero]

/-- Imaginary-part formulation of actual threshold reality. -/
@[simp] theorem centralZeta_zero_im (j J : ℤ) (hj : j ≠ 0) :
    (centralZeta j J 0).im = 0 := by
  have h := congrArg Complex.im (conj_centralZeta_zero j J hj)
  simp only [Complex.conj_im] at h
  linarith

/-- The frequency-swap identity is continued after cross multiplication, so
zeros of a Fourier factor away from threshold cause no division problem. -/
theorem centralNumerator_swap_cross_eqOn (j J : ℤ) (hj : j ≠ 0) (hJ : J ≠ 0) :
    EqOn (fun κ => centralNumerator 1 zero_lt_one j J κ * centralFourierFactor 1 J κ)
      (fun κ => centralNumerator 1 zero_lt_one J j κ * centralFourierFactor 1 j κ)
      (horizontalFourierDomain 1 zero_lt_one) := by
  have hD (m : ℤ) (hm : m ≠ 0) : AnalyticOnNhd ℂ (centralFourierFactor 1 m)
      (horizontalFourierDomain 1 zero_lt_one) :=
    fun κ _ => centralFourierFactor_analyticAt zero_lt_one hm κ
  apply eqOn_continuationRegion_of_common (horizontalContinuation 1 zero_lt_one).radius_pos
    ((analyticOnNhd_centralNumerator 1 zero_lt_one j J).mul (hD J hJ))
    ((analyticOnNhd_centralNumerator 1 zero_lt_one J j).mul (hD j hj))
  intro κ hκ
  rw [centralNumerator_eq_factor_mul_dirichlet 1 zero_lt_one j J hj (by linarith),
    centralNumerator_eq_factor_mul_dirichlet 1 zero_lt_one J j hJ (by linarith),
    kloostermanDirichlet_symm j J]
  ring

/-- The actual threshold central value is symmetric in its nonzero frequencies. -/
theorem centralZeta_zero_symm (j J : ℤ) (hj : j ≠ 0) (hJ : J ≠ 0) :
    centralZeta j J 0 = centralZeta J j 0 := by
  unfold centralZeta centralQuotient
  apply (div_eq_div_iff (centralFourierFactor_zero_ne_zero zero_lt_one hj)
    (centralFourierFactor_zero_ne_zero zero_lt_one hJ)).mpr
  exact centralNumerator_swap_cross_eqOn j J hj hJ
    (zero_mem_horizontalFourierDomain 1 zero_lt_one)

/-- The actual nonzero-frequency central matrix is Hermitian. -/
theorem conj_centralZeta_zero_swap (j J : ℤ) (hj : j ≠ 0) (hJ : J ≠ 0) :
    conj (centralZeta J j 0) = centralZeta j J 0 := by
  rw [conj_centralZeta_zero J j hJ, centralZeta_zero_symm J j hJ hj]

end GapFamily.Analytic.PoincareCentralZeta
