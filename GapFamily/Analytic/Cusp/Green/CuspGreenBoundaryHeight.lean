import GapFamily.Analytic.Cusp.Green.CuspGreenSolutionBasic

/-!
# Change of the scalar Dirichlet boundary height

Moving the boundary from `a` to `b` changes the actual compact-source Green
solution by one outgoing exponential, whose coefficient is its value at `b`.
The finite-integral definition makes the identity valid also at parameter zero.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set

/-- Above the new boundary, the kernel difference is an outgoing boundary value. -/
theorem cuspGreen_boundaryHeight_above (a b t u : ℝ) (hbu : b ≤ u)
    (κ : ℂ) :
    cuspGreen a t u κ = cuspGreen b t u κ +
      Complex.exp (-κ * ((t-b : ℝ) : ℂ)) * cuspGreen a b u κ := by
  by_cases hκ : κ = 0
  · subst κ
    simp only [cuspGreen_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul,
      min_eq_left hbu]
    push_cast
    ring
  · have hfirst :
        Complex.exp (-κ * ((t-b : ℝ) : ℂ)) *
          Complex.exp (-κ * ((u-b : ℝ) : ℂ)) =
          Complex.exp (-κ * ((t+u-2*b : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hsecond :
        Complex.exp (-κ * ((t-b : ℝ) : ℂ)) *
          Complex.exp (-κ * ((b+u-2*a : ℝ) : ℂ)) =
          Complex.exp (-κ * ((t+u-2*a : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [cuspGreen_eq_quotient a t u hκ, cuspGreen_eq_quotient b t u hκ,
      cuspGreen_eq_quotient a b u hκ,
      abs_of_nonpos (sub_nonpos.mpr hbu)]
    have habs : -(b-u) = u-b := by ring
    rw [habs, ← mul_div_assoc, mul_sub, hfirst, hsecond]
    ring

/-- A source below the new boundary contributes only its outgoing boundary value. -/
theorem cuspGreen_boundaryHeight_below (a b t u : ℝ) (hbt : b ≤ t) (hub : u ≤ b)
    (κ : ℂ) :
    cuspGreen a t u κ =
      Complex.exp (-κ * ((t-b : ℝ) : ℂ)) * cuspGreen a b u κ := by
  by_cases hκ : κ = 0
  · subst κ
    simp only [cuspGreen_zero, min_eq_right (hub.trans hbt), min_eq_right hub,
      neg_zero, zero_mul, Complex.exp_zero, one_mul]
  · have hfirst :
        Complex.exp (-κ * ((t-b : ℝ) : ℂ)) *
          Complex.exp (-κ * ((b-u : ℝ) : ℂ)) =
          Complex.exp (-κ * ((t-u : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hsecond :
        Complex.exp (-κ * ((t-b : ℝ) : ℂ)) *
          Complex.exp (-κ * ((b+u-2*a : ℝ) : ℂ)) =
          Complex.exp (-κ * ((t+u-2*a : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [cuspGreen_eq_quotient a t u hκ, cuspGreen_eq_quotient a b u hκ,
      abs_of_nonneg (sub_nonneg.mpr (hub.trans hbt)),
      abs_of_nonneg (sub_nonneg.mpr hub), ← mul_div_assoc, mul_sub, hfirst, hsecond]

/-- Raising the boundary changes the actual compact-source solution by one outgoing term. -/
theorem cuspGreenSolution_boundaryHeight (a b t : ℝ) (hab : a ≤ b) (hbt : b ≤ t)
    (κ : ℂ) {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    cuspGreenSolution a κ f t = cuspGreenSolution b κ f t +
      Complex.exp (-κ * ((t-b : ℝ) : ℂ)) * cuspGreenSolution a κ f b := by
  obtain ⟨T, hT, hfT⟩ := exists_cuspSource_cutoff hfc b
  let E : ℂ := Complex.exp (-κ * ((t-b : ℝ) : ℂ))
  have hk (c v : ℝ) : Continuous (fun u : ℝ => cuspGreen c v u κ * f u) :=
    (cuspGreen_continuous_source c v κ).mul hf
  have hleft :
      (∫ u in a..b, cuspGreen a t u κ * f u) =
        E * (∫ u in a..b, cuspGreen a b u κ * f u) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hab] at hu
    dsimp only
    rw [cuspGreen_boundaryHeight_below a b t u hbt hu.2]
    dsimp only [E]
    ring
  have hright :
      (∫ u in b..T, cuspGreen a t u κ * f u) =
        (∫ u in b..T, cuspGreen b t u κ * f u) +
          E * (∫ u in b..T, cuspGreen a b u κ * f u) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hk b t).intervalIntegrable b T)
        (((hk a b).const_mul E).intervalIntegrable b T)]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hT.le] at hu
    dsimp only
    rw [cuspGreen_boundaryHeight_above a b t u hu.1]
    dsimp only [E]
    ring
  rw [cuspGreenSolution_eq_interval a T t (hab.trans hT.le) κ hfT,
    cuspGreenSolution_eq_interval b T t hT.le κ hfT,
    cuspGreenSolution_eq_interval a T b (hab.trans hT.le) κ hfT,
    ← intervalIntegral.integral_add_adjacent_intervals
      ((hk a t).intervalIntegrable a b) ((hk a t).intervalIntegrable b T),
    ← intervalIntegral.integral_add_adjacent_intervals
      ((hk a b).intervalIntegrable a b) ((hk a b).intervalIntegrable b T), hleft, hright]
  dsimp only [E]
  ring

end GapFamily.Analytic
