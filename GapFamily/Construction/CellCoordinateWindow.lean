import GapFamily.Construction.CellEndpoint

/-!
# Endpoint selection on the actual transformed window

An energy window of length one half need not have coordinate length one half.
The endpoint argument therefore uses its actual transformed length.
-/

open Set MeasureTheory

namespace GapFamily.Construction

/-- C3 and C4 on any positive-length terminal window, with its actual mass
lower bound. No fixed lower bound on the coordinate window length is assumed. -/
theorem exists_signed_cell_of_quadratic_variable_window
    {a u w A B : ℝ} {k : ℕ} (ha : 0 ≤ a) (hau : a < u)
    (huw : u ≤ w) (hA : 0 ≤ A)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume a w)
    (hbound : ∀ x ∈ Icc a w, A*x^2-B ≤ f x)
    (hterminal : 1 < (A*u^2-B)*(w-u))
    (hreserve : 1/2 < (A*(u-a)^2/(8192*((k : ℝ)+1)^6)-B)*(u-a)/(64*((k : ℝ)+1)^6)) :
    ∃ V ∈ Icc u w, ∃ N : ℕ, 0 < N ∧ (∫ x in a..V, f x) = (N : ℝ) ∧
      ∃ node : Fin N → ℝ, (∀ j, node j ∈ Icc a V) ∧
        ∀ p : Polynomial ℝ, p.natDegree ≤ k →
          ∑ j, p.eval (node j) = ∫ x in a..V, p.eval x * f x := by
  have hbracket : 0 < A*(u-a)^2/(8192*((k : ℝ)+1)^6)-B := by
    have hpos : 0 < (A*(u-a)^2/(8192*((k : ℝ)+1)^6)-B)*(u-a)/(64*((k : ℝ)+1)^6) :=
      lt_trans (by norm_num) hreserve
    have hmul := (div_pos_iff_of_pos_right (show 0 < 64*((k : ℝ)+1)^6 by positivity)).mp hpos
    exact pos_of_mul_pos_left hmul (sub_nonneg.mpr hau.le)
  have hfu : IntervalIntegrable f volume a u := hf.mono_set (by
    rw [uIcc_of_le hau.le, uIcc_of_le (hau.le.trans huw)]
    exact Icc_subset_Icc_right huw)
  have hinitial : 0 ≤ ∫ x in a..u, f x := by
    have hp := GapFamily.Quadrature.signedDensityFunctional_strictPositive ha hau hA
      f hfu (fun x hx => hbound x (Icc_subset_Icc_right huw hx)) k hbracket
      1 (by simp) one_ne_zero (by intro x _; simp)
    exact le_of_lt (by simpa [GapFamily.Quadrature.signedDensityFunctional] using hp)
  have hfuw : IntervalIntegrable f volume u w := hf.mono_set (by
    rw [uIcc_of_le huw, uIcc_of_le (hau.le.trans huw)]
    exact Icc_subset_Icc_left hau.le)
  have hbounduw : ∀ x ∈ Icc u w, A*u^2-B ≤ f x := by
    intro x hx
    apply le_trans _ (hbound x (Icc_subset_Icc_left hau.le hx))
    apply sub_le_sub_right
    apply mul_le_mul_of_nonneg_left _ hA
    have hu : 0 ≤ u := ha.trans hau.le
    nlinarith [hx.1]
  have hincrement : 1 < ∫ x in u..w, f x := by
    have hi := intervalIntegral.integral_mono_on huw intervalIntegrable_const hfuw hbounduw
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
    exact hterminal.trans_le (by simpa only [mul_comm] using hi)
  exact exists_integer_mass_cell_unit_nodes ha hau huw hA f hf hinitial hincrement hbound hreserve

end GapFamily.Construction
