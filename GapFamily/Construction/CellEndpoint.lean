import GapFamily.Quadrature.PolynomialBound
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Integer-mass endpoints for signed cells

The endpoint map is the actual primitive of an integrable signed density.
An increment exceeding one crosses a positive integer; no sign restriction on
the already processed portion of the interval is needed.
-/

open Set MeasureTheory

namespace GapFamily.Construction

/-- An integrable signed density whose mass grows by more than one across the
endpoint window admits an endpoint of positive integer total mass. -/
theorem exists_integer_mass_endpoint {a u w : ℝ} (hau : a ≤ u) (huw : u ≤ w)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume a w)
    (hinitial : 0 ≤ ∫ x in a..u, f x) (hincrement : 1 < ∫ x in u..w, f x) :
    ∃ V ∈ Icc u w, ∃ N : ℕ, 0 < N ∧ (∫ x in a..V, f x) = (N : ℝ) := by
  let m := ∫ x in a..u, f x
  let N : ℕ := ⌊m⌋₊ + 1
  have hNu : m < (N : ℝ) := by simpa [N] using Nat.lt_floor_add_one m
  have hNupper : (N : ℝ) ≤ m+1 := by
    simpa [N] using add_le_add_right (Nat.floor_le hinitial) 1
  have hfu : IntervalIntegrable f volume a u := hf.mono_set (by
    rw [uIcc_of_le hau, uIcc_of_le (hau.trans huw)]
    exact Icc_subset_Icc_right huw)
  have hfuw : IntervalIntegrable f volume u w := hf.mono_set (by
    rw [uIcc_of_le huw, uIcc_of_le (hau.trans huw)]
    exact Icc_subset_Icc_left hau)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hfu hfuw
  have hNw : (N : ℝ) ≤ ∫ x in a..w, f x := by
    dsimp [m] at hNupper
    linarith
  have hcont : ContinuousOn (fun V => ∫ x in a..V, f x) (Icc u w) := by
    apply (intervalIntegral.continuousOn_primitive_interval' hf left_mem_uIcc).mono
    rw [uIcc_of_le (hau.trans huw)]
    exact Icc_subset_Icc_left hau
  obtain ⟨V, hV, hmass⟩ := intermediate_value_Icc huw hcont ⟨hNu.le, hNw⟩
  exact ⟨V, hV, N, Nat.succ_pos _, hmass⟩

/-- A pointwise lower bound on a half-length or longer window supplies the
increment hypothesis used for endpoint selection. The earlier density may be signed. -/
theorem exists_integer_mass_endpoint_of_lower_bound
    {a u w c : ℝ} (hau : a ≤ u) (hwindow : 1/2 ≤ w-u) (hc : 2 < c)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume a w)
    (hinitial : 0 ≤ ∫ x in a..u, f x)
    (hbound : ∀ x ∈ Icc u w, c ≤ f x) :
    ∃ V ∈ Icc u w, ∃ N : ℕ, 0 < N ∧ (∫ x in a..V, f x) = (N : ℝ) := by
  have huw : u ≤ w := by linarith
  apply exists_integer_mass_endpoint hau huw f hf hinitial
  have hfuw : IntervalIntegrable f volume u w := hf.mono_set (by
    rw [uIcc_of_le huw, uIcc_of_le (hau.trans huw)]
    exact Icc_subset_Icc_left hau)
  have hmass := intervalIntegral.integral_mono_on huw intervalIntegrable_const hfuw hbound
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hmass
  have hproduct := mul_le_mul_of_nonneg_right hwindow (show 0 ≤ c by linarith)
  nlinarith

/-- Once the quadratic bracket is nonnegative, increasing the cell's right
endpoint increases the explicit C3 variation reserve. -/
theorem signed_density_reserve_mono {a u V A B : ℝ} (k : ℕ)
    (hau : a ≤ u) (huV : u ≤ V) (hA : 0 ≤ A)
    (hbracket : 0 ≤ A*(u-a)^2/(8192*((k : ℝ)+1)^6)-B) :
    (A*(u-a)^2/(8192*((k : ℝ)+1)^6)-B)*(u-a)/(64*((k : ℝ)+1)^6) ≤
      (A*(V-a)^2/(8192*((k : ℝ)+1)^6)-B)*(V-a)/(64*((k : ℝ)+1)^6) := by
  have hd : 0 ≤ u-a := sub_nonneg.mpr hau
  have hdV : u-a ≤ V-a := sub_le_sub_right huV a
  have hs : (u-a)^2 ≤ (V-a)^2 := by nlinarith
  have hbr : A*(u-a)^2/(8192*((k : ℝ)+1)^6)-B ≤
      A*(V-a)^2/(8192*((k : ℝ)+1)^6)-B :=
    sub_le_sub_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs hA) (by positivity)) B
  exact div_le_div_of_nonneg_right
    (mul_le_mul hbr hdV hd (hbracket.trans hbr)) (by positivity)

/-- Endpoint selection followed by C3 and C4 gives an actual finite unit-node
cell. The numerical reserve is checked only at the shortest allowed cell. -/
theorem exists_integer_mass_cell_unit_nodes
    {a u w A B : ℝ} {k : ℕ} (ha : 0 ≤ a) (hau : a < u) (huw : u ≤ w) (hA : 0 ≤ A)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume a w)
    (hinitial : 0 ≤ ∫ x in a..u, f x) (hincrement : 1 < ∫ x in u..w, f x)
    (hbound : ∀ x ∈ Icc a w, A*x^2-B ≤ f x)
    (hreserve : 1/2 < (A*(u-a)^2/(8192*((k : ℝ)+1)^6)-B)*(u-a)/(64*((k : ℝ)+1)^6)) :
    ∃ V ∈ Icc u w, ∃ N : ℕ, 0 < N ∧ (∫ x in a..V, f x) = (N : ℝ) ∧
      ∃ node : Fin N → ℝ, (∀ j, node j ∈ Icc a V) ∧
        ∀ p : Polynomial ℝ, p.natDegree ≤ k →
          ∑ j, p.eval (node j) = ∫ x in a..V, p.eval x * f x := by
  obtain ⟨V, hV, N, hN, hmass⟩ := exists_integer_mass_endpoint hau.le huw f hf hinitial hincrement
  have hbracket : 0 ≤ A*(u-a)^2/(8192*((k : ℝ)+1)^6)-B := by
    have hpos : 0 < (A*(u-a)^2/(8192*((k : ℝ)+1)^6)-B)*(u-a)/(64*((k : ℝ)+1)^6) :=
      lt_trans (by norm_num) hreserve
    have hmul := (div_pos_iff_of_pos_right (show 0 < 64*((k : ℝ)+1)^6 by positivity)).mp hpos
    exact (pos_of_mul_pos_left hmul (sub_nonneg.mpr hau.le)).le
  have haV : a < V := hau.trans_le hV.1
  have hfV : IntervalIntegrable f volume a V := hf.mono_set (by
    rw [uIcc_of_le haV.le, uIcc_of_le (hau.le.trans huw)]
    exact Icc_subset_Icc_right hV.2)
  refine ⟨V, hV, N, hN, hmass, ?_⟩
  apply GapFamily.Quadrature.exists_unit_nodes_of_signed_density_lower_bound ha haV hA
    f hfV (fun x hx => hbound x (Icc_subset_Icc_right hV.2 hx)) hN hmass
  exact hreserve.trans_le (signed_density_reserve_mono k hau.le hV.1 hA hbracket)

/-- Two explicit scalar inequalities suffice to construct a signed cell with
an integer-mass endpoint and exact unit nodes. The shortest-cell reserve proves
positive initial mass, and the terminal-window lower bound supplies the increment. -/
theorem exists_signed_cell_of_quadratic_window
    {a u w A B : ℝ} {k : ℕ} (ha : 0 ≤ a) (hau : a < u)
    (hwindow : 1/2 ≤ w-u) (hA : 0 ≤ A)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume a w)
    (hbound : ∀ x ∈ Icc a w, A*x^2-B ≤ f x)
    (hterminal : 2 < A*u^2-B)
    (hreserve : 1/2 < (A*(u-a)^2/(8192*((k : ℝ)+1)^6)-B)*(u-a)/(64*((k : ℝ)+1)^6)) :
    ∃ V ∈ Icc u w, ∃ N : ℕ, 0 < N ∧ (∫ x in a..V, f x) = (N : ℝ) ∧
      ∃ node : Fin N → ℝ, (∀ j, node j ∈ Icc a V) ∧
        ∀ p : Polynomial ℝ, p.natDegree ≤ k →
          ∑ j, p.eval (node j) = ∫ x in a..V, p.eval x * f x := by
  have huw : u ≤ w := by linarith
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
    have hprod := mul_le_mul_of_nonneg_right hwindow (show 0 ≤ A*u^2-B by linarith)
    nlinarith
  exact exists_integer_mass_cell_unit_nodes ha hau huw hA f hf hinitial hincrement hbound hreserve

end GapFamily.Construction
