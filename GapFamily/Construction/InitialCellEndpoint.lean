import GapFamily.Construction.InitialCellMoment
import GapFamily.Construction.CellEndpoint

/-!
# Integer endpoint and unit nodes for an initial cell

A single upper-half density bound and negative-mass budget work throughout
the endpoint window. The shortest-cell variation reserve supplies positive
initial mass and persists when the endpoint increases.
-/

open Set MeasureTheory
open GapFamily.Quadrature

namespace GapFamily.Construction

/-- Negative mass cannot increase when a positive-length cell is shortened. -/
theorem initialCellNegativeMass_mono_right {a u w : ℝ} (hau : a ≤ u) (huw : u ≤ w)
    (q : ℝ → ℝ) (hq : IntervalIntegrable q volume a w) :
    initialCellNegativeMass a u q ≤ initialCellNegativeMass a w q :=
  intervalIntegral.integral_mono_interval le_rfl hau huw
    (Filter.Eventually.of_forall fun _ => le_max_right _ _)
    (initialCell_negativePart_intervalIntegrable hq)

/-- The initial-cell polynomial margin increases with the right endpoint. -/
theorem initialCellMomentMargin_mono_right {a u V A N : ℝ} (k : ℕ)
    (huV : u ≤ V) (hA : 0 ≤ A) :
    initialCellMomentMargin a u A N k ≤ initialCellMomentMargin a V A N k := by
  unfold initialCellMomentMargin
  exact sub_le_sub_right (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sub_le_sub_right huV a) hA) (by positivity)) _

/-- The shortest initial cell gives a uniform variation reserve on the
entire endpoint window. -/
theorem initialCellVariationReserve_mono_right {a u V A N : ℝ} (k : ℕ)
    (huV : u ≤ V) (hA : 0 ≤ A) :
    initialCellVariationReserve a u A N k ≤ initialCellVariationReserve a V A N k := by
  unfold initialCellVariationReserve
  exact div_le_div_of_nonneg_right (initialCellMomentMargin_mono_right k huV hA) (by positivity)

/-- Endpoint selection and the initial-cell reserve produce exactly the
integer mass of unit nodes. The density may be signed on the lower portion. -/
theorem exists_initialCell_integer_endpoint_unit_nodes
    {a u w A Nminus : ℝ} {k : ℕ} (hau : a < u) (huw : u ≤ w) (hA : 0 ≤ A)
    (q : ℝ → ℝ) (hq : IntervalIntegrable q volume a w)
    (hnegative : initialCellNegativeMass a w q ≤ Nminus)
    (hupper : ∀ x ∈ Icc ((a + u) / 2) w, A ≤ q x)
    (hincrement : 1 < ∫ x in u..w, q x)
    (hreserve : 1 / 2 < initialCellVariationReserve a u A Nminus k) :
    ∃ V ∈ Icc u w, ∃ N : ℕ, 0 < N ∧ (∫ x in a..V, q x) = (N : ℝ) ∧
      ∃ node : Fin N → ℝ, (∀ i, node i ∈ Ioo a V) ∧
        ∀ p : Polynomial ℝ, p.natDegree ≤ k →
          ∑ i, p.eval (node i) = ∫ x in a..V, p.eval x * q x := by
  have hqu : IntervalIntegrable q volume a u := hq.mono_set (by
    rw [uIcc_of_le hau.le, uIcc_of_le (hau.le.trans huw)]
    exact Icc_subset_Icc_right huw)
  have hnegativeu : initialCellNegativeMass a u q ≤ Nminus :=
    (initialCellNegativeMass_mono_right hau.le huw q hq).trans hnegative
  have hupperu : ∀ x ∈ Icc ((a + u) / 2) u, A ≤ q x :=
    fun x hx => hupper x (Icc_subset_Icc_right huw hx)
  have hmargin : 0 < initialCellMomentMargin a u A Nminus k := by
    have hp : 0 < initialCellVariationReserve a u A Nminus k :=
      lt_trans (by norm_num) hreserve
    exact (div_pos_iff_of_pos_right (by positivity)).mp hp
  have hinitial : 0 ≤ ∫ x in a..u, q x := by
    have hp := initialCell_signedDensityFunctional_strictPositive hau hA q hqu
      hnegativeu hupperu k hmargin 1 (by simp) one_ne_zero (by intro x hx; simp)
    exact le_of_lt (by simpa [signedDensityFunctional] using hp)
  obtain ⟨V, hV, N, hN, hmass⟩ :=
    exists_integer_mass_endpoint hau.le huw q hq hinitial hincrement
  have haV : a < V := hau.trans_le hV.1
  have hqV : IntervalIntegrable q volume a V := hq.mono_set (by
    rw [uIcc_of_le haV.le, uIcc_of_le (hau.le.trans huw)]
    exact Icc_subset_Icc_right hV.2)
  have hnegativeV : initialCellNegativeMass a V q ≤ Nminus :=
    (initialCellNegativeMass_mono_right haV.le hV.2 q hq).trans hnegative
  have hupperV : ∀ x ∈ Icc ((a + V) / 2) V, A ≤ q x := by
    intro x hx
    exact hupper x ⟨by linarith [hV.1, hx.1], hx.2.trans hV.2⟩
  refine ⟨V, hV, N, hN, hmass, ?_⟩
  exact exists_initialCell_unit_nodes haV hA q hqV hnegativeV hupperV hN hmass
    (hreserve.trans_le (initialCellVariationReserve_mono_right k hV.1 hA))

end GapFamily.Construction
