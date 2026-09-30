import GapFamily.Construction.InitialCellPolynomial
import GapFamily.Construction.InitialCellSignedDensity

/-!
# Initial-cell moment positivity and variation reserve

A lower bound on the upper half and a bound on total negative mass suffice.
The resulting moment functional need not come from a nonnegative density.
The exponential degree loss is exactly `6^k`, so the construction's initial
positive and negative exponential budgets remain distinct.
-/

noncomputable section

open MeasureTheory Set
open GapFamily.Quadrature

namespace GapFamily.Construction

/-- The positive upper-half moment remaining after the signed loss. -/
def initialCellMomentMargin (a b A N : ℝ) (k : ℕ) : ℝ :=
  A * (b - a) / (32 * ((k : ℝ) + 1) ^ 3) - N * (6 : ℝ) ^ k

/-- The margin divided by the proved polynomial variation factor. -/
def initialCellVariationReserve (a b A N : ℝ) (k : ℕ) : ℝ :=
  initialCellMomentMargin a b A N k / (4 * ((k : ℝ) + 1) ^ 3 * (6 : ℝ) ^ k)

/-- The ordinary signed functional has the explicit initial-cell lower bound
at any maximum attained on the upper half. -/
theorem initialCell_polynomial_moment_lower {a b A N : ℝ} (hab : a < b) (hA : 0 ≤ A)
    (q : ℝ → ℝ) (hq : IntervalIntegrable q volume a b)
    (hnegative : initialCellNegativeMass a b q ≤ N)
    (hupper : ∀ x ∈ Icc ((a + b) / 2) b, A ≤ q x)
    (p : Polynomial ℝ) (k : ℕ) (hdeg : p.natDegree ≤ k)
    (hpos : ∀ x ∈ Icc a b, 0 ≤ p.eval x) {t : ℝ}
    (ht : t ∈ Icc ((a + b) / 2) b)
    (hmax : ∀ x ∈ Icc ((a + b) / 2) b, p.eval x ≤ p.eval t) :
    initialCellMomentMargin a b A N k * p.eval t ≤ signedDensityFunctional a b q hq p := by
  have hsub : Icc ((a + b) / 2) b ⊆ Icc a b := Icc_subset_Icc_left (by linarith)
  have hS : 0 ≤ p.eval t := hpos t (hsub ht)
  have hupperBound : ∀ x ∈ Icc ((a + b) / 2) b, |p.eval x| ≤ p.eval t := by
    intro x hx
    rw [abs_of_nonneg (hpos x (hsub hx))]
    exact hmax x hx
  have hfull : ∀ x ∈ Icc a b, p.eval x ≤ (6 : ℝ) ^ k * p.eval t := by
    intro x hx
    exact (le_abs_self _).trans (initialCell_polynomial_extrapolation p k hab hdeg hupperBound hx)
  have hmass := polynomial_upperHalf_intervalIntegral_lower p k hab hdeg
    (fun x hx => hpos x (hsub hx)) ht
  have hsigned := initialCell_signed_integral_lower (by linarith : a ≤ (a + b) / 2)
    (by linarith : (a + b) / 2 ≤ b) (by positivity : 0 ≤ (6 : ℝ) ^ k * p.eval t)
    q hq hnegative hupper p.eval p.continuous.continuousOn hpos hfull
  have hscale := mul_le_mul_of_nonneg_left hmass hA
  change _ ≤ ∫ x in a..b, p.eval x * q x
  unfold initialCellMomentMargin
  calc
    _ = A * ((b - a) / (32 * ((k : ℝ) + 1) ^ 3) * p.eval t) -
        (6 : ℝ) ^ k * p.eval t * N := by ring
    _ ≤ A * (∫ x in (a + b) / 2..b, p.eval x) - (6 : ℝ) ^ k * p.eval t * N :=
      sub_le_sub_right hscale _
    _ ≤ _ := hsigned

/-- A positive initial margin makes every nonzero nonnegative polynomial
moment strictly positive, uniformly through the specified degree. -/
theorem initialCell_signedDensityFunctional_strictPositive
    {a b A N : ℝ} (hab : a < b) (hA : 0 ≤ A)
    (q : ℝ → ℝ) (hq : IntervalIntegrable q volume a b)
    (hnegative : initialCellNegativeMass a b q ≤ N)
    (hupper : ∀ x ∈ Icc ((a + b) / 2) b, A ≤ q x)
    (k : ℕ) (hmargin : 0 < initialCellMomentMargin a b A N k)
    (p : Polynomial ℝ) (hdeg : p.natDegree ≤ k) (hp : p ≠ 0)
    (hpos : ∀ x ∈ Icc a b, 0 ≤ p.eval x) :
    0 < signedDensityFunctional a b q hq p := by
  have hmid : (a + b) / 2 < b := by linarith
  have hsub : Icc ((a + b) / 2) b ⊆ Icc a b := Icc_subset_Icc_left (by linarith)
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hmid.le) p.continuous.continuousOn
  have hS : 0 < p.eval t := by
    by_contra hnot
    have hS0 : p.eval t ≤ 0 := le_of_not_gt hnot
    apply hp
    apply p.eq_zero_of_infinite_isRoot
    apply (Icc_infinite hmid).mono
    intro x hx
    exact le_antisymm ((hmax hx).trans hS0) (hpos x (hsub hx))
  exact (mul_pos hmargin hS).trans_le
    (initialCell_polynomial_moment_lower hab hA q hq hnegative hupper p k hdeg hpos ht
      (fun _ hx => hmax hx))

/-- The same explicit margin gives the actual partition-variation reserve. -/
theorem initialCell_signedDensityFunctional_variation_reserve
    {a b A N : ℝ} (hab : a < b) (hA : 0 ≤ A)
    (q : ℝ → ℝ) (hq : IntervalIntegrable q volume a b)
    (hnegative : initialCellNegativeMass a b q ≤ N)
    (hupper : ∀ x ∈ Icc ((a + b) / 2) b, A ≤ q x)
    (k : ℕ) (hmargin : 0 ≤ initialCellMomentMargin a b A N k)
    (p : Polynomial ℝ) (hdeg : p.natDegree ≤ k)
    (hpos : ∀ x ∈ Icc a b, 0 ≤ p.eval x) :
    initialCellVariationReserve a b A N k * (eVariationOn p.eval (Icc a b)).toReal ≤
      signedDensityFunctional a b q hq p := by
  have hmid : (a + b) / 2 < b := by linarith
  have hsub : Icc ((a + b) / 2) b ⊆ Icc a b := Icc_subset_Icc_left (by linarith)
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hmid.le) p.continuous.continuousOn
  have hupperBound : ∀ x ∈ Icc ((a + b) / 2) b, |p.eval x| ≤ p.eval t := by
    intro x hx
    rw [abs_of_nonneg (hpos x (hsub hx))]
    exact hmax hx
  have hreserve : 0 ≤ initialCellVariationReserve a b A N k := by
    exact div_nonneg hmargin (by positivity)
  have hvar := mul_le_mul_of_nonneg_left
    (initialCell_polynomial_variation_le p k hab hdeg hupperBound) hreserve
  have heq : initialCellVariationReserve a b A N k *
      (4 * ((k : ℝ) + 1) ^ 3 * (6 : ℝ) ^ k * p.eval t) =
      initialCellMomentMargin a b A N k * p.eval t := by
    unfold initialCellVariationReserve
    field_simp
  rw [heq] at hvar
  exact hvar.trans (initialCell_polynomial_moment_lower hab hA q hq hnegative hupper
    p k hdeg hpos ht (fun _ hx => hmax hx))

/-- A signed initial cell with the prescribed integer mass has exactly that
many unit nodes once the explicit upper-half reserve exceeds one half. -/
theorem exists_initialCell_unit_nodes {a b A Nminus : ℝ} {k N : ℕ}
    (hab : a < b) (hA : 0 ≤ A) (q : ℝ → ℝ) (hq : IntervalIntegrable q volume a b)
    (hnegative : initialCellNegativeMass a b q ≤ Nminus)
    (hupper : ∀ x ∈ Icc ((a + b) / 2) b, A ≤ q x)
    (hN : 0 < N) (hmass : (∫ x in a..b, q x) = (N : ℝ))
    (hreserve : 1 / 2 < initialCellVariationReserve a b A Nminus k) :
    ∃ node : Fin N → ℝ, (∀ i, node i ∈ Ioo a b) ∧
      ∀ p : Polynomial ℝ, p.natDegree ≤ k →
        ∑ i, p.eval (node i) = ∫ x in a..b, p.eval x * q x := by
  have hmargin : 0 ≤ initialCellMomentMargin a b A Nminus k := by
    have hpos : 0 < initialCellVariationReserve a b A Nminus k := lt_trans (by norm_num) hreserve
    exact ((div_pos_iff_of_pos_right (by positivity)).mp hpos).le
  apply exists_interior_unit_nodes_of_variation_reserve hab hN hreserve
    (signedDensityFunctional a b q hq)
  · simpa only [signedDensityFunctional, LinearMap.coe_mk, AddHom.coe_mk,
      Polynomial.eval_one, one_mul] using hmass
  · intro p hdeg hpos
    exact initialCell_signedDensityFunctional_variation_reserve hab hA q hq hnegative hupper
      k hmargin p hdeg hpos

end GapFamily.Construction
