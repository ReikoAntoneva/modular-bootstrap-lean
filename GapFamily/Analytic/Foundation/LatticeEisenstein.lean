import GapFamily.Analytic.Foundation.LatticeHeight
import GapFamily.Analytic.Poincare.PoincareAnalytic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Scalar lattice and cusp-series normalization

Absolute convergence justifies the decomposition of nonzero integer rows into
positive integer scales of primitive rows. Each cusp coset accounts for exactly
the two signs of one primitive row, giving the factor `2 * riemannZeta (2*s)`.
-/

namespace GapFamily.Analytic

open Complex Matrix Matrix.SpecialLinearGroup EisensteinSeries
open scoped Real MatrixGroups UpperHalfPlane

noncomputable section

abbrev PrimitiveRow := EisensteinSeries.gammaSet 1 1 0

def signedCuspBottomRow (p : CuspCoset × Bool) : PrimitiveRow :=
  ⟨if p.2 then cuspBottomRow p.1 else -cuspBottomRow p.1, by
    rw [EisensteinSeries.mem_gammaSet_one]
    split
    · exact cuspBottomRow_coprime _
    · simpa only [Pi.neg_apply, IsCoprime.neg_left_iff, IsCoprime.neg_right_iff] using
        cuspBottomRow_coprime p.1⟩

lemma cuspBottomRow_eq_of_eq_or_neg {q r : CuspCoset}
    (h : cuspBottomRow q = cuspBottomRow r ∨ cuspBottomRow q = -cuspBottomRow r) :
    q = r := by
  apply Quotient.out_equiv_out.mp
  exact (cuspRel_iff_bottomRow q.out r.out).mpr h

lemma cuspBottomRow_ne_neg_self (q : CuspCoset) :
    cuspBottomRow q ≠ -cuspBottomRow q := by
  intro h
  apply cuspBottomRow_ne_zero q
  funext i
  have hi := congrFun h i
  simp only [Pi.neg_apply] at hi
  change cuspBottomRow q i = 0
  omega

lemma signedCuspBottomRow_injective : Function.Injective signedCuspBottomRow := by
  rintro ⟨q, b⟩ ⟨r, d⟩ h
  have h' := congrArg Subtype.val h
  cases b <;> cases d
  · simp only [signedCuspBottomRow, Bool.false_eq_true, ↓reduceIte] at h'
    have hqr : q = r := cuspBottomRow_injective (neg_injective h')
    simp [hqr]
  · simp only [signedCuspBottomRow, Bool.false_eq_true, ↓reduceIte] at h'
    have hqr : q = r := cuspBottomRow_eq_of_eq_or_neg (Or.inr (neg_eq_iff_eq_neg.mp h'))
    subst r
    exact (cuspBottomRow_ne_neg_self q h'.symm).elim
  · simp only [signedCuspBottomRow, Bool.false_eq_true, ↓reduceIte] at h'
    have hqr : q = r := cuspBottomRow_eq_of_eq_or_neg (Or.inr h')
    subst r
    exact (cuspBottomRow_ne_neg_self q h').elim
  · simp only [signedCuspBottomRow, ↓reduceIte] at h'
    have hqr : q = r := cuspBottomRow_injective h'
    simp [hqr]

lemma signedCuspBottomRow_surjective : Function.Surjective signedCuspBottomRow := by
  intro v
  obtain ⟨g, hg⟩ := primitiveRow_has_representative v.1
    ((EisensteinSeries.mem_gammaSet_one _).mp v.2)
  let q : CuspCoset := Quotient.mk _ g
  have hrel : QuotientGroup.rightRel cuspInfinity q.out g := Quotient.exact q.out_eq
  have hrow := (cuspRel_iff_bottomRow q.out g).mp hrel
  rcases hrow with heq | heq
  · refine ⟨(q, true), Subtype.ext ?_⟩
    simpa [signedCuspBottomRow, cuspBottomRow] using heq.trans hg
  · refine ⟨(q, false), Subtype.ext ?_⟩
    simp [signedCuspBottomRow, cuspBottomRow, heq, hg]

def cuspSignedRowEquiv : (CuspCoset × Bool) ≃ PrimitiveRow :=
  Equiv.ofBijective signedCuspBottomRow
    ⟨signedCuspBottomRow_injective, signedCuspBottomRow_surjective⟩

lemma signedCuspBottomRow_height (q : CuspCoset) (b : Bool) (s : ℂ)
    (z : UpperHalfPlane) :
    (((z.im / Complex.normSq
      (((cuspSignedRowEquiv (q, b)).1 0 : ℂ) * z +
        (cuspSignedRowEquiv (q, b)).1 1)) : ℝ) : ℂ) ^ s =
      complexPoincareTerm 0 0 s z q := by
  rw [complexPoincareTerm_out]
  simp only [complexPointSeed, mul_zero, zero_mul, Int.cast_zero, Complex.ofReal_zero,
    zero_add, Complex.exp_zero, mul_one]
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
  cases b
  · simp only [cuspSignedRowEquiv, Equiv.ofBijective, Equiv.coe_fn_mk,
      signedCuspBottomRow, Bool.false_eq_true, ↓reduceIte, Pi.neg_apply, Int.cast_neg,
      neg_mul, ← neg_add, Complex.normSq_neg, cuspBottomRow]
  · rfl

lemma summable_norm_primitive_height {s : ℂ} (hs : 1 < s.re) (z : UpperHalfPlane) :
    Summable fun v : PrimitiveRow =>
      ‖(((z.im / Complex.normSq ((v.1 0 : ℂ) * z + v.1 1)) : ℝ) : ℂ) ^ s‖ := by
  have hall := (summable_poincare_height z hs).subtype
    (fun v => v ∈ EisensteinSeries.gammaSet 1 1 0)
  apply hall.congr
  intro v
  exact (Complex.norm_cpow_eq_rpow_re_of_nonneg
    (div_nonneg z.im_pos.le (Complex.normSq_nonneg _)) (by linarith : s.re ≠ 0)).symm

lemma primitive_height_sum_eq_two_cusp {s : ℂ} (hs : 1 < s.re) (z : UpperHalfPlane) :
    (∑' v : PrimitiveRow,
      (((z.im / Complex.normSq ((v.1 0 : ℂ) * z + v.1 1)) : ℝ) : ℂ) ^ s) =
      2 * complexPoincareSeries 0 0 s z := by
  have hsum := (summable_norm_primitive_height hs z).of_norm
  rw [← cuspSignedRowEquiv.tsum_eq]
  have heqsum := cuspSignedRowEquiv.summable_iff.mpr hsum
  simp only [Function.comp_def] at heqsum
  rw [heqsum.tsum_prod]
  simp_rw [signedCuspBottomRow_height, tsum_bool, ← two_mul]
  exact tsum_mul_left


/-- Splitting integer rows by their nonnegative gcd extracts a homogeneous radial factor. -/
theorem tsum_integer_rows_eq_factor_mul_primitive
    (f : (Fin 2 → ℤ) → ℂ) (c : ℕ → ℂ) (hf : Summable f)
    (hc : c 0 = 0)
    (hscale : ∀ (n : ℕ) (v : Fin 2 → ℤ), f (n • v) = c n * f v) :
    ∑' v : Fin 2 → ℤ, f v = (∑' n : ℕ, c n) *
      ∑' v : gammaSet 1 1 0, f v := by
  rw [← gammaSetDivGcdSigmaEquiv.symm.tsum_eq]
  have hsum : Summable (fun v : Σ n : ℕ, gammaSet 1 n 0 => f v.2) :=
    gammaSetDivGcdSigmaEquiv.symm.summable_iff.mpr hf
  change (∑' v : Σ n : ℕ, gammaSet 1 n 0, f v.2) = _
  rw [hsum.tsum_sigma, ← tsum_mul_right]
  refine tsum_congr fun n => ?_
  have hrow (v : gammaSet 1 n 0) : f v = c n * f (divIntMap n v) := by
    nth_rw 1 [gammaSet_eq_gcd_mul_divIntMap v.2]
    rw [hscale]
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [hrow, hc, zero_mul, tsum_zero]
  · let : NeZero n := ⟨hn⟩
    simp_rw [hrow, tsum_mul_left]
    congr 1
    exact (gammaSetDivGcdEquiv n).tsum_eq (fun v => f v)

/-- The actual lattice Dirichlet series equals its primitive-row series times
`ζ(2s)` in the region of absolute convergence. -/
theorem tsum_latticeDirichletTerm_eq_riemannZeta_mul_primitive
    (z : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    ∑' v : Fin 2 → ℤ, latticeDirichletTerm z s v =
      riemannZeta (2 * s) *
        ∑' v : gammaSet 1 1 0, latticeDirichletTerm z s v := by
  have hs2 : 1 < (2 * s).re := by norm_num [mul_re]; linarith
  rw [tsum_integer_rows_eq_factor_mul_primitive (latticeDirichletTerm z s)
    (fun n : ℕ => 1 / (n : ℂ) ^ (2 * s)) (summable_latticeDirichletTerm z hs)
    (by simp [Complex.zero_cpow (Complex.ne_zero_of_one_lt_re hs2)])
    (latticeDirichletTerm_nsmul z s), ← zeta_eq_tsum_one_div_nat_cpow hs2]


/-- The scalar Dirichlet series indexed by genuinely nonzero lattice rows. -/
def latticeDirichletSeries (z : UpperHalfPlane) (s : ℂ) : ℂ :=
  ∑' v : {v : Fin 2 → ℤ // v ≠ 0}, latticeDirichletTerm z s v

theorem summable_norm_latticeDirichletSeries (z : UpperHalfPlane) {s : ℂ}
    (hs : 1 < s.re) :
    Summable fun v : {v : Fin 2 → ℤ // v ≠ 0} => ‖latticeDirichletTerm z s v‖ :=
  (summable_norm_latticeDirichletTerm z hs).subtype _

theorem hasSum_latticeDirichletSeries (z : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun v : {v : Fin 2 → ℤ // v ≠ 0} => latticeDirichletTerm z s v)
      (latticeDirichletSeries z s) :=
  (summable_norm_latticeDirichletSeries z hs).of_norm.hasSum

/-- Removing the zero row is harmless because its summand is proved zero in the
convergence region, not because a divergent totalized sum is assigned zero. -/
theorem latticeDirichletSeries_eq_tsum_all (z : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    latticeDirichletSeries z s = ∑' v : Fin 2 → ℤ, latticeDirichletTerm z s v := by
  apply tsum_subtype_eq_of_support_subset
  intro v hv
  change v ≠ 0
  intro hv0
  subst v
  exact hv (latticeDirichletTerm_zero z (Complex.ne_zero_of_one_lt_re hs))

/-- Primitive lattice rows count both signs of each scalar cusp coset. -/
theorem tsum_primitive_latticeDirichletTerm_eq_two_poincare
    (z : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    (∑' v : PrimitiveRow, latticeDirichletTerm z s v) =
      2 * complexPoincareSeries 0 0 s z := by
  simp_rw [latticeDirichletTerm_eq_height]
  exact primitive_height_sum_eq_two_cusp hs z

/-- The actual scalar Poincaré series and nonzero lattice Dirichlet series have
the exact `2 ζ(2s)` normalization throughout their absolute convergence region. -/
theorem latticeDirichletSeries_eq_two_zeta_mul_poincare
    (z : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    latticeDirichletSeries z s =
      2 * riemannZeta (2 * s) * complexPoincareSeries 0 0 s z := by
  rw [latticeDirichletSeries_eq_tsum_all z hs,
    tsum_latticeDirichletTerm_eq_riemannZeta_mul_primitive z hs,
    tsum_primitive_latticeDirichletTerm_eq_two_poincare z hs]
  ring

/-- The normalization identity expressed as a convergent-sum certificate. -/
theorem hasSum_latticeDirichletTerm_two_zeta_mul_poincare
    (z : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun v : {v : Fin 2 → ℤ // v ≠ 0} => latticeDirichletTerm z s v)
      (2 * riemannZeta (2 * s) * complexPoincareSeries 0 0 s z) := by
  rw [← latticeDirichletSeries_eq_two_zeta_mul_poincare z hs]
  exact hasSum_latticeDirichletSeries z hs

theorem latticeDirichletSeries_smul (z : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re)
    (g : SL(2, ℤ)) : latticeDirichletSeries (g • z) s = latticeDirichletSeries z s := by
  rw [latticeDirichletSeries_eq_two_zeta_mul_poincare (g • z) hs,
    latticeDirichletSeries_eq_two_zeta_mul_poincare z hs, complexPoincareSeries_smul]

end

end GapFamily.Analytic
