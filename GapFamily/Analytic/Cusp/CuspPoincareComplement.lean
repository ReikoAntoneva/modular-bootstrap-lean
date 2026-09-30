import GapFamily.Analytic.Poincare.PoincareAnalytic
import GapFamily.Analytic.Cusp.Fourier.CuspFourierCutoffProfile

/-! The actual cusp-coset series of the complementary cutoff seed. -/
noncomputable section
namespace GapFamily.Analytic.PoincareComplement
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- The literal complementary-cutoff zero-energy point seed. -/
def pointSeed (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) : ℂ :=
  ((1 - CuspFourierCutoff.cutoff τ.im : ℝ) : ℂ) * complexPointSeed 0 J s τ

/-- The point seed is invariant under the actual cusp subgroup, including signs. -/
theorem pointSeed_cusp (J : ℤ) (s : ℂ) (g : SL(2, ℤ))
    (hg : g ∈ cuspInfinity) (τ : UpperHalfPlane) :
    pointSeed J s (g • τ) = pointSeed J s τ := by
  obtain ⟨n, hn⟩ := ModularGroup.exists_eq_T_zpow_of_c_eq_zero hg
  rw [hn]
  simp only [pointSeed, ModularGroup.im_T_zpow_smul, complexPointSeed_translation]

/-- The multiplier and the point seed both descend to the true cusp quotient. -/
theorem pointSeed_coset_eq (J : ℤ) (s : ℂ) (τ : UpperHalfPlane)
    {g h : SL(2, ℤ)} (hgh : QuotientGroup.rightRel cuspInfinity g h) :
    pointSeed J s (g • τ) = pointSeed J s (h • τ) := by
  have hmem : h * g⁻¹ ∈ cuspInfinity := QuotientGroup.rightRel_apply.mp hgh
  have h := pointSeed_cusp J s (h * g⁻¹) hmem (g • τ)
  simpa [mul_smul] using h.symm

/-- An actual quotient term; no chosen representative is used in its definition. -/
def term (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) (q : CuspCoset) : ℂ :=
  Quotient.lift (fun g : SL(2, ℤ) => pointSeed J s (g • τ))
    (fun _ _ h => pointSeed_coset_eq J s τ h) q

@[simp] theorem term_mk (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    term J s τ (Quotient.mk _ g) = pointSeed J s (g • τ) := rfl

theorem term_out (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) (q : CuspCoset) :
    term J s τ q = pointSeed J s (q.out • τ) := by
  conv_lhs => rw [← q.out_eq]
  rfl

@[simp] theorem term_identity (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) :
    term J s τ identityCuspCoset = pointSeed J s τ := by
  simp [identityCuspCoset]

theorem term_smul (J : ℤ) (s : ℂ) (τ : UpperHalfPlane)
    (g : SL(2, ℤ)) (q : CuspCoset) :
    term J s (g • τ) q = term J s τ (cuspRightEquiv g q) := by
  induction q using Quotient.inductionOn with | h h =>
    simp [cuspRightEquiv, mul_smul]

/-- The real complementary cutoff has norm at most one. -/
theorem norm_pointSeed_le (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) :
    ‖pointSeed J s τ‖ ≤ ‖complexPointSeed 0 J s τ‖ := by
  have h0 : 0 ≤ CuspFourierCutoff.cutoff τ.im := Real.smoothTransition.nonneg _
  have h1 : CuspFourierCutoff.cutoff τ.im ≤ 1 := Real.smoothTransition.le_one _
  rw [pointSeed, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr h1)]
  exact (mul_le_mul_of_nonneg_right (by linarith : 1 - CuspFourierCutoff.cutoff τ.im ≤ 1)
    (norm_nonneg _)).trans_eq (one_mul _)

theorem norm_term_le (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) (q : CuspCoset) :
    ‖term J s τ q‖ ≤ ‖complexPoincareTerm 0 J s τ q‖ := by
  rw [term_out, complexPoincareTerm_out]
  exact norm_pointSeed_le J s (q.out • τ)

/-- Absolute convergence in the ordinary cusp-series half-plane. -/
theorem summable_norm_term (J : ℤ) {s : ℂ} (hs : 1 < s.re) (τ : UpperHalfPlane) :
    Summable (fun q : CuspCoset => ‖term J s τ q‖) :=
  (summable_norm_complexPoincareTerm 0 J hs τ).of_nonneg_of_le
    (fun _ => norm_nonneg _) (norm_term_le J s τ)

/-- The global automorphic complementary-cutoff series. -/
def series (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) : ℂ := ∑' q : CuspCoset, term J s τ q

theorem hasSum_term (J : ℤ) {s : ℂ} (hs : 1 < s.re) (τ : UpperHalfPlane) :
    HasSum (term J s τ) (series J s τ) := (summable_norm_term J hs τ).of_norm.hasSum

/-- Reindexing is literal right multiplication on the true cusp quotient.
The preceding norm theorem supplies actual convergence whenever Re s>1. -/
theorem series_smul (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    series J s (g • τ) = series J s τ := by
  simp only [series, term_smul]
  exact (cuspRightEquiv g).tsum_eq _

/-- The convergent series has the same actual sum at every modular translate. -/
theorem hasSum_term_smul (J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    HasSum (term J s (g • τ)) (series J s τ) := by
  rw [← series_smul J s τ g]
  exact hasSum_term J hs (g • τ)

end GapFamily.Analytic.PoincareComplement
