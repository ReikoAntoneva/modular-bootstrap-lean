import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationPairing
import GapFamily.Analytic.Modular.Geometry.ModularSeamCoordinateMeasure

/-!
# Euclidean source testing for actual modular periodization

The inverse height square is applied only through a seed supported compactly
inside the upper half-plane. The actual hyperbolic measure identity then gives
the ordinary Euclidean source pairing, with the test in the first inner slot.
-/

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff Topology ComplexConjugate

/-- The Euclidean source test corresponding to an unweighted hyperbolic seed. -/
def upperSourceTestFunction (ψ : ℂ → ℂ) (z : ℂ) : ℂ := ψ z / (z.im : ℂ) ^ 2

/-- Division by height squared is smooth wherever the seed can be nonzero;
the zero germ supplies global smoothness at every remaining point. -/
theorem contDiff_upperSourceTestFunction {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    ContDiff ℝ ∞ (upperSourceTestFunction ψ) := by
  change ContDiff ℝ ∞ (fun z : ℂ => ψ z / (z.im : ℂ) ^ 2)
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport ψ
  · have hy : 0 < z.im := hs hz
    have hh : ContDiffAt ℝ ∞ (fun w : ℂ => (w.im ^ 2)⁻¹) z :=
      (Complex.imCLM.contDiff.contDiffAt.pow 2).inv (pow_ne_zero 2 hy.ne')
    have hprod : ContDiffAt ℝ ∞ (fun w : ℂ => (w.im ^ 2)⁻¹ • ψ w) z :=
      hh.smul hψ.contDiffAt
    simpa only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow,
      div_eq_mul_inv, mul_comm] using hprod
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
    simp [hw]

/-- Weighting preserves the seed's closed support. -/
theorem tsupport_upperSourceTestFunction_subset (ψ : ℂ → ℂ) :
    tsupport (upperSourceTestFunction ψ) ⊆ tsupport ψ := by
  change tsupport (fun z : ℂ => ψ z / (z.im : ℂ) ^ 2) ⊆ tsupport ψ
  simp only [div_eq_mul_inv]
  exact tsupport_mul_subset_left

/-- A weighted compact seed still has compact support. -/
theorem hasCompactSupport_upperSourceTestFunction {ψ : ℂ → ℂ}
    (hc : HasCompactSupport ψ) : HasCompactSupport (upperSourceTestFunction ψ) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_upperSourceTestFunction_subset ψ)

/-- The weighted test paired with a genuine core is an ordinary Euclidean integrable function. -/
theorem integrable_upperSourceTestFunction_mul_core (F : smoothCore) {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    Integrable (fun z : ℂ => star (upperSourceTestFunction ψ z) * F.val z) volume := by
  have hprod := contDiff_conjCore_mul_upperSeed F
    (contDiff_upperSourceTestFunction hψ hs)
    ((tsupport_upperSourceTestFunction_subset ψ).trans hs)
  have hi : Integrable (fun z : ℂ => star (F.val z) * upperSourceTestFunction ψ z) volume :=
    hprod.continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_upperSourceTestFunction hc).mul_left
  have hconj := Complex.conjCLE.toContinuousLinearMap.integrable_comp hi
  simpa only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul,
    ← Complex.star_def, star_star, mul_comm] using hconj

/-- Actual hyperbolic density cancels the source test's inverse height square. -/
theorem integral_upperSourceTestFunction_mul_core (F : smoothCore) {ψ : ℂ → ℂ}
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    (∫ z : ℂ, star (upperSourceTestFunction ψ z) * F.val z) =
      ∫ τ : UpperHalfPlane, star (ψ τ) * F.val τ ∂volume := by
  let g : ℂ → ℂ := fun z => star (upperSourceTestFunction ψ z) * F.val z
  have hgzero (z : ℂ) (hz : z ∉ upperHalfPlaneSet) : g z = 0 := by
    have hψzero : ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hs h))
    simp only [g, upperSourceTestFunction, hψzero, zero_div, star_zero, zero_mul]
  change (∫ z : ℂ, g z) = _
  calc
    _ = ∫ z in upperHalfPlaneSet, g z :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hgzero).symm
    _ = ∫ τ : UpperHalfPlane in UpperHalfPlane.coe ⁻¹' upperHalfPlaneSet,
        τ.im ^ 2 • g τ :=
      setIntegral_eq_upperHalfPlane_im_sq_smul isOpen_upperHalfPlaneSet.measurableSet
        (fun _ hz => hz) g
    _ = ∫ τ : UpperHalfPlane, τ.im ^ 2 • g τ := by
      rw [show UpperHalfPlane.coe ⁻¹' upperHalfPlaneSet = (univ : Set UpperHalfPlane) by
        ext τ
        simp only [mem_preimage, mem_univ, iff_true]
        exact τ.im_pos, Measure.restrict_univ]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with τ
      have hy : (τ.im : ℂ) ≠ 0 := by exact_mod_cast τ.im_pos.ne'
      simp only [g, upperSourceTestFunction, Complex.real_smul, star_div₀, star_pow,
        Complex.star_def, Complex.conj_ofReal, Complex.ofReal_pow]
      change (τ.im : ℂ) ^ 2 *
        (conj (ψ τ) / (τ.im : ℂ) ^ 2 * F.val τ) = conj (ψ τ) * F.val τ
      field_simp [hy]

/-- The actual Hilbert value pairing becomes the test-first Euclidean source integral. -/
theorem inner_periodizedUpperCore_value_eq_euclidean (F : smoothCore) {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    inner ℂ (value (periodizedUpperCore ψ hψ hc hs)) (value F) =
      ∫ z : ℂ, star (upperSourceTestFunction ψ z) * F.val z := by
  rw [integral_upperSourceTestFunction_mul_core F hs]
  calc
    _ = conj (inner ℂ (value F) (value (periodizedUpperCore ψ hψ hc hs))) :=
      (inner_conj_symm _ _).symm
    _ = conj (∫ τ : UpperHalfPlane, star (F.val τ) * ψ τ ∂volume) := by
      rw [inner_value_periodizedUpperCore F hψ hc hs]
    _ = _ := by
      rw [← integral_conj]
      apply integral_congr_ae
      filter_upwards with τ
      simp only [map_mul, ← Complex.star_def, star_star, mul_comm]

end GapFamily.Analytic
