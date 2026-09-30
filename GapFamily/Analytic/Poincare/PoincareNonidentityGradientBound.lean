import GapFamily.Analytic.Poincare.Seed.PoincareSeriesDifferentiable
import GapFamily.Analytic.Cusp.CuspHeightFundamentalDomain

/-!
# Uniform fundamental-domain bounds for the nonidentity derivative series

The majorant is the established summable integer-row height majorant multiplied
by the bounded translated-seed gradient factor. The derivative series is the
ordinary norm-summable series of the actual quotient-term derivatives.
-/

noncomputable section

namespace GapFamily.Analytic.PoincareNonidentityGradientBound

open Set PoincareTermGradient PoincareSeriesDifferentiable
open scoped Topology MatrixGroups

/-- Every nonidentity cusp image has uniformly bounded height on the closed domain. -/
theorem nonidentity_height_le_two
    (q : {q : CuspCoset // q ≠ identityCuspCoset})
    {τ : UpperHalfPlane} (hτ : τ ∈ ModularGroup.fd) :
    (q.val.out • τ).im ≤ 2 := by
  apply (nonidentity_cusp_height_le q.val q.property hτ).trans
  have hn := one_le_norm_int_pair _ (cuspBottomRow_ne_zero q.val)
  exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hn)).mpr (by nlinarith)

/-- One actual summable row majorant controls every nonidentity frame derivative. -/
theorem exists_nonidentity_frame_majorant (J : ℤ) {s : ℂ} (hs : 2 < s.re) :
    ∃ u : {q : CuspCoset // q ≠ identityCuspCoset} → ℝ,
      Summable u ∧ (∀ q, 0 ≤ u q) ∧
      ∀ (q : {q : CuspCoset // q ≠ identityCuspCoset})
        (τ : UpperHalfPlane), τ ∈ ModularGroup.fd → ∀ v : ℂ,
        τ.im * ‖fderiv ℝ (term J s q.val) (τ : ℂ) v‖ ≤ u q * ‖v‖ := by
  let C : ℝ := ‖s‖ + 4 * Real.pi * |(J : ℝ)|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let u : {q : CuspCoset // q ≠ identityCuspCoset} → ℝ :=
    fun q => C * ((2 : ℝ) ^ s.re * ‖cuspBottomRow q.val‖ ^ (-s.re))
  refine ⟨u, (summable_nonidentity_cusp_height_majorant hs).mul_left C,
    fun q => mul_nonneg hC (mul_nonneg (by positivity) (by positivity)), ?_⟩
  intro q τ hτ v
  have hheight := nonidentity_height_le_two q hτ
  have hfactor : ‖s‖ + 2 * Real.pi * |(J : ℝ)| * (q.val.out • τ).im ≤ C := by
    have hp : 0 ≤ 2 * Real.pi * |(J : ℝ)| := by positivity
    have hm := mul_le_mul_of_nonneg_left hheight hp
    calc
      _ ≤ ‖s‖ + 2 * Real.pi * |(J : ℝ)| * 2 := add_le_add le_rfl hm
      _ = C := by dsimp [C]; ring
  have hrow := nonidentity_cusp_height_rpow_le q.val q.property hτ (by linarith : 0 ≤ s.re)
  have hb : (‖s‖ + 2 * Real.pi * |(J : ℝ)| * (q.val.out • τ).im) *
      (q.val.out • τ).im ^ s.re ≤ u q := by
    exact mul_le_mul hfactor hrow (Real.rpow_nonneg (q.val.out • τ).im_pos.le _) hC
  exact (translatedSeed_frame_bound J s q.val.out τ v).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg v))

/-- The actual nonidentity derivative operators have a norm-summable series. -/
theorem summable_norm_nonidentity_fderiv_term (J : ℤ) {s : ℂ}
    (hs : 1 < s.re) (τ : UpperHalfPlane) :
    Summable (fun q : {q : CuspCoset // q ≠ identityCuspCoset} =>
      ‖fderiv ℝ (term J s q.val) (τ : ℂ)‖) :=
  (summable_norm_fderiv_term J hs τ).subtype _

/-- The actual derivative series evaluated in any fixed direction converges absolutely. -/
theorem summable_norm_nonidentity_directional_term (J : ℤ) {s : ℂ}
    (hs : 1 < s.re) (τ : UpperHalfPlane) (v : ℂ) :
    Summable (fun q : {q : CuspCoset // q ≠ identityCuspCoset} =>
      ‖fderiv ℝ (term J s q.val) (τ : ℂ) v‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun q => (fderiv ℝ (term J s q.val) (τ : ℂ)).le_opNorm v)
    ((summable_norm_nonidentity_fderiv_term J hs τ).mul_right ‖v‖)

/-- The norm-summable nonidentity operator series has a uniform hyperbolic-frame bound. -/
theorem exists_nonidentity_fderiv_tsum_frame_bound (J : ℤ) {s : ℂ}
    (hs : 2 < s.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (τ : UpperHalfPlane), τ ∈ ModularGroup.fd → ∀ v : ℂ,
      τ.im * ‖(∑' q : {q : CuspCoset // q ≠ identityCuspCoset},
        fderiv ℝ (term J s q.val) (τ : ℂ)) v‖ ≤ B * ‖v‖ := by
  obtain ⟨u, hu, hu0, hub⟩ := exists_nonidentity_frame_majorant J hs
  refine ⟨∑' q, u q, tsum_nonneg hu0, ?_⟩
  intro τ hτ v
  have hs₁ : 1 < s.re := by linarith
  have hD := (summable_norm_nonidentity_fderiv_term J hs₁ τ).of_norm
  have heval := (summable_norm_nonidentity_directional_term J hs₁ τ v).of_norm
  have hb : ‖∑' q : {q : CuspCoset // q ≠ identityCuspCoset},
      fderiv ℝ (term J s q.val) (τ : ℂ) v‖ ≤ (∑' q, u q) * ‖v‖ / τ.im := by
    apply heval.hasSum.norm_le_of_bounded ((hu.hasSum.mul_right ‖v‖).div_const τ.im)
    intro q
    exact (le_div_iff₀ τ.im_pos).mpr (by simpa only [mul_comm] using hub q τ hτ v)
  have happly : (∑' q : {q : CuspCoset // q ≠ identityCuspCoset},
      fderiv ℝ (term J s q.val) (τ : ℂ)) v =
      ∑' q : {q : CuspCoset // q ≠ identityCuspCoset},
        fderiv ℝ (term J s q.val) (τ : ℂ) v := by
    simpa only [ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply ℝ ℂ v).map_tsum hD
  rw [happly]
  simpa only [mul_comm] using (le_div_iff₀ τ.im_pos).mp hb

end GapFamily.Analytic.PoincareNonidentityGradientBound
