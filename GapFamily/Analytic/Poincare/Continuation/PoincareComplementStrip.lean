import GapFamily.Analytic.Cusp.CuspPoincareComplementFD

noncomputable section
namespace GapFamily.Analytic.PoincareComplement
open Set Filter MeasureTheory
open scoped Topology

/-- Every nonidentity cusp height is strictly below two throughout the open
height-half strip, with no real-coordinate restriction. -/
theorem nonidentity_height_lt_two_of_half_lt_im (q : CuspCoset)
    (hq : q ≠ identityCuspCoset) {τ : UpperHalfPlane} (hτ : 1 / 2 < τ.im) :
    (q.out • τ).im < 2 := by
  have hmul := nonidentity_cusp_height_mul_im_le_one q hq τ
  nlinarith [(q.out • τ).im_pos]

/-- The actual complementary multiplier is one on each nonidentity orbit
above input height one half. -/
theorem term_eq_raw_of_half_lt_im (J : ℤ) (s : ℂ) (q : CuspCoset)
    (hq : q ≠ identityCuspCoset) {τ : UpperHalfPlane} (hτ : 1 / 2 < τ.im) :
    term J s τ q = complexPoincareTerm 0 J s τ q := by
  rw [term_out, pointSeed, complexPoincareTerm_out,
    CuspFourierCutoff.cutoff_eq_zero
      (nonidentity_height_lt_two_of_half_lt_im q hq hτ).le]
  simp

/-- The actual global automorphic complement equals the literal cutoff subtraction
on the whole open strip, not merely on the fundamental domain. -/
theorem series_eq_residual_of_half_lt_im (J : ℤ) {s : ℂ} (hs : 1 < s.re)
    {τ : UpperHalfPlane} (hτ : 1 / 2 < τ.im) :
    series J s τ = complexPoincareSeries 0 J s τ -
      (CuspFourierCutoff.cutoff τ.im : ℂ) * complexPointSeed 0 J s τ := by
  rw [series_direct_term J hs τ,
    complexPoincareSeries_residual_split 0 J hs τ (CuspFourierCutoff.cutoff τ.im : ℂ)]
  have ht : (∑' q : {q : CuspCoset // q ≠ identityCuspCoset}, term J s τ q) =
      ∑' q : {q : CuspCoset // q ≠ identityCuspCoset}, complexPoincareTerm 0 J s τ q := by
    apply tsum_congr
    intro q
    exact term_eq_raw_of_half_lt_im J s q q.property hτ
  rw [ht, pointSeed]
  push_cast
  ring

/-- The same strip identity for the literal ambient representative. -/
theorem series_ofComplex_eq_residual_of_half_lt_im (J : ℤ) {s : ℂ}
    (hs : 1 < s.re) {z : ℂ} (hz : 1 / 2 < z.im) :
    series J s (UpperHalfPlane.ofComplex z) =
      complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z) -
        (CuspFourierCutoff.cutoff z.im : ℂ) *
          complexPointSeed 0 J s (UpperHalfPlane.ofComplex z) := by
  have hy : 0 < z.im := by linarith
  simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hy, UpperHalfPlane.im] using
    series_eq_residual_of_half_lt_im J hs (τ := ⟨z, hy⟩) hz

/-- The open-strip identity is an actual neighborhood equality, ready for ordinary derivatives. -/
theorem series_ofComplex_germ_residual_of_half_lt_im (J : ℤ) {s : ℂ}
    (hs : 1 < s.re) {z : ℂ} (hz : 1 / 2 < z.im) :
    (fun w : ℂ => series J s (UpperHalfPlane.ofComplex w)) =ᶠ[𝓝 z]
      (fun w : ℂ => complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex w) -
        (CuspFourierCutoff.cutoff w.im : ℂ) *
          complexPointSeed 0 J s (UpperHalfPlane.ofComplex w)) := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with w hw
  exact series_ofComplex_eq_residual_of_half_lt_im J hs hw

end GapFamily.Analytic.PoincareComplement
