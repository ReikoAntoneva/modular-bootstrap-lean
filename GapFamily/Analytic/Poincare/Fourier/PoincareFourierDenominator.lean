import GapFamily.Analytic.Poincare.Fourier.PoincareFourierUnfold

/-! Actual ordinary Fourier integrals at one positive denominator assemble into
the finite Kloosterman sum times the full-line kernel integral. -/

noncomputable section
namespace GapFamily.Analytic.PoincareFourierRegroup
open Set MeasureTheory PoincareFourier PoincareFourierUnfold
open scoped Topology

/-- Integrated pointwise norms are summable over every unit residue and integer
translate at one positive denominator, including denominator one. -/
theorem summable_integral_norm_denominator (j J : ℤ) {s : ℂ}
    (hs : 1 / 2 < s.re) (n : ℕ) (y : ℝ) (hy : 0 < y) :
    Summable (fun p : (ZMod (n + 1))ˣ × ℤ => ∫ x in (0 : ℝ)..1,
      ‖primitiveFourierTerm j J s y hy (residueRow n p.1 p.2) x‖) := by
  apply (summable_prod_of_nonneg (fun p : (ZMod (n + 1))ˣ × ℤ =>
    intervalIntegral.integral_nonneg_of_forall zero_le_one (fun x => norm_nonneg _))).mpr
  refine ⟨fun u => summable_integral_norm_residueRow j J hs n u y hy, ?_⟩
  apply summable_of_hasFiniteSupport
  exact Set.toFinite _

/-- The actual ordinary Fourier integrals are absolutely summable over the
unit residues and integer translates at one positive denominator. -/
theorem summable_norm_integral_denominator (j J : ℤ) {s : ℂ}
    (hs : 1 / 2 < s.re) (n : ℕ) (y : ℝ) (hy : 0 < y) :
    Summable (fun p : (ZMod (n + 1))ˣ × ℤ =>
      ‖∫ x in (0 : ℝ)..1,
        primitiveFourierTerm j J s y hy (residueRow n p.1 p.2) x‖) :=
  (summable_integral_norm_denominator j J hs n y hy).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun _ => intervalIntegral.norm_integral_le_integral_norm zero_le_one)

/-- The convergent family at a fixed positive denominator has exactly the
existing finite Kloosterman sum times the actual full-line kernel integral. -/
theorem hasSum_integral_denominator (j J : ℤ) {s : ℂ}
    (hs : 1 / 2 < s.re) (n : ℕ) (y : ℝ) (hy : 0 < y) :
    HasSum (fun p : (ZMod (n + 1))ˣ × ℤ => ∫ x in (0 : ℝ)..1,
      primitiveFourierTerm j J s y hy (residueRow n p.1 p.2) x)
      (kloostermanSum j J n * ∫ t : ℝ, fourierKernel (n + 1 : ℕ) y j J s t) := by
  have hsum := (summable_norm_integral_denominator j J hs n y hy).of_norm
  convert hsum.hasSum using 1
  rw [hsum.tsum_prod]
  simp_rw [integral_residueRow_tsum_eq j J hs n _ y hy]
  rw [tsum_fintype, ← Finset.sum_mul]
  rfl

end GapFamily.Analytic.PoincareFourierRegroup
