import GapFamily.Analytic.Poincare.Fourier.PoincareFourierKernel
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierCoordinate
import GapFamily.Analytic.Poincare.PoincareResidueRow
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierMatrix
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierPrimitive

/-! Actual fixed-residue Poincaré Fourier integrals unfold to the ordinary real line. -/
noncomputable section
namespace GapFamily.Analytic.PoincareFourierUnfold
open Set MeasureTheory UpperHalfPlane PoincareFourier
open scoped MatrixGroups Topology

/-- A literal matrix Fourier integrand is the centered kernel with its exact
rational residue phases. Every complex exponent is admitted in this identity. -/
theorem fourierMatrix_eq_phase_kernel (j J : ℤ) (s : ℂ) (γ : SL(2, ℤ))
    (hc : 0 < (γ 1 0 : ℝ)) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    cuspFourierMode (-j) x * complexPointSeed 0 J s (γ • rowPoint y hy x) =
      (cuspFourierMode j ((γ 1 1 : ℝ) / (γ 1 0 : ℝ)) *
        cuspFourierMode J ((γ 0 0 : ℝ) / (γ 1 0 : ℝ))) *
          fourierKernel (γ 1 0 : ℝ) y j J s (x + (γ 1 1 : ℝ) / (γ 1 0 : ℝ)) := by
  have hcZ : γ 1 0 ≠ 0 := by exact_mod_cast hc.ne'
  have hn := normSq_affine_row (γ 1 0 : ℝ) (γ 1 1 : ℝ) x y hc.ne'
  have hi := re_inv_affine_row (γ 1 0 : ℝ) (γ 1 1 : ℝ) x y hc hy
  push_cast at hn hi
  rw [complexPointSeed_zero_smul_eq_height_phase J s γ (rowPoint y hy x) hcZ]
  change cuspFourierMode (-j) x *
    (((y / Complex.normSq ((γ 1 0 : ℂ) * Complex.mk x y + (γ 1 1 : ℂ)) : ℝ) : ℂ) ^ s *
      cuspFourierMode J ((γ 0 0 : ℝ) / (γ 1 0 : ℝ)) *
      cuspFourierMode J (-(1 / ((γ 1 0 : ℂ) *
        ((γ 1 0 : ℂ) * Complex.mk x y + (γ 1 1 : ℂ)))).re)) = _
  rw [hn, hi, cuspFourierMode_neg_argument,
    cuspFourierMode_shift_split j x ((γ 1 1 : ℝ) / (γ 1 0 : ℝ))]
  unfold fourierKernel
  ring

/-- The actual primitive matrix associated to a residue and translate gives
exactly the existing Kloosterman phase times a translate of the actual kernel. -/
theorem primitiveFourierTerm_residueRow_eq (j J : ℤ) (s : ℂ) (n : ℕ)
    (u : (ZMod (n + 1))ˣ) (k : ℤ) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    primitiveFourierTerm j J s y hy (residueRow n u k) x =
      kloostermanPhase j J n u *
        fourierKernel (n + 1 : ℕ) y j J s
          (x + ((u : ZMod (n + 1)).val : ℝ) / (n + 1 : ℕ) + (k : ℝ)) := by
  have hc : 0 < (primitiveMatrix (residueRow n u k) 1 0 : ℝ) := by
    rw [primitiveMatrix_residueRow_bottomLeft]
    positivity
  rw [primitiveFourierTerm, primitiveSpinTerm, fourierMatrix_eq_phase_kernel j J s _ hc]
  simp only [primitiveMatrix_residueRow_bottomLeft, Int.cast_natCast]
  rw [residueRow_fourier_phase_eq_kloostermanPhase,
    primitiveMatrix_residueRow_bottomRight_div, ← add_assoc]

/-- Integrated norms over all integer translates of this actual matrix family
are summable. This proves the convergence needed by the following unfolding. -/
theorem summable_integral_norm_residueRow (j J : ℤ) {s : ℂ} (hs : 1 / 2 < s.re)
    (n : ℕ) (u : (ZMod (n + 1))ˣ) (y : ℝ) (hy : 0 < y) :
    Summable (fun k : ℤ => ∫ x in (0 : ℝ)..1,
      ‖primitiveFourierTerm j J s y hy (residueRow n u k) x‖) := by
  simpa only [primitiveFourierTerm_residueRow_eq, norm_mul, norm_kloostermanPhase, one_mul] using
    summable_intervalIntegral_norm_fourierKernel (by positivity : 0 < ((n + 1 : ℕ) : ℝ))
      hy j J hs (((u : ZMod (n + 1)).val : ℝ) / (n + 1 : ℕ))

/-- For a fixed positive denominator and unit residue, the actual Poincaré
Fourier integrals form a genuine convergent sum over the entire real line. -/
theorem hasSum_integral_residueRow (j J : ℤ) {s : ℂ} (hs : 1 / 2 < s.re)
    (n : ℕ) (u : (ZMod (n + 1))ˣ) (y : ℝ) (hy : 0 < y) :
    HasSum (fun k : ℤ => ∫ x in (0 : ℝ)..1,
      primitiveFourierTerm j J s y hy (residueRow n u k) x)
      (kloostermanPhase j J n u * ∫ t : ℝ, fourierKernel (n + 1 : ℕ) y j J s t) := by
  have h := (hasSum_intervalIntegral_fourierKernel
    (by positivity : 0 < ((n + 1 : ℕ) : ℝ)) hy j J hs
      (((u : ZMod (n + 1)).val : ℝ) / (n + 1 : ℕ))).mul_left (kloostermanPhase j J n u)
  simpa only [primitiveFourierTerm_residueRow_eq, intervalIntegral.integral_const_mul] using h

/-- The fixed-residue ordinary integral sum has the literal full-line value. -/
theorem integral_residueRow_tsum_eq (j J : ℤ) {s : ℂ} (hs : 1 / 2 < s.re)
    (n : ℕ) (u : (ZMod (n + 1))ˣ) (y : ℝ) (hy : 0 < y) :
    (∑' k : ℤ, ∫ x in (0 : ℝ)..1,
      primitiveFourierTerm j J s y hy (residueRow n u k) x) =
      kloostermanPhase j J n u * ∫ t : ℝ, fourierKernel (n + 1 : ℕ) y j J s t :=
  (hasSum_integral_residueRow j J hs n u y hy).tsum_eq

end GapFamily.Analytic.PoincareFourierUnfold
