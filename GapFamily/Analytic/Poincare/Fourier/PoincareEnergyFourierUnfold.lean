import GapFamily.Analytic.Poincare.Fourier.PoincareEnergyFourierKernel
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierUnfold

/-!
Actual energy-correction matrix terms unfold into the ordinary real-line energy
kernel. At a fixed positive denominator the arithmetic factor is the existing
finite Kloosterman sum, with genuine integrated-norm convergence.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier

open Set MeasureTheory UpperHalfPlane PoincareFourier PoincareFourierUnfold
open scoped MatrixGroups Topology

/-- Literal zero-energy subtraction factors through the actual zero-energy seed. -/
theorem complexPointSeed_sub_zero_energy_eq_mul (E : ℂ) (J : ℤ) (s : ℂ)
    (z : UpperHalfPlane) :
    complexPointSeed E J s z - complexPointSeed 0 J s z =
      complexPointSeed 0 J s z *
        (Complex.exp (-2 * (Real.pi : ℂ) * E * z.im) - 1) := by
  rw [complexPointSeed_sub_zero_energy]
  simp only [complexPointSeed, mul_zero, zero_mul, zero_add]

/-- The actual primitive-row Fourier integrand with its zero-energy subtraction. -/
def primitiveEnergyFourierTerm (y : ℝ) (hy : 0 < y) (E : ℂ) (j J : ℤ)
    (s : ℂ) (v : PrimitiveRow) (x : ℝ) : ℂ :=
  cuspFourierMode (-j) x *
    (complexPointSeed E J s (primitiveMatrix v • rowPoint y hy x) -
      complexPointSeed 0 J s (primitiveMatrix v • rowPoint y hy x))

/-- The matrix height is exactly the centered quadratic height in the real-line kernel. -/
theorem matrix_rowPoint_im_eq_centered (γ : SL(2, ℤ))
    (hc : 0 < (γ 1 0 : ℝ)) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    (γ • rowPoint y hy x : UpperHalfPlane).im =
      y / ((γ 1 0 : ℝ) ^ 2 * ((x + (γ 1 1 : ℝ) / (γ 1 0 : ℝ)) ^ 2 + y ^ 2)) := by
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
  have hn := normSq_affine_row (γ 1 0 : ℝ) (γ 1 1 : ℝ) x y hc.ne'
  push_cast at hn
  change y / Complex.normSq ((γ 1 0 : ℂ) * Complex.mk x y + (γ 1 1 : ℂ)) = _
  rw [hn]

/-- Exact matrix energy-correction identity for every complex energy and exponent. -/
theorem energyFourierMatrix_eq_phase_kernel (y : ℝ) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) (s : ℂ) (γ : SL(2, ℤ))
    (hc : 0 < (γ 1 0 : ℝ)) (x : ℝ) :
    cuspFourierMode (-j) x *
      (complexPointSeed E J s (γ • rowPoint y hy x) -
        complexPointSeed 0 J s (γ • rowPoint y hy x)) =
      (cuspFourierMode j ((γ 1 1 : ℝ) / (γ 1 0 : ℝ)) *
        cuspFourierMode J ((γ 0 0 : ℝ) / (γ 1 0 : ℝ))) *
          energyFourierKernel (γ 1 0 : ℝ) y E j J s
            (x + (γ 1 1 : ℝ) / (γ 1 0 : ℝ)) := by
  rw [complexPointSeed_sub_zero_energy_eq_mul, ← mul_assoc,
    fourierMatrix_eq_phase_kernel j J s γ hc y hy x,
    matrix_rowPoint_im_eq_centered γ hc y hy x]
  simp only [energyFourierKernel, mul_assoc]

/-- An actual residue-row matrix gives the Kloosterman phase times a translated
energy-correction kernel, without any half-plane assumption. -/
theorem primitiveEnergyFourierTerm_residueRow_eq (y : ℝ) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) (s : ℂ) (n : ℕ) (u : (ZMod (n + 1))ˣ) (k : ℤ) (x : ℝ) :
    primitiveEnergyFourierTerm y hy E j J s (residueRow n u k) x =
      kloostermanPhase j J n u *
        energyFourierKernel (n + 1 : ℕ) y E j J s
          (x + ((u : ZMod (n + 1)).val : ℝ) / (n + 1 : ℕ) + (k : ℝ)) := by
  have hc : 0 < (primitiveMatrix (residueRow n u k) 1 0 : ℝ) := by
    rw [primitiveMatrix_residueRow_bottomLeft]
    positivity
  rw [primitiveEnergyFourierTerm, energyFourierMatrix_eq_phase_kernel y hy E j J s _ hc]
  simp only [primitiveMatrix_residueRow_bottomLeft, Int.cast_natCast]
  rw [residueRow_fourier_phase_eq_kloostermanPhase,
    primitiveMatrix_residueRow_bottomRight_div, ← add_assoc]

/-- Every actual residue-row integrand is ordinarily interval integrable. -/
theorem intervalIntegrable_primitiveEnergyFourierTerm_residueRow (y : ℝ) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) (s : ℂ) (n : ℕ) (u : (ZMod (n + 1))ˣ) (k : ℤ) :
    IntervalIntegrable (primitiveEnergyFourierTerm y hy E j J s (residueRow n u k))
      volume 0 1 := by
  have hc : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have h : Continuous (primitiveEnergyFourierTerm y hy E j J s (residueRow n u k)) := by
    simp_rw [show primitiveEnergyFourierTerm y hy E j J s (residueRow n u k) =
      fun x => kloostermanPhase j J n u * energyFourierKernel (n + 1 : ℕ) y E j J s
        (x + ((u : ZMod (n + 1)).val : ℝ) / (n + 1 : ℕ) + (k : ℝ)) from
        funext (primitiveEnergyFourierTerm_residueRow_eq y hy E j J s n u k)]
    exact continuous_const.mul ((continuous_energyFourierKernel hc hy E j J s).comp
      ((continuous_id.add continuous_const).add continuous_const))
  exact h.intervalIntegrable 0 1

/-- Integrated norms over all integer translates of an actual energy family are summable. -/
theorem summable_integral_norm_energyResidueRow (y : ℝ) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) {s : ℂ} (hs : 0 < s.re) (n : ℕ) (u : (ZMod (n + 1))ˣ) :
    Summable (fun k : ℤ => ∫ x in (0 : ℝ)..1,
      ‖primitiveEnergyFourierTerm y hy E j J s (residueRow n u k) x‖) := by
  simpa only [primitiveEnergyFourierTerm_residueRow_eq, norm_mul,
    norm_kloostermanPhase, one_mul] using
    summable_intervalIntegral_norm_energyFourierKernel
      (by positivity : 0 < ((n + 1 : ℕ) : ℝ)) hy E j J hs
        (((u : ZMod (n + 1)).val : ℝ) / (n + 1 : ℕ))

/-- A fixed unit residue unfolds by a genuine convergent sum to the ordinary real line. -/
theorem hasSum_integral_energyResidueRow (y : ℝ) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) {s : ℂ} (hs : 0 < s.re) (n : ℕ) (u : (ZMod (n + 1))ˣ) :
    HasSum (fun k : ℤ => ∫ x in (0 : ℝ)..1,
      primitiveEnergyFourierTerm y hy E j J s (residueRow n u k) x)
      (kloostermanPhase j J n u * ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y E j J s t) := by
  have h := (hasSum_intervalIntegral_energyFourierKernel
    (by positivity : 0 < ((n + 1 : ℕ) : ℝ)) hy E j J hs
      (((u : ZMod (n + 1)).val : ℝ) / (n + 1 : ℕ))).mul_left (kloostermanPhase j J n u)
  simpa only [primitiveEnergyFourierTerm_residueRow_eq,
    intervalIntegral.integral_const_mul] using h

/-- The fixed-residue ordinary integral sum has its literal full-line value. -/
theorem integral_energyResidueRow_tsum_eq (y : ℝ) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) {s : ℂ} (hs : 0 < s.re) (n : ℕ) (u : (ZMod (n + 1))ˣ) :
    (∑' k : ℤ, ∫ x in (0 : ℝ)..1,
      primitiveEnergyFourierTerm y hy E j J s (residueRow n u k) x) =
      kloostermanPhase j J n u * ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y E j J s t :=
  (hasSum_integral_energyResidueRow y hy E j J hs n u).tsum_eq

/-- At one positive denominator, unit residues and all integer translates have
summable ordinary integrated pointwise norms. -/
theorem summable_integral_norm_energyDenominator (y : ℝ) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    Summable (fun p : (ZMod (n + 1))ˣ × ℤ => ∫ x in (0 : ℝ)..1,
      ‖primitiveEnergyFourierTerm y hy E j J s (residueRow n p.1 p.2) x‖) := by
  apply (summable_prod_of_nonneg (fun p : (ZMod (n + 1))ˣ × ℤ =>
    intervalIntegral.integral_nonneg_of_forall zero_le_one (fun x => norm_nonneg _))).mpr
  refine ⟨fun u => summable_integral_norm_energyResidueRow y hy E j J hs n u, ?_⟩
  apply summable_of_hasFiniteSupport
  exact Set.toFinite _

/-- Absolute convergence of the actual ordinary Fourier integrals at one denominator. -/
theorem summable_norm_integral_energyDenominator (y : ℝ) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    Summable (fun p : (ZMod (n + 1))ˣ × ℤ =>
      ‖∫ x in (0 : ℝ)..1,
        primitiveEnergyFourierTerm y hy E j J s (residueRow n p.1 p.2) x‖) :=
  (summable_integral_norm_energyDenominator y hy E j J hs n).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun _ => intervalIntegral.norm_integral_le_integral_norm zero_le_one)

/-- The fixed-denominator family sums to the existing finite Kloosterman sum
times the ordinary full-line energy-correction integral. -/
theorem hasSum_integral_energyDenominator (y : ℝ) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    HasSum (fun p : (ZMod (n + 1))ˣ × ℤ => ∫ x in (0 : ℝ)..1,
      primitiveEnergyFourierTerm y hy E j J s (residueRow n p.1 p.2) x)
      (kloostermanSum j J n * ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y E j J s t) := by
  have hsum := (summable_norm_integral_energyDenominator y hy E j J hs n).of_norm
  convert hsum.hasSum using 1
  rw [hsum.tsum_prod]
  simp_rw [integral_energyResidueRow_tsum_eq y hy E j J hs n]
  rw [tsum_fintype, ← Finset.sum_mul]
  rfl

end GapFamily.Analytic.PoincareEnergyFourier
