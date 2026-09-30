import GapFamily.Analytic.Poincare.Fourier.PoincareEnergyFourierFunctional
import GapFamily.Analytic.Poincare.Fourier.PoincareEnergyFourierUnfold
import GapFamily.Analytic.Poincare.PoincarePositiveCoset
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierIdentity

/-! Actual arithmetic regrouping of the normally convergent nonzero-energy correction. -/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier
open Set MeasureTheory PoincareFourier PoincareFourierUnfold
open PoincareFourierRegroup
open scoped Topology MatrixGroups

/-- The exact diagonal energy correction from the identity cusp coset. -/
def energyFourierDirect (y : ℝ) (E : ℂ) (j J : ℤ) (s : ℂ) : ℂ :=
  if j = J then (y : ℂ) ^ s *
    (Complex.exp (-2 * (Real.pi : ℂ) * E * (y : ℂ)) - 1) else 0

/-- Literal identity-coset correction at every exponent and energy. -/
theorem energyFourierTerm_identity (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) (s : ℂ) (x : ℝ) :
    energyFourierTerm y hy E j J s identityCuspCoset x =
      fourierTerm j J s y hy identityCuspCoset x *
        (Complex.exp (-2 * (Real.pi : ℂ) * E * (y : ℂ)) - 1) := by
  simp only [energyFourierTerm, complexPoincareDifferenceTerm, fourierTerm,
    complexPoincareTerm_identity, complexPointSeed_sub_zero_energy_eq_mul]
  exact (mul_assoc _ _ _).symm

/-- Width-one orthogonality gives one diagonal term, with no extra factor one half. -/
theorem integral_energyFourierTerm_identity (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) (s : ℂ) :
    (∫ x in (0 : ℝ)..1, energyFourierTerm y hy E j J s identityCuspCoset x) =
      energyFourierDirect y E j J s := by
  simp_rw [energyFourierTerm_identity]
  rw [intervalIntegral.integral_mul_const, integral_fourierTerm_identity]
  classical
  by_cases h : j = J <;> simp [energyFourierDirect, h]

/-- The nonidentity subseries retains genuine integrated-norm summability. -/
theorem summable_integral_norm_energyNonidentity (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun q : {q : CuspCoset // q ≠ identityCuspCoset} =>
      ∫ x in (0 : ℝ)..1, ‖energyFourierTerm y hy E j J s q.val x‖) :=
  (summable_integral_norm_energyFourierTerm y hy E j J hs).subtype _

/-- Removing the actual identity coset subtracts precisely its literal diagonal. -/
theorem hasSum_integral_energyNonidentity (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun q : {q : CuspCoset // q ≠ identityCuspCoset} =>
      ∫ x in (0 : ℝ)..1, energyFourierTerm y hy E j J s q.val x)
      (energyFourierCorrection y hy E j J s - energyFourierDirect y E j J s) := by
  classical
  have h := hasSum_ite_sub_hasSum
    (hasSum_energyFourierCorrection y hy E j J hs) identityCuspCoset
  rw [integral_energyFourierTerm_identity] at h
  apply (hasSum_subtype_iff_indicator
    (f := fun q : CuspCoset => ∫ x in (0 : ℝ)..1, energyFourierTerm y hy E j J s q x)
    (s := {q : CuspCoset | q ≠ identityCuspCoset})).mpr
  convert h using 1
  funext q
  by_cases hq : q = identityCuspCoset <;> simp [Set.indicator, hq]

/-- The existing positive-row quotient equivalence preserves the literal correction integrand. -/
theorem energyFourierTerm_nonidentityResidueEquiv_symm (y : ℝ) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) (s : ℂ) (n : ℕ) (u : (ZMod (n + 1))ˣ) (k : ℤ) (x : ℝ) :
    energyFourierTerm y hy E j J s
      (nonidentityResidueEquiv.symm ⟨n, (u, k)⟩).val x =
        primitiveEnergyFourierTerm y hy E j J s (residueRow n u k) x := by
  rw [nonidentityResidueEquiv_symm_apply_val]
  rfl

/-- All positive-row arithmetic indices retain ordinary integrated-norm convergence. -/
theorem summable_integral_norm_energyIndexed (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun p : (Σ n : ℕ, (ZMod (n + 1))ˣ × ℤ) =>
      ∫ x in (0 : ℝ)..1,
        ‖primitiveEnergyFourierTerm y hy E j J s (residueRow p.1 p.2.1 p.2.2) x‖) := by
  have h := nonidentityResidueEquiv.symm.summable_iff.mpr
    (summable_integral_norm_energyNonidentity y hy E j J hs)
  convert h using 1
  funext p
  obtain ⟨n, u, k⟩ := p
  simp only [Function.comp_def, energyFourierTerm_nonidentityResidueEquiv_symm]

/-- The arithmetic indexing has the actual energy correction minus its identity term as sum. -/
theorem hasSum_integral_energyIndexed (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun p : (Σ n : ℕ, (ZMod (n + 1))ˣ × ℤ) =>
      ∫ x in (0 : ℝ)..1,
        primitiveEnergyFourierTerm y hy E j J s (residueRow p.1 p.2.1 p.2.2) x)
      (energyFourierCorrection y hy E j J s - energyFourierDirect y E j J s) := by
  have h := nonidentityResidueEquiv.symm.hasSum_iff.mpr
    (hasSum_integral_energyNonidentity y hy E j J hs)
  convert h using 1
  funext p
  obtain ⟨n, u, k⟩ := p
  simp only [Function.comp_def, energyFourierTerm_nonidentityResidueEquiv_symm]

/-- Actual fixed-denominator unfolding and quotient convergence give the full arithmetic HasSum. -/
theorem hasSum_kloosterman_energyFourier (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun n : ℕ => kloostermanSum j J n *
      ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y E j J s t)
      (energyFourierCorrection y hy E j J s - energyFourierDirect y E j J s) :=
  (hasSum_integral_energyIndexed y hy E j J hs).sigma
    (fun n => hasSum_integral_energyDenominator y hy E j J hs n)

/-- The denominator series converges in complex norm already on Re s>0. -/
theorem summable_norm_kloosterman_energyFourier (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ => ‖kloostermanSum j J n *
      ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y E j J s t‖) :=
  (hasSum_kloosterman_energyFourier y hy E j J hs).summable.norm

/-- Exact nonzero-energy Fourier correction, with a norm-convergent arithmetic tail. -/
theorem energyFourierCorrection_eq_direct_add_kloosterman (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    energyFourierCorrection y hy E j J s = energyFourierDirect y E j J s +
      ∑' n : ℕ, kloostermanSum j J n *
        ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y E j J s t := by
  rw [(hasSum_kloosterman_energyFourier y hy E j J hs).tsum_eq]
  ring

/-- The identification is an ordinary integral of the actual energy-difference series. -/
theorem integral_energyDifference_eq_direct_add_kloosterman (y : ℝ) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    (∫ x in (0 : ℝ)..1, cuspFourierMode (-j) x *
      complexPoincareEnergyDifference E J s (rowPoint y hy x)) =
      energyFourierDirect y E j J s + ∑' n : ℕ, kloostermanSum j J n *
        ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y E j J s t := by
  rw [← energyFourierCorrection_eq_intervalIntegral y hy E j J hs]
  exact energyFourierCorrection_eq_direct_add_kloosterman y hy E j J hs

end GapFamily.Analytic.PoincareEnergyFourier
