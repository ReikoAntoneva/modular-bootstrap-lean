import GapFamily.Analytic.Poincare.PoincareHorizontalFunctional
import GapFamily.Analytic.Poincare.Continuation.PoincareCompactEnergyEntire
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierIntegral

/-! Ordinary Fourier integrals of the actual, normally convergent energy correction. -/

noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier

open Set MeasureTheory UpperHalfPlane PoincareFourier
open PoincareFourierContinuation PoincareEnergyConvergentAnalytic
open scoped Topology

/-- The literal Fourier integrand of one actual energy-difference quotient term. -/
def energyFourierTerm (y : ℝ) (hy : 0 < y) (E : ℂ) (j J : ℤ) (s : ℂ)
    (q : CuspCoset) (x : ℝ) : ℂ :=
  cuspFourierMode (-j) x * complexPoincareDifferenceTerm E J s (rowPoint y hy x) q

/-- The bounded ordinary Fourier functional applied to the actual compact energy sum. -/
def energyFourierCorrection (y : ℝ) (hy : 0 < y) (E : ℂ) (j J : ℤ) (s : ℂ) : ℂ :=
  horizontalFourierFunctional y j
    (compactEnergySeries (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) E J s)

/-- A compact continuous row representative gives a genuinely integrable literal integrand. -/
theorem intervalIntegrable_horizontalFourierRepresentative (y : ℝ) (j : ℤ)
    (F : C(horizontalRow y, ℂ)) (g : ℝ → ℂ)
    (hfg : ∀ (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1),
      F ⟨Complex.mk x y, ⟨x, hx, rfl⟩⟩ = g x) :
    IntervalIntegrable (fun x => cuspFourierMode (-j) x * g x) volume 0 1 := by
  have hc : Continuous (fun x : HorizontalInterval => cuspFourierMode (-j) x.val * g x.val) := by
    have heq : (fun x : HorizontalInterval => cuspFourierMode (-j) x.val * g x.val) =
        fun x => horizontalFourierMode j x * F (horizontalRowPath y x) := by
      funext x
      change cuspFourierMode (-j) x.val * g x.val =
        cuspFourierMode (-j) x.val * F ⟨Complex.mk x.val y, ⟨x.val, x.property, rfl⟩⟩
      rw [hfg x.val x.property]
    rw [heq]
    exact (horizontalFourierMode j).continuous.mul (F.continuous.comp (horizontalRowPath y).continuous)
  exact (continuousOn_iff_continuous_domRestrict.mpr hc).intervalIntegrable_of_Icc zero_le_one

/-- Evaluation of the actual compact term is the literal upper-half-plane row term. -/
theorem compactEnergyTerm_horizontalRow_apply (y : ℝ) (hy : 0 < y) (E : ℂ)
    (J : ℤ) (s : ℂ) (q : CuspCoset) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    compactEnergyTerm (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) E J s q
      ⟨Complex.mk x y, ⟨x, hx, rfl⟩⟩ =
        complexPoincareDifferenceTerm E J s (rowPoint y hy x) q := by
  rw [compactEnergyTerm_apply]
  rw [show ofComplex (Complex.mk x y) = rowPoint y hy x from ofComplex_apply (rowPoint y hy x)]

/-- Each single energy Fourier term is interval integrable at every exponent. -/
theorem intervalIntegrable_energyFourierTerm (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) (s : ℂ) (q : CuspCoset) :
    IntervalIntegrable (energyFourierTerm y hy E j J s q) volume 0 1 :=
  intervalIntegrable_horizontalFourierRepresentative y j
    (compactEnergyTerm (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) E J s q)
    _ (compactEnergyTerm_horizontalRow_apply y hy E J s q)

/-- The compact term's functional is exactly the ordinary integral of the actual term. -/
theorem horizontalFourierFunctional_compactEnergyTerm (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) (s : ℂ) (q : CuspCoset) :
    horizontalFourierFunctional y j
      (compactEnergyTerm (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) E J s q) =
        ∫ x in (0 : ℝ)..1, energyFourierTerm y hy E j J s q x :=
  horizontalFourierFunctional_eq_intervalIntegral y j _ _
    (compactEnergyTerm_horizontalRow_apply y hy E J s q)

/-- The actual compact series agrees with the literal energy correction along the row. -/
theorem compactEnergySeries_horizontalRow_apply (y : ℝ) (hy : 0 < y) (E : ℂ)
    (J : ℤ) {s : ℂ} (hs : 0 < s.re) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    compactEnergySeries (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) E J s
      ⟨Complex.mk x y, ⟨x, hx, rfl⟩⟩ =
        complexPoincareEnergyDifference E J s (rowPoint y hy x) := by
  rw [compactEnergySeries_apply _ _ _ _ hs]
  rw [show ofComplex (Complex.mk x y) = rowPoint y hy x from ofComplex_apply (rowPoint y hy x)]

/-- The Fourier correction is the literal ordinary interval integral on its full convergence half-plane. -/
theorem energyFourierCorrection_eq_intervalIntegral (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    energyFourierCorrection y hy E j J s =
      ∫ x in (0 : ℝ)..1,
        cuspFourierMode (-j) x * complexPoincareEnergyDifference E J s (rowPoint y hy x) :=
  horizontalFourierFunctional_eq_intervalIntegral y j _ _
    (compactEnergySeries_horizontalRow_apply y hy E J hs)

/-- The literal energy-correction Fourier integral is genuinely interval integrable. -/
theorem intervalIntegrable_energyFourierCorrectionIntegrand (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    IntervalIntegrable (fun x =>
      cuspFourierMode (-j) x * complexPoincareEnergyDifference E J s (rowPoint y hy x))
        volume 0 1 :=
  intervalIntegrable_horizontalFourierRepresentative y j
    (compactEnergySeries (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) E J s)
    _ (compactEnergySeries_horizontalRow_apply y hy E J hs)

/-- The compact supremum norm bounds the literal term pointwise throughout the integration row. -/
theorem norm_energyFourierTerm_le_compactEnergyTerm (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) (s : ℂ) (q : CuspCoset) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖energyFourierTerm y hy E j J s q x‖ ≤
      ‖compactEnergyTerm (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) E J s q‖ := by
  rw [energyFourierTerm, norm_mul, norm_cuspFourierMode, one_mul,
    ← compactEnergyTerm_horizontalRow_apply y hy E J s q x hx]
  exact ContinuousMap.norm_coe_le_norm _ _

/-- Unit interval length and unit Fourier modulus preserve the compact majorant after integration. -/
theorem integral_norm_energyFourierTerm_le (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) (s : ℂ) (q : CuspCoset) :
    (∫ x in (0 : ℝ)..1, ‖energyFourierTerm y hy E j J s q x‖) ≤
      ‖compactEnergyTerm (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) E J s q‖ := by
  have h := intervalIntegral.integral_mono_on zero_le_one
    (intervalIntegrable_energyFourierTerm y hy E j J s q).norm
    (intervalIntegrable_const (c :=
      ‖compactEnergyTerm (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) E J s q‖))
    (norm_energyFourierTerm_le_compactEnergyTerm y hy E j J s q)
  simpa using h

/-- The norms of the ordinary complex term integrals obey the same actual compact majorant. -/
theorem norm_integral_energyFourierTerm_le (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) (s : ℂ) (q : CuspCoset) :
    ‖∫ x in (0 : ℝ)..1, energyFourierTerm y hy E j J s q x‖ ≤
      ‖compactEnergyTerm (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) E J s q‖ := by
  rw [← horizontalFourierFunctional_compactEnergyTerm]
  exact norm_horizontalFourierFunctional_apply_le y j _

/-- The integral of each term norm forms a summable family on Re s>0. -/
theorem summable_integral_norm_energyFourierTerm (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun q : CuspCoset => ∫ x in (0 : ℝ)..1, ‖energyFourierTerm y hy E j J s q x‖) := by
  apply (compactEnergyTerm_summable_norm (horizontalRow y)
    (horizontalRow_subset_upperHalfPlaneSet y hy) E J hs).of_nonneg_of_le
  · intro q
    exact intervalIntegral.integral_nonneg_of_forall zero_le_one (fun x => norm_nonneg _)
  · exact integral_norm_energyFourierTerm_le y hy E j J s

/-- Absolute summability also holds for the ordinary complex term integrals. -/
theorem summable_norm_integral_energyFourierTerm (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun q : CuspCoset => ‖∫ x in (0 : ℝ)..1, energyFourierTerm y hy E j J s q x‖) := by
  exact (compactEnergyTerm_summable_norm (horizontalRow y)
    (horizontalRow_subset_upperHalfPlaneSet y hy) E J hs).of_nonneg_of_le
      (fun _ => norm_nonneg _) (norm_integral_energyFourierTerm_le y hy E j J s)

/-- The full sum of the termwise absolute integrals is bounded by the actual compact norm sum. -/
theorem tsum_integral_norm_energyFourierTerm_le (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    (∑' q : CuspCoset, ∫ x in (0 : ℝ)..1, ‖energyFourierTerm y hy E j J s q x‖) ≤
      ∑' q : CuspCoset,
        ‖compactEnergyTerm (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) E J s q‖ :=
  Summable.tsum_le_tsum (integral_norm_energyFourierTerm_le y hy E j J s)
    (summable_integral_norm_energyFourierTerm y hy E j J hs)
    (compactEnergyTerm_summable_norm (horizontalRow y)
      (horizontalRow_subset_upperHalfPlaneSet y hy) E J hs)

/-- Termwise ordinary integration has the actual Fourier correction as its HasSum value. -/
theorem hasSum_energyFourierCorrection (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun q : CuspCoset => ∫ x in (0 : ℝ)..1, energyFourierTerm y hy E j J s q x)
      (energyFourierCorrection y hy E j J s) := by
  have h := (compactEnergyTerm_summable_norm (horizontalRow y)
    (horizontalRow_subset_upperHalfPlaneSet y hy) E J hs).of_norm.hasSum.map
      (horizontalFourierFunctional y j).toAddMonoidHom (horizontalFourierFunctional y j).continuous
  change HasSum (fun q : CuspCoset => horizontalFourierFunctional y j
    (compactEnergyTerm (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) E J s q))
      (energyFourierCorrection y hy E j J s) at h
  convert h using 1
  funext q
  exact (horizontalFourierFunctional_compactEnergyTerm y hy E j J s q).symm

/-- The same HasSum identity written entirely with literal ordinary integrals. -/
theorem hasSum_integral_energyFourierTerm (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun q : CuspCoset => ∫ x in (0 : ℝ)..1,
      cuspFourierMode (-j) x * complexPoincareDifferenceTerm E J s (rowPoint y hy x) q)
      (∫ x in (0 : ℝ)..1,
        cuspFourierMode (-j) x * complexPoincareEnergyDifference E J s (rowPoint y hy x)) := by
  rw [← energyFourierCorrection_eq_intervalIntegral y hy E j J hs]
  exact hasSum_energyFourierCorrection y hy E j J hs

/-- The Fourier correction inherits the actual compact norm bound. -/
theorem norm_energyFourierCorrection_le (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) (s : ℂ) :
    ‖energyFourierCorrection y hy E j J s‖ ≤
      ‖compactEnergySeries (horizontalRow y) (horizontalRow_subset_upperHalfPlaneSet y hy) E J s‖ :=
  norm_horizontalFourierFunctional_apply_le y j _

/-- Norm analyticity in the exponent holds throughout the improved convergence half-plane. -/
theorem analyticAt_energyFourierCorrection_exponent (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (energyFourierCorrection y hy E j J) s :=
  ((horizontalFourierFunctional y j).analyticAt _).comp
    (compactEnergySeries_analyticAt_exponent (horizontalRow y)
      (horizontalRow_subset_upperHalfPlaneSet y hy) E J hs)

/-- The complete positive real-part exponent domain has complex norm analyticity. -/
theorem analyticOnNhd_energyFourierCorrection_exponent (y : ℝ) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) :
    AnalyticOnNhd ℂ (energyFourierCorrection y hy E j J) {s : ℂ | 0 < s.re} :=
  fun _ hs => analyticAt_energyFourierCorrection_exponent y hy E j J hs

/-- In cutoff coordinates, the actual correction is norm analytic through the threshold. -/
theorem analyticAt_energyFourierCorrection_parameter (y : ℝ) (hy : 0 < y) (E : ℂ)
    (j J : ℤ) {κ : ℂ} (hκ : (-1 / 2 : ℝ) < κ.re) :
    AnalyticAt ℂ (fun w => energyFourierCorrection y hy E j J (CuspFourierCutoff.exponent w)) κ :=
  ((horizontalFourierFunctional y j).analyticAt _).comp
    (compactEnergySeries_analyticAt_parameter (horizontalRow y)
      (horizontalRow_subset_upperHalfPlaneSet y hy) E J hκ)

/-- At every convergent exponent, the actual ordinary Fourier correction is entire in energy. -/
theorem analyticAt_energyFourierCorrection_energy (y : ℝ) (hy : 0 < y)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) (E : ℂ) :
    AnalyticAt ℂ (fun F => energyFourierCorrection y hy F j J s) E :=
  ((horizontalFourierFunctional y j).analyticAt _).comp
    (compactEnergySeries_analyticAt_energy (horizontalRow y)
      (horizontalRow_subset_upperHalfPlaneSet y hy) J hs E)

end GapFamily.Analytic.PoincareEnergyFourier
