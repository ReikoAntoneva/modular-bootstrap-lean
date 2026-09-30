import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactWeight
import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalMeasure

/-! # Ordinary energy in an actual cusp collar

The collar is a literal rectangle in the fundamental strip. The inverse-square
modular density gives uniform value and vertical-gradient bounds on its ordinary
Euclidean integral, without a cutoff or an assumed local energy estimate.
-/

noncomputable section
namespace GapFamily.Analytic

open Set MeasureTheory ModularGradient

def cuspCollarRectangle (ε : ℝ) : Set ℂ :=
  {z | |z.re| < 1 / 2 ∧ 1 < z.im ∧ z.im < 1 + ε}

theorem isOpen_cuspCollarRectangle (ε : ℝ) : IsOpen (cuspCollarRectangle ε) :=
  (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const))

theorem cuspCollarRectangle_subset_interior (ε : ℝ) :
    cuspCollarRectangle ε ⊆ modularInterior := by
  intro z hz
  exact horizontalCusp_subset_modularInterior (le_refl 1) ⟨hz.1, hz.2.1⟩

theorem cuspCollar_value_energy_le (F : smoothCore) {ε : ℝ} (hε : ε ≤ 1) :
    (∫ z : ℂ in cuspCollarRectangle ε, ‖F.val z‖ ^ 2) ≤ 4 * ‖value F‖ ^ 2 := by
  let K := cuspCollarRectangle ε
  have hK : MeasurableSet K := (isOpen_cuspCollarRectangle ε).measurableSet
  rw [← integral_indicator hK]
  rw [integral_eq_coordinate_weighted _ (by
    intro z hz
    exact indicator_of_notMem (fun hk => hz (cuspCollarRectangle_subset_interior ε hk)) _)]
  calc
    _ ≤ ∫ z, 4 * ‖F.val z‖ ^ 2 ∂modularCoordinateMeasure := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _)
          (by exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) z))
        ((coordinate_core_value_integrable F).const_mul 4)
      apply Filter.Eventually.of_forall
      intro z
      dsimp only
      by_cases hz : z ∈ K
      · rw [indicator_of_mem hz]
        have hlow : 1 < z.im := hz.2.1
        have hhigh : z.im < 2 := by have := hz.2.2; linarith
        exact mul_le_mul_of_nonneg_right (by nlinarith : z.im ^ 2 ≤ 4) (sq_nonneg _)
      · rw [indicator_of_notMem hz, mul_zero]
        positivity
    _ = _ := by rw [integral_const_mul, coordinate_core_value_integral]

theorem cuspCollar_vertical_energy_le (F : smoothCore) (ε : ℝ) :
    (∫ z : ℂ in cuspCollarRectangle ε, ‖fderiv ℝ F.val z Complex.I‖ ^ 2) ≤
      ‖coreGradient F‖ ^ 2 := by
  let K := cuspCollarRectangle ε
  have hK : MeasurableSet K := (isOpen_cuspCollarRectangle ε).measurableSet
  rw [← integral_indicator hK]
  rw [integral_eq_coordinate_weighted _ (by
    intro z hz
    exact indicator_of_notMem (fun hk => hz (cuspCollarRectangle_subset_interior ε hk)) _)]
  have hcomp :
      (∫ z, z.im ^ 2 * K.indicator (fun w => ‖fderiv ℝ F.val w Complex.I‖ ^ 2) z
        ∂modularCoordinateMeasure) ≤ ‖yComponent F‖ ^ 2 := by
    calc
      _ ≤ ∫ z, ‖(z.im : ℂ) * fderiv ℝ F.val z Complex.I‖ ^ 2
          ∂modularCoordinateMeasure := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _)
            (by exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) z))
          (coordinate_core_component_integrable Complex.I (fun G => G.property.2.2.2.2) F)
        apply Filter.Eventually.of_forall
        intro z
        dsimp only
        by_cases hz : z ∈ K
        · rw [indicator_of_mem hz]
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
          exact le_rfl
        · rw [indicator_of_notMem hz, mul_zero]
          positivity
      _ = _ := coordinate_core_component_integral Complex.I (fun G => G.property.2.2.2.2) F
  exact hcomp.trans (by rw [coreGradient_norm_sq]; nlinarith [sq_nonneg ‖xComponent F‖])

end GapFamily.Analytic
