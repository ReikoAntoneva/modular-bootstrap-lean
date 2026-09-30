import GapFamily.Analytic.Eisenstein.EisensteinFourierAverage
import GapFamily.Analytic.Cusp.Fourier.CuspFourierProfileCore

/-! The ordinary horizontal Fourier coefficient as a bounded complex linear functional. -/

noncomputable section
namespace GapFamily.Analytic.PoincareFourierContinuation

open Set UpperHalfPlane
open scoped Topology

/-- The closed unit row at height y, as an actual compact subset of the complex plane. -/
def horizontalRow (y : ℝ) : Set ℂ :=
  (fun x : ℝ => Complex.mk x y) '' Icc (0 : ℝ) 1

theorem continuous_horizontalRowMap (y : ℝ) :
    Continuous (fun x : ℝ => Complex.mk x y) := by
  convert Complex.continuous_ofReal.add
    (continuous_const (y := (y : ℂ) * Complex.I)) using 1
  funext x
  apply Complex.ext <;> simp

theorem isCompact_horizontalRow (y : ℝ) : IsCompact (horizontalRow y) :=
  isCompact_Icc.image (continuous_horizontalRowMap y)

instance horizontalRow_compactSpace (y : ℝ) : CompactSpace (horizontalRow y) :=
  isCompact_iff_compactSpace.mp (isCompact_horizontalRow y)

theorem mem_horizontalRow (y x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    Complex.mk x y ∈ horizontalRow y := ⟨x, hx, rfl⟩

theorem horizontalRow_subset_upperHalfPlaneSet (y : ℝ) (hy : 0 < y) :
    horizontalRow y ⊆ upperHalfPlaneSet := by
  rintro z ⟨x, hx, rfl⟩
  exact hy

/-- The literal unit-interval path along the compact row. -/
def horizontalRowPath (y : ℝ) : C(HorizontalInterval, horizontalRow y) where
  toFun x := ⟨Complex.mk x.val y, mem_horizontalRow y x.val x.property⟩
  continuous_toFun := ((continuous_horizontalRowMap y).comp continuous_subtype_val).subtype_mk _

/-- The output Fourier mode restricted to the compact horizontal interval. -/
def horizontalFourierMode (j : ℤ) : C(HorizontalInterval, ℂ) where
  toFun x := cuspFourierMode (-j) x.val
  continuous_toFun := (contDiff_cuspFourierMode (-j)).continuous.comp continuous_subtype_val

/-- Pull back to the row, multiply by the output Fourier mode, and apply the actual average. -/
def horizontalFourierFunctional (y : ℝ) (j : ℤ) : C(horizontalRow y, ℂ) →L[ℂ] ℂ :=
  (horizontalAverage.comp
    (ContinuousLinearMap.mul ℂ C(HorizontalInterval, ℂ) (horizontalFourierMode j))).comp
      (ContinuousMap.compCLM ℂ ℂ (horizontalRowPath y))

@[simp] theorem horizontalFourierFunctional_apply (y : ℝ) (j : ℤ)
    (F : C(horizontalRow y, ℂ)) :
    horizontalFourierFunctional y j F =
      ∫ x : ℝ in 0..1,
        cuspFourierMode (-j) (Set.projIcc 0 1 zero_le_one x).val *
          F (horizontalRowPath y (Set.projIcc 0 1 zero_le_one x)) := rfl

/-- The functional is the ordinary integral of every representative agreeing on the row. -/
theorem horizontalFourierFunctional_eq_intervalIntegral (y : ℝ) (j : ℤ)
    (F : C(horizontalRow y, ℂ)) (g : ℝ → ℂ)
    (hfg : ∀ (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1),
      F ⟨Complex.mk x y, ⟨x, hx, rfl⟩⟩ = g x) :
    horizontalFourierFunctional y j F =
      ∫ x : ℝ in 0..1, cuspFourierMode (-j) x * g x := by
  change horizontalAverage (horizontalFourierMode j * F.comp (horizontalRowPath y)) = _
  apply horizontalAverage_eq_intervalIntegral
  intro x
  change cuspFourierMode (-j) x.val *
    F ⟨Complex.mk x.val y, ⟨x.val, x.property, rfl⟩⟩ = cuspFourierMode (-j) x.val * g x.val
  rw [hfg x.val x.property]

/-- The unit-length row and unit-modulus mode give a bound independent of height and mode. -/
theorem norm_horizontalFourierFunctional_apply_le (y : ℝ) (j : ℤ)
    (F : C(horizontalRow y, ℂ)) : ‖horizontalFourierFunctional y j F‖ ≤ ‖F‖ := by
  rw [horizontalFourierFunctional_apply]
  have hbound : ∀ x : ℝ, x ∈ uIoc (0 : ℝ) 1 →
      ‖cuspFourierMode (-j) (Set.projIcc 0 1 zero_le_one x).val *
        F (horizontalRowPath y (Set.projIcc 0 1 zero_le_one x))‖ ≤ ‖F‖ := by
    intro x hx
    rw [norm_mul, norm_cuspFourierMode, one_mul]
    exact F.norm_coe_le_norm _
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbound

theorem norm_horizontalFourierFunctional_le (y : ℝ) (j : ℤ) :
    ‖horizontalFourierFunctional y j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro F
  simpa only [one_mul] using norm_horizontalFourierFunctional_apply_le y j F

end GapFamily.Analytic.PoincareFourierContinuation
