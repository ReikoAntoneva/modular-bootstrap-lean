import GapFamily.Analytic.Spatial.SpatialOrbitConstantMode
import GapFamily.Analytic.Spatial.SpatialOrbitPositive
import Mathlib.Tactic.NoncommRing

/-! Actual compression off the constant mode and its literal mean-zero kernel
in the real convergence half-plane. -/
noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open MeasureTheory UpperHalfPlane
open scoped ComplexOrder

/-- The actual integral operator compressed by the fixed mean-zero projection. -/
def spatialOrbitMeanZeroOperator (s : ℝ) (hs : 1 < s) :
    ModularHilbert →L[ℂ] ModularHilbert :=
  modularMeanZeroProjection.comp
    ((spatialOrbitIntegralOperator s hs).comp modularMeanZeroProjection)

/-- The literal kernel after removing the constant spectral channel. -/
def spatialOrbitMeanZeroKernel (s : ℝ) (z w : UpperHalfPlane) : ℂ :=
  spatialOrbitKernel (s : ℂ) z w - ((3 / (s - 1) : ℝ) : ℂ)

/-- The proved constant eigenvalue makes compression exactly subtraction of
the constant-channel operator, rather than a formal block decomposition. -/
theorem spatialOrbitMeanZeroOperator_eq_sub (s : ℝ) (hs : 1 < s) :
    spatialOrbitMeanZeroOperator s hs = spatialOrbitIntegralOperator s hs -
      (((Real.pi / (s - 1) : ℝ) : ℂ) • modularConstantProjection) := by
  let A := spatialOrbitIntegralOperator s hs
  let P := modularConstantProjection
  let massScalar : ℂ := ((Real.pi / (s - 1) : ℝ) : ℂ)
  have hAP : A * P = massScalar • P := spatialOrbitIntegralOperator_comp_constantProjection s hs
  have hPA : P * A = massScalar • P := constantProjection_comp_spatialOrbitIntegralOperator s hs
  have hP : P * P = P := modularConstantProjection_idempotent
  unfold spatialOrbitMeanZeroOperator
  rw [modularMeanZeroProjection_eq]
  change (1 - P) * (A * (1 - P)) = A - massScalar • P
  calc
    _ = A - A * P - P * A + (P * A) * P := by
      simp only [mul_sub, sub_mul, one_mul, mul_one, mul_assoc]
      abel
    _ = A - massScalar • P - massScalar • P + (massScalar • P) * P := by rw [hAP, hPA]
    _ = A - massScalar • P := by rw [smul_mul_assoc, hP]; abel

/-- Compression by the genuine orthogonal projection preserves the proved
positivity of the actual spatial operator. -/
theorem spatialOrbitMeanZeroOperator_isPositive (s : ℝ) (hs : 1 < s) :
    (spatialOrbitMeanZeroOperator s hs).IsPositive := by
  exact ContinuousLinearMap.IsPositive.conj_starProjection modularMeanZero
    (spatialOrbitIntegralOperator_isPositive s hs)

/-- Exact hyperbolic volume pi/3 fixes the subtracted kernel coefficient. -/
theorem spatialOrbit_constantKernel_factor (s : ℝ) (hs : 1 < s)
    (z w : UpperHalfPlane) :
    (((Real.pi / (s - 1) : ℝ) : ℂ)) * modularConstantKernel z w =
      ((3 / (s - 1) : ℝ) : ℂ) := by
  rw [modularConstantKernel_eq]
  have h : Real.pi / (s - 1) * (3 / Real.pi) = 3 / (s - 1) := by
    field_simp [Real.pi_ne_zero, sub_ne_zero.mpr hs.ne']
  exact_mod_cast h

/-- Every L² input has a genuine ordinary row integral against the literal
mean-zero kernel at almost every target point. -/
theorem spatialOrbitMeanZeroKernel_integrable_ae (s : ℝ) (hs : 1 < s)
    (f : ModularHilbert) :
    ∀ᵐ z : UpperHalfPlane ∂modularMeasure,
      Integrable (fun w => spatialOrbitMeanZeroKernel s z w * f w) modularMeasure := by
  filter_upwards [spatialOrbitIntegralOperator_integrable_ae s hs f] with z hz
  have hi := hz.sub ((integrable_modularHilbert f).const_mul (((3 / (s - 1) : ℝ) : ℂ)))
  change Integrable (fun w => spatialOrbitKernel (s : ℂ) z w * f w -
    (((3 / (s - 1) : ℝ) : ℂ)) * f w) modularMeasure at hi
  simpa only [spatialOrbitMeanZeroKernel, sub_mul] using hi

/-- The actual compressed operator has precisely K_s - 3/(s-1) as its
ordinary integral representative, for every actual modular L² input. -/
theorem spatialOrbitMeanZeroOperator_ae (s : ℝ) (hs : 1 < s)
    (f : ModularHilbert) :
    spatialOrbitMeanZeroOperator s hs f =ᵐ[modularMeasure]
      fun z => ∫ w, spatialOrbitMeanZeroKernel s z w * f w ∂modularMeasure := by
  let massScalar : ℂ := ((Real.pi / (s - 1) : ℝ) : ℂ)
  rw [spatialOrbitMeanZeroOperator_eq_sub]
  change spatialOrbitIntegralOperator s hs f - massScalar • modularConstantProjection f =ᵐ[modularMeasure] _
  filter_upwards [spatialOrbitIntegralOperator_ae s hs f, modularConstantProjection_ae f,
    Lp.coeFn_sub (spatialOrbitIntegralOperator s hs f) (massScalar • modularConstantProjection f),
    Lp.coeFn_smul massScalar (modularConstantProjection f),
    spatialOrbitIntegralOperator_integrable_ae s hs f] with z hA hP hsub hsm hrow
  simp only [Pi.sub_apply] at hsub
  simp only [Pi.smul_apply, smul_eq_mul] at hsm
  rw [hsub, hsm, hA, hP]
  have hmean : massScalar * modularAverage f =
      ∫ w, (((3 / (s - 1) : ℝ) : ℂ)) * f w ∂modularMeasure := by
    rw [← modularConstantKernel_integral z f, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with w
    rw [← mul_assoc]
    exact congrArg (fun c : ℂ => c * f w) (spatialOrbit_constantKernel_factor s hs z w)
  rw [hmean]
  simp only [spatialOrbitMeanZeroKernel, sub_mul]
  rw [integral_sub hrow ((integrable_modularHilbert f).const_mul (((3 / (s - 1) : ℝ) : ℂ)))]

end GapFamily.Analytic.SpatialPoint
