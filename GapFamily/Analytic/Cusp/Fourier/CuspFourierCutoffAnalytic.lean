import GapFamily.Analytic.Modular.ModularHilbert
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section

namespace GapFamily.Analytic.CuspFourierCutoff

open MeasureTheory
open scoped BoundedContinuousFunction

/-- Evaluation of the actual bounded-continuous-function exponential. -/
theorem boundedExp_apply (ell : UpperHalfPlane →ᵇ ℂ) (κ : ℂ) (τ : UpperHalfPlane) :
    NormedSpace.exp (κ • ell) τ = Complex.exp (κ * ell τ) := by
  let ev : (UpperHalfPlane →ᵇ ℂ) →+* ℂ :=
    { toFun := fun f => f τ
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hev : Continuous ev := (BoundedContinuousFunction.evalCLM ℂ τ).continuous
  have h := NormedSpace.map_exp ev hev (κ • ell)
  change NormedSpace.exp (κ • ell) τ = NormedSpace.exp (κ * ell τ) at h
  simpa only [Complex.exp_eq_exp_ℂ] using h

/-- The literal affine exponential forcing in the spatial Banach algebra. -/
def boundedForcing (A B ell : UpperHalfPlane →ᵇ ℂ) (κ : ℂ) : UpperHalfPlane →ᵇ ℂ :=
  NormedSpace.exp (κ • ell) * (A + κ • B)

theorem boundedForcing_apply (A B ell : UpperHalfPlane →ᵇ ℂ) (κ : ℂ)
    (τ : UpperHalfPlane) :
    boundedForcing A B ell κ τ = Complex.exp (κ * ell τ) * (A τ + κ * B τ) := by
  simp only [boundedForcing, BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply,
    smul_eq_mul, boundedExp_apply]

/-- Entire parameter dependence in the uniform spatial norm. -/
theorem boundedForcing_analyticAt (A B ell : UpperHalfPlane →ᵇ ℂ) (κ : ℂ) :
    AnalyticAt ℂ (boundedForcing A B ell) κ := by
  have hs : AnalyticAt ℂ (fun z : ℂ => z • ell) κ :=
    analyticAt_id.smul analyticAt_const
  have he : AnalyticAt ℂ (fun z : ℂ => NormedSpace.exp (z • ell)) κ :=
    (NormedSpace.exp_analytic (𝕂 := ℂ) (κ • ell)).comp_of_eq hs rfl
  exact he.mul (analyticAt_const.add (analyticAt_id.smul analyticAt_const))

/-- The actual modular `L²` forcing obtained from its bounded continuous representative. -/
def hilbertForcing (A B ell : UpperHalfPlane →ᵇ ℂ) (κ : ℂ) : ModularHilbert :=
  BoundedContinuousFunction.toLp 2 modularMeasure ℂ (boundedForcing A B ell κ)

/-- The forcing is entire in the genuine modular Hilbert norm. -/
theorem hilbertForcing_analyticAt (A B ell : UpperHalfPlane →ᵇ ℂ) (κ : ℂ) :
    AnalyticAt ℂ (hilbertForcing A B ell) κ := by
  change AnalyticAt ℂ (fun z => BoundedContinuousFunction.toLp 2 modularMeasure ℂ
    (boundedForcing A B ell z)) κ
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := UpperHalfPlane →ᵇ ℂ) (F := ModularHilbert)
    (BoundedContinuousFunction.toLp 2 modularMeasure ℂ) _).comp
      (boundedForcing_analyticAt A B ell κ)

/-- The Hilbert class has the exact ordinary exponential representative. -/
theorem hilbertForcing_ae (A B ell : UpperHalfPlane →ᵇ ℂ) (κ : ℂ) :
    hilbertForcing A B ell κ =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => Complex.exp (κ * ell τ) * (A τ + κ * B τ)) := by
  apply (BoundedContinuousFunction.coeFn_toLp 2 modularMeasure ℂ
    (boundedForcing A B ell κ)).trans
  exact Filter.Eventually.of_forall (boundedForcing_apply A B ell κ)

end GapFamily.Analytic.CuspFourierCutoff
