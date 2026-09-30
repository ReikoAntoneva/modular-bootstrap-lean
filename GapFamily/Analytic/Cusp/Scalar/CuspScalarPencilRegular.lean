import GapFamily.Analytic.Cusp.Scalar.CuspScalarPencilWeak
import GapFamily.Analytic.Cusp.Scalar.CuspScalarPencilAnalytic
import GapFamily.Analytic.Foundation.PositiveQuarterPencil

/-!
# Physical regularity of the actual scalar cusp pencil

The proved positive response and four-fifths norm bound give regularity off
the real quarter ray. Every parameter κ with positive real part yields the
actual scalar weak solution at z=1/4−κ², with uniqueness and local analyticity.
-/

noncomputable section

namespace GapFamily.Analytic

open scoped Topology

/-- The actual scalar pencil is regular off the real quarter ray. -/
theorem cuspScalarPencil_isUnit_regular {z : ℂ}
    (hz : z.im ≠ 0 ∨ z.re < (1 / 4 : ℝ)) : IsUnit (cuspScalarPencil z) :=
  positiveQuarterPencil_isUnit cuspScalarWeakResolvent
    cuspScalarWeakResolvent_isPositive cuspScalarWeakResolvent_norm_le hz

/-- Every physical logarithmic half-plane parameter gives an actual scalar inverse. -/
theorem cuspScalarPencil_isUnit_physical {κ : ℂ} (hκ : 0 < κ.re) :
    IsUnit (cuspScalarPencil ((1 / 4 : ℂ) - κ ^ 2)) :=
  positiveQuarterPencil_isUnit_physical cuspScalarWeakResolvent
    cuspScalarWeakResolvent_isPositive cuspScalarWeakResolvent_norm_le hκ

/-- The constructed physical scalar response solves the true scalar form equation. -/
theorem cuspScalarPencilSolution_equation_physical {κ : ℂ} (hκ : 0 < κ.re)
    (f : ModularHilbert) (v : cuspScalarForm) :
    inner ℂ (cuspScalarGradient v)
        (cuspScalarGradient (cuspScalarPencilSolution ((1 / 4 : ℂ) - κ ^ 2) f)) -
      ((1 / 4 : ℂ) - κ ^ 2) * inner ℂ (scalarCuspEmbedding v)
        (scalarCuspEmbedding (cuspScalarPencilSolution ((1 / 4 : ℂ) - κ ^ 2) f)) =
      inner ℂ (scalarCuspEmbedding v) f :=
  cuspScalarPencilSolution_equation (cuspScalarPencil_isUnit_physical hκ) f v

/-- Physical scalar weak solutions are unique in the actual completed scalar form space. -/
theorem cuspScalarPencilSolution_unique_physical {κ : ℂ} (hκ : 0 < κ.re)
    (f : ModularHilbert) (u : cuspScalarForm)
    (hu : ∀ v : cuspScalarForm,
      inner ℂ (cuspScalarGradient v) (cuspScalarGradient u) -
        ((1 / 4 : ℂ) - κ ^ 2) * inner ℂ (scalarCuspEmbedding v) (scalarCuspEmbedding u) =
          inner ℂ (scalarCuspEmbedding v) f) :
    u = cuspScalarPencilSolution ((1 / 4 : ℂ) - κ ^ 2) f :=
  cuspScalarPencilSolution_unique (cuspScalarPencil_isUnit_physical hκ) f u hu

/-- Physical parameter dependence is analytic in the actual form-operator norm. -/
theorem cuspScalarPencilSolution_analyticAt_physical {κ : ℂ} (hκ : 0 < κ.re) :
    AnalyticAt ℂ (fun k : ℂ => cuspScalarPencilSolution ((1 / 4 : ℂ) - k ^ 2)) κ := by
  have hi : AnalyticAt ℂ (fun k : ℂ => (1 / 4 : ℂ) - k ^ 2) κ := by fun_prop
  exact (cuspScalarPencilSolution_analyticAt (cuspScalarPencil_isUnit_physical hκ)).comp_of_eq
    hi rfl

end GapFamily.Analytic
