import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroGlobalUnit
import GapFamily.Analytic.Cusp.Schur.CuspSchurGlobalDenominator

noncomputable section
namespace GapFamily.Analytic.CuspSchurGlobalPhysical
open ModularGradient ModularProjected CuspSchur

/-- The literal Schur denominator never vanishes in the physical half-plane
away from the actual constant eigenvalue at κ=1/2. -/
theorem actualSchurDenominator_ne_zero_physical {κ : ℂ} (hκ : 0 < κ.re)
    (hhalf : κ ≠ (1 / 2 : ℂ)) :
    actualSchurDenominator ((1 / 4 : ℂ) - κ ^ 2) ≠ 0 :=
  actualSchurDenominator_ne_zero_of_projected_units
    (CuspMeanZeroGlobalUnit.cuspMeanZeroPencil_isUnit_physical hκ)
    (cuspScalarPencil_isUnit_physical hκ) (projectedPencil_isUnit_physical hκ)
    (physical_parameter_ne_zero hκ hhalf)

/-- Every regularity premise of the actual Schur construction is discharged
on the entire physical parameter region, not just near threshold. -/
theorem actualSchur_regular_physical {κ : ℂ} (hκ : 0 < κ.re) (hhalf : κ ≠ (1 / 2 : ℂ)) :
    IsUnit (cuspMeanZeroPencil ((1 / 4 : ℂ) - κ ^ 2)) ∧
      IsUnit (cuspScalarPencil ((1 / 4 : ℂ) - κ ^ 2)) ∧
      actualSchurDenominator ((1 / 4 : ℂ) - κ ^ 2) ≠ 0 :=
  ⟨CuspMeanZeroGlobalUnit.cuspMeanZeroPencil_isUnit_physical hκ,
    cuspScalarPencil_isUnit_physical hκ, actualSchurDenominator_ne_zero_physical hκ hhalf⟩

/-- The actual full completed-form Schur response solves the literal weak equation. -/
theorem actualSchurSolution_equation_physical {κ : ℂ} (hκ : 0 < κ.re)
    (hhalf : κ ≠ (1 / 2 : ℂ)) (f : ModularHilbert) (t : FormDomain) :
    inner ℂ (formGradient t)
        (formGradient (actualSchurSolution ((1 / 4 : ℂ) - κ ^ 2) f)) -
      ((1 / 4 : ℂ) - κ ^ 2) * inner ℂ (formEmbedding t)
        (actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2) f) = inner ℂ (formEmbedding t) f := by
  obtain ⟨hV, hW, hD⟩ := actualSchur_regular_physical hκ hhalf
  exact actualSchurSolution_equation_of_units hV hW hD f t

/-- Uniqueness holds in the actual full form domain throughout the physical region. -/
theorem actualSchurSolution_unique_physical {κ : ℂ} (hκ : 0 < κ.re)
    (hhalf : κ ≠ (1 / 2 : ℂ)) (f : ModularHilbert) (u : FormDomain)
    (hu : ∀ t : FormDomain, inner ℂ (formGradient t) (formGradient u) -
      ((1 / 4 : ℂ) - κ ^ 2) * inner ℂ (formEmbedding t) (formEmbedding u) =
        inner ℂ (formEmbedding t) f) :
    u = actualSchurSolution ((1 / 4 : ℂ) - κ ^ 2) f := by
  obtain ⟨hV, hW, hD⟩ := actualSchur_regular_physical hκ hhalf
  exact actualSchurSolution_unique_of_units hV hW hD f u hu

/-- Every physical Schur value lies in the actual closed modular Laplacian domain. -/
theorem actualSchurResolvent_mem_domain_physical {κ : ℂ} (hκ : 0 < κ.re)
    (hhalf : κ ≠ (1 / 2 : ℂ)) (f : ModularHilbert) :
    actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2) f ∈ laplacian.domain := by
  obtain ⟨hV, hW, hD⟩ := actualSchur_regular_physical hκ hhalf
  exact actualSchurResolvent_mem_domain_of_units hV hW hD f

/-- The actual bounded Schur map is a full right inverse of A−(1/4−κ²). -/
theorem actualSchurResolvent_rightInverse_physical {κ : ℂ} (hκ : 0 < κ.re)
    (hhalf : κ ≠ (1 / 2 : ℂ)) (f : ModularHilbert) :
    laplacian ⟨actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2) f,
      actualSchurResolvent_mem_domain_physical hκ hhalf f⟩ -
        ((1 / 4 : ℂ) - κ ^ 2) • actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2) f = f := by
  obtain ⟨hV, hW, hD⟩ := actualSchur_regular_physical hκ hhalf
  exact actualSchurResolvent_rightInverse_of_units hV hW hD f

/-- The same map is a left inverse on every vector in the actual operator domain. -/
theorem actualSchurResolvent_leftInverse_physical {κ : ℂ} (hκ : 0 < κ.re)
    (hhalf : κ ≠ (1 / 2 : ℂ)) (x : laplacian.domain) :
    actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2)
      (laplacian x - ((1 / 4 : ℂ) - κ ^ 2) • (x : ModularHilbert)) = x := by
  obtain ⟨hV, hW, hD⟩ := actualSchur_regular_physical hκ hhalf
  exact actualSchurResolvent_leftInverse_of_units hV hW hD x

/-- The two independently constructed actual full inverses agree everywhere
in the physical half-plane except the constant pole. -/
theorem fullResolvent_eq_actualSchurResolvent_physical {κ : ℂ} (hκ : 0 < κ.re)
    (hhalf : κ ≠ (1 / 2 : ℂ)) :
    fullResolvent ((1 / 4 : ℂ) - κ ^ 2) = actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2) := by
  obtain ⟨hV, hW, hD⟩ := actualSchur_regular_physical hκ hhalf
  exact CuspSchurLocal.fullResolvent_eq_actualSchurResolvent_of_units
    (projectedPencil_isUnit_physical hκ) (physical_parameter_ne_zero hκ hhalf) hV hW hD

end GapFamily.Analytic.CuspSchurGlobalPhysical
