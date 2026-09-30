import GapFamily.Analytic.Poincare.PoincareHighCuspLift
import GapFamily.Analytic.Cusp.CuspPoincareComplementFD

/-! The actual high-cusp lift completes the actual convergent complement series. -/
noncomputable section
namespace GapFamily.Analytic.PoincareHighCusp
open Set UpperHalfPlane CuspFourierCutoff
open scoped Topology MatrixGroups

/-- Global equality with the two independently constructed actual modular terms. -/
theorem complexPoincareSeries_eq_complement_add_highCusp (J : ℤ) {s : ℂ}
    (hs : 1 < s.re) (τ : UpperHalfPlane) :
    complexPoincareSeries 0 J s τ = PoincareComplement.series J s τ + highCuspLift J s τ := by
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
  have hcomp := PoincareComplement.series_eq_residual_of_mem_fd J hs hγ
  have hlift := highCuspLift_eq_on_fd J s hγ
  have heq : complexPoincareSeries 0 J s (γ • τ) =
      PoincareComplement.series J s (γ • τ) + highCuspLift J s (γ • τ : UpperHalfPlane) := by
    rw [hcomp, hlift]
    abel
  simpa only [complexPoincareSeries_smul, PoincareComplement.series_smul,
    highCuspLift_smul] using heq

/-- The requested κ-family has the same exact decomposition on the common
absolute-convergence region Re(1/2+κ)>1. -/
theorem complexPoincareSeries_eq_complement_add_continuedHighCusp (J : ℤ) {κ : ℂ}
    (hκ : 1 < (exponent κ).re) (τ : UpperHalfPlane) :
    complexPoincareSeries 0 J (exponent κ) τ =
      PoincareComplement.series J (exponent κ) τ + continuedHighCusp J κ τ :=
  complexPoincareSeries_eq_complement_add_highCusp J hκ τ

end GapFamily.Analytic.PoincareHighCusp
