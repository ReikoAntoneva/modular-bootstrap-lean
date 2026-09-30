import GapFamily.Analytic.Cusp.Scalar.CuspScalarForm
import GapFamily.Analytic.Cusp.Profile.CuspProfileNorm

/-!
# Horizontal gradient of the completed scalar cusp space

The actual compact profile generators have zero horizontal component. The
kernel of the bounded horizontal gradient map is closed, so the same identity
holds throughout the genuine completed scalar form space.
-/

noncomputable section
namespace GapFamily.Analytic
open ModularGradient

theorem cuspScalarForm_gradient_fst_eq_zero (w : cuspScalarForm) :
    (formGradient (w : FormDomain)).ofLp.1 = 0 := by
  let A : FormDomain →L[ℂ] ModularHilbert :=
    (WithLp.fstL 2 ℂ ModularHilbert ModularHilbert).comp formGradient
  have hW : cuspScalarForm ≤ A.ker := by
    apply cuspScalarForm_le_of_isClosed _ A.isClosed_ker
    intro b hb hc hs
    change (formGradient (coreForm (cuspProfileCore b hb hc hs))).ofLp.1 = 0
    rw [formGradient_coreForm, coreGradient_fst]
    exact cuspProfileCore_xComponent_eq_zero b hb hc hs
  exact hW w.property

end GapFamily.Analytic
