import GapFamily.Analytic.Cusp.Scalar.CuspScalarFormBasic
import GapFamily.Analytic.Cusp.Scalar.CuspScalarFormTrace
import GapFamily.Analytic.Cusp.Scalar.CuspScalarFormProjection

/-!
# Trace and orthogonality of the actual closed scalar cusp form space

The trace, mass and energy assertions hold first for the genuine compact
profile generators. Kernels of actual continuous linear maps are closed,
so these assertions pass to their span and closure in the completed form norm.
-/

noncomputable section

namespace GapFamily.Analytic

open Set ModularGradient
open scoped ContDiff

/-- The actual scalar form space has zero ordinary cusp-average boundary trace. -/
theorem cuspScalarForm_le_trace_ker : cuspScalarForm ≤ cuspAverageTrace.ker := by
  apply cuspScalarForm_le_of_isClosed _ cuspAverageTrace.isClosed_ker
  intro b hb hc hs
  exact cuspAverageTrace_cuspProfileCore b hb hc hs

@[simp] theorem cuspScalarForm_trace (w : cuspScalarForm) :
    cuspAverageTrace (w : FormDomain) = 0 :=
  cuspScalarForm_le_trace_ker w.property

/-- The literal ambient scalar cusp projection fixes every completed scalar form value. -/
theorem cuspScalarProjection_formEmbedding (w : cuspScalarForm) :
    cuspScalarProjection (formEmbedding (w : FormDomain)) = formEmbedding (w : FormDomain) := by
  let A : FormDomain →L[ℂ] ModularHilbert :=
    cuspScalarProjection.comp formEmbedding - formEmbedding
  have hW : cuspScalarForm ≤ A.ker := by
    apply cuspScalarForm_le_of_isClosed _ A.isClosed_ker
    intro b hb hc hs
    change cuspScalarProjection (formEmbedding (coreForm (cuspProfileCore b hb hc hs))) -
      formEmbedding (coreForm (cuspProfileCore b hb hc hs)) = 0
    rw [formEmbedding_coreForm, cuspScalarProjection_cuspProfileCore, sub_self]
  have h := hW w.property
  change cuspScalarProjection (formEmbedding (w : FormDomain)) -
    formEmbedding (w : FormDomain) = 0 at h
  exact sub_eq_zero.mp h

@[simp] theorem cuspScalarProjection_scalarCuspEmbedding (w : cuspScalarForm) :
    cuspScalarProjection (scalarCuspEmbedding w) = scalarCuspEmbedding w :=
  cuspScalarProjection_formEmbedding w

/-- The same actual ambient projection annihilates every zero-average cusp form value. -/
@[simp] theorem cuspScalarProjection_meanZeroCuspEmbedding (u : cuspMeanZeroForm) :
    cuspScalarProjection (meanZeroCuspEmbedding u) = 0 := by
  rw [cuspScalarProjection_apply, meanZeroCusp_average_eq_zero 1 le_rfl u]
  exact map_zero (cuspZeroExtension 1)

/-- Every completed scalar cusp form value is mass-orthogonal to every
completed zero-average cusp form value. -/
theorem cuspScalarForm_mass_orthogonal (w : cuspScalarForm) (u : cuspMeanZeroForm) :
    inner ℂ (scalarCuspEmbedding w) (meanZeroCuspEmbedding u) = 0 := by
  let A : FormDomain →L[ℂ] ℂ := (innerSL ℂ (meanZeroCuspEmbedding u)).comp formEmbedding
  have hW : cuspScalarForm ≤ A.ker := by
    apply cuspScalarForm_le_of_isClosed _ A.isClosed_ker
    intro b hb hc hs
    change inner ℂ (meanZeroCuspEmbedding u)
      (formEmbedding (coreForm (cuspProfileCore b hb hc hs))) = 0
    rw [formEmbedding_coreForm, inner_eq_zero_symm]
    exact cuspProfileCore_mass_orthogonal b hb hc hs u
  have h := hW w.property
  change inner ℂ (meanZeroCuspEmbedding u) (scalarCuspEmbedding w) = 0 at h
  exact inner_eq_zero_symm.mp h

/-- Orthogonality holds also for the genuine closed gradients, not just for
their ambient values. -/
theorem cuspScalarForm_energy_orthogonal (w : cuspScalarForm) (u : cuspMeanZeroForm) :
    inner ℂ (formGradient (w : FormDomain)) (cuspMeanZeroGradient u) = 0 := by
  let A : FormDomain →L[ℂ] ℂ := (innerSL ℂ (cuspMeanZeroGradient u)).comp formGradient
  have hW : cuspScalarForm ≤ A.ker := by
    apply cuspScalarForm_le_of_isClosed _ A.isClosed_ker
    intro b hb hc hs
    change inner ℂ (cuspMeanZeroGradient u)
      (formGradient (coreForm (cuspProfileCore b hb hc hs))) = 0
    rw [formGradient_coreForm, inner_eq_zero_symm]
    exact cuspProfileCore_energy_orthogonal b hb hc hs u
  have h := hW w.property
  change inner ℂ (cuspMeanZeroGradient u) (formGradient (w : FormDomain)) = 0 at h
  exact inner_eq_zero_symm.mp h

/-- The two actual cusp form subspaces have trivial intersection. -/
theorem disjoint_cuspMeanZeroForm_cuspScalarForm : Disjoint cuspMeanZeroForm cuspScalarForm := by
  apply disjoint_iff_inf_le.mpr
  intro u hu
  change u = 0
  apply formEmbedding_injective
  rw [map_zero]
  have hfix := cuspScalarProjection_formEmbedding ⟨u, hu.2⟩
  have hzero := cuspScalarProjection_meanZeroCuspEmbedding ⟨u, hu.1⟩
  exact hfix.symm.trans hzero

end GapFamily.Analytic
