import GapFamily.Analytic.Cusp.Schur.CuspSchurGlobalPhysical
import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroPencilAnalytic
import GapFamily.Analytic.Cusp.Scalar.CuspScalarPencilAnalytic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Norm analyticity of the actual physical Schur inverse

The two constructed inverse pencils and the literal nonzero Schur denominator
supply analytic dependence of the actual form-valued solution and its value.
Every regularity premise is discharged throughout the physical half-plane,
except for the actual constant pole at κ=1/2.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchurPhysicalAnalytic
open ModularGradient CuspSchur

private theorem analyticAt_postcompose
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (P : F →L[ℂ] G) {A : ℂ → E →L[ℂ] F} {z : ℂ}
    (hA : AnalyticAt ℂ A z) : AnalyticAt ℂ (fun w => P.comp (A w)) z :=
  ((ContinuousLinearMap.compL ℂ E F G P).analyticAt _).comp hA

/-- The sum of the actual constrained and scalar form responses is norm analytic
where their actual inverse pencils are units. -/
theorem actualZeroTraceResponse_analyticAt {z : ℂ}
    (hV : IsUnit (cuspMeanZeroPencil z)) (hW : IsUnit (cuspScalarPencil z)) :
    AnalyticAt ℂ (fun w => zeroTraceResponse w (cuspScalarPencilSolution w)) z :=
  by
    let PV : (ModularHilbert →L[ℂ] cuspMeanZeroForm) →L[ℂ]
        (ModularHilbert →L[ℂ] FormDomain) :=
      ContinuousLinearMap.compL ℂ ModularHilbert cuspMeanZeroForm FormDomain cuspMeanZeroForm.subtypeL
    let PW : (ModularHilbert →L[ℂ] cuspScalarForm) →L[ℂ]
        (ModularHilbert →L[ℂ] FormDomain) :=
      ContinuousLinearMap.compL ℂ ModularHilbert cuspScalarForm FormDomain cuspScalarForm.subtypeL
    have hv := (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
      (E := ModularHilbert →L[ℂ] cuspMeanZeroForm) (F := ModularHilbert →L[ℂ] FormDomain)
      PV (cuspMeanZeroPencilSolution z)).comp_of_eq (cuspMeanZeroPencilSolution_analyticAt hV) rfl
    have hw := (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
      (E := ModularHilbert →L[ℂ] cuspScalarForm) (F := ModularHilbert →L[ℂ] FormDomain)
      PW (cuspScalarPencilSolution z)).comp_of_eq (cuspScalarPencilSolution_analyticAt hW) rfl
    exact hv.add hw

/-- Analyticity is for the literal full Schur denominator, not a surrogate. -/
theorem actualSchurDenominator_analyticAt {z : ℂ}
    (hV : IsUnit (cuspMeanZeroPencil z)) (hW : IsUnit (cuspScalarPencil z)) :
    AnalyticAt ℂ actualSchurDenominator z := by
  let B : FormDomain →L[ℂ] ℂ := (innerSL ℂ modularConstant).comp formEmbedding
  have hZ := actualZeroTraceResponse_analyticAt hV hW
  have hZc := ((ContinuousLinearMap.apply ℂ FormDomain modularConstant).analyticAt _).comp hZ
  have hB : AnalyticAt ℂ (fun w => inner ℂ modularConstant
      (formEmbedding (zeroTraceResponse w (cuspScalarPencilSolution w) modularConstant))) z :=
    (B.analyticAt _).comp hZc
  exact (analyticAt_id.neg.mul analyticAt_const).sub ((analyticAt_id.pow 2).mul hB)

/-- The source numerator is analytic in the norm of actual Hilbert functionals. -/
theorem actualSchurNumerator_analyticAt {z : ℂ}
    (hV : IsUnit (cuspMeanZeroPencil z)) (hW : IsUnit (cuspScalarPencil z)) :
    AnalyticAt ℂ (fun w => schurNumeratorMap w (cuspScalarPencilSolution w)) z := by
  have hZ := actualZeroTraceResponse_analyticAt hV hW
  have hB := analyticAt_postcompose (innerSL ℂ modularConstant)
    (analyticAt_postcompose formEmbedding hZ)
  exact analyticAt_const.add (analyticAt_id.smul hB)

/-- The actual completed-form Schur solution is norm analytic at every point
where both pencils are units and the actual denominator is nonzero. -/
theorem actualSchurSolution_analyticAt_of_units {z : ℂ}
    (hV : IsUnit (cuspMeanZeroPencil z)) (hW : IsUnit (cuspScalarPencil z))
    (hD : actualSchurDenominator z ≠ 0) : AnalyticAt ℂ actualSchurSolution z := by
  have hZ := actualZeroTraceResponse_analyticAt hV hW
  have hZc := ((ContinuousLinearMap.apply ℂ FormDomain modularConstant).analyticAt _).comp hZ
  have hq : AnalyticAt ℂ (fun w => constantForm +
      w • zeroTraceResponse w (cuspScalarPencilSolution w) modularConstant) z :=
    analyticAt_const.add (analyticAt_id.smul hZc)
  have hn := ((actualSchurDenominator_analyticAt hV hW).inv hD).smul
    (actualSchurNumerator_analyticAt hV hW)
  let M : (ModularHilbert →L[ℂ] ℂ) →L[ℂ] FormDomain →L[ℂ]
      (ModularHilbert →L[ℂ] FormDomain) := ContinuousLinearMap.smulRightL ℂ ModularHilbert FormDomain
  have hb := ContinuousLinearMap.analyticAt_bilinear (𝕜 := ℂ)
    (E := ModularHilbert →L[ℂ] ℂ) (F := FormDomain) (G := ModularHilbert →L[ℂ] FormDomain) M
    ((actualSchurDenominator z)⁻¹ • schurNumeratorMap z (cuspScalarPencilSolution z),
      constantForm + z • zeroTraceResponse z (cuspScalarPencilSolution z) modularConstant)
  have hr := hb.comp_of_eq (hn.prod hq) rfl
  exact hZ.add hr

/-- Bounded form embedding preserves the actual operator-norm analyticity. -/
theorem actualSchurResolvent_analyticAt_of_units {z : ℂ}
    (hV : IsUnit (cuspMeanZeroPencil z)) (hW : IsUnit (cuspScalarPencil z))
    (hD : actualSchurDenominator z ≠ 0) : AnalyticAt ℂ actualSchurResolvent z :=
  analyticAt_postcompose formEmbedding (actualSchurSolution_analyticAt_of_units hV hW hD)

/-- The actual full form-valued solution is analytic at every physical κ except
the constant eigenvalue pole. No source-dependent radius or regularity input occurs. -/
theorem actualSchurSolution_analyticAt_physical {κ : ℂ} (hκ : 0 < κ.re)
    (hhalf : κ ≠ (1 / 2 : ℂ)) :
    AnalyticAt ℂ (fun k => actualSchurSolution ((1 / 4 : ℂ) - k ^ 2)) κ := by
  obtain ⟨hV, hW, hD⟩ := CuspSchurGlobalPhysical.actualSchur_regular_physical hκ hhalf
  exact (actualSchurSolution_analyticAt_of_units hV hW hD).comp_of_eq
    (analyticAt_const.sub (analyticAt_id.pow 2)) rfl

/-- The actual physical inverse is analytic in the norm of operators on the
modular Hilbert space throughout Re κ>0, κ≠1/2. -/
theorem actualSchurResolvent_analyticAt_physical {κ : ℂ} (hκ : 0 < κ.re)
    (hhalf : κ ≠ (1 / 2 : ℂ)) :
    AnalyticAt ℂ (fun k => actualSchurResolvent ((1 / 4 : ℂ) - k ^ 2)) κ := by
  obtain ⟨hV, hW, hD⟩ := CuspSchurGlobalPhysical.actualSchur_regular_physical hκ hhalf
  exact (actualSchurResolvent_analyticAt_of_units hV hW hD).comp_of_eq
    (analyticAt_const.sub (analyticAt_id.pow 2)) rfl

/-- Norm analyticity holds on the entire actual physical region away from its pole. -/
theorem actualSchurSolution_analyticOnNhd_physical :
    AnalyticOnNhd ℂ (fun k => actualSchurSolution ((1 / 4 : ℂ) - k ^ 2))
      {κ : ℂ | 0 < κ.re ∧ κ ≠ (1 / 2 : ℂ)} :=
  fun _ hκ => actualSchurSolution_analyticAt_physical hκ.1 hκ.2

theorem actualSchurResolvent_analyticOnNhd_physical :
    AnalyticOnNhd ℂ (fun k => actualSchurResolvent ((1 / 4 : ℂ) - k ^ 2))
      {κ : ℂ | 0 < κ.re ∧ κ ≠ (1 / 2 : ℂ)} :=
  fun _ hκ => actualSchurResolvent_analyticAt_physical hκ.1 hκ.2

end GapFamily.Analytic.CuspSchurPhysicalAnalytic
