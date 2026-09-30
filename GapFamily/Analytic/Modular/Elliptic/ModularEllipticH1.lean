import GapFamily.Analytic.Modular.Elliptic.ModularEllipticScalar
import GapFamily.Analytic.Modular.Elliptic.ModularEllipticChart
import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior

/-!
# Actual modular H¹ and weak Poisson data in a centered real chart

The value, gradient, and forcing are the actual modular representatives. Their
ordinary local L² bounds and weak equations are transported through the centered
volume-preserving chart. No Sobolev or Poisson witness is an input.

The pinned vendored elliptic proof supplies the H1Function and
WeakPoissonEquationOn interfaces used by the actual weak-Hessian application.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set MeasureTheory Homogenization
open scoped ContDiff

/-- Transport a supported integrand through the actual centered volume chart. -/
theorem ellipticChart_test_integral (z : ℂ) (U : Set (Fin 2 → ℝ)) (g : ℂ → ℝ)
    (hU : ellipticChart z '' U ⊆ modularInterior)
    (hz : ∀ v, v ∉ U → g (ellipticChart z v) = 0) :
    (∫ v in U, g (ellipticChart z v)) = ∫ w in modularInterior, g w := by
  have hg : ∀ w, w ∉ modularInterior → g w = 0 := by
    intro w hw
    have hv : (ellipticChart z).symm w ∉ U := by
      intro hv
      apply hw
      apply hU
      exact ⟨(ellipticChart z).symm w, hv, (ellipticChart z).apply_symm_apply w⟩
    simpa only [Homeomorph.apply_symm_apply] using hz ((ellipticChart z).symm w) hv
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    setIntegral_eq_integral_of_forall_compl_eq_zero hg]
  exact (ellipticChart_measurePreserving z).integral_comp
    (ellipticChart z).toMeasurableEquiv.measurableEmbedding g

def ellipticChartTest (z : ℂ) (φ : (Fin 2 → ℝ) → ℝ) : ℂ → ℝ :=
  φ ∘ (ellipticChart z).symm

@[simp] theorem ellipticChartTest_apply (z : ℂ) (φ : (Fin 2 → ℝ) → ℝ)
    (v : Fin 2 → ℝ) : ellipticChartTest z φ (ellipticChart z v) = φ v := by
  simp only [ellipticChartTest, Function.comp_apply, Homeomorph.symm_apply_apply]

theorem ellipticChartTest_contDiff (z : ℂ) {φ : (Fin 2 → ℝ) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (ellipticChartTest z φ) :=
  hφ.comp (ellipticChart_symm_contDiff z)

theorem ellipticChartTest_hasCompactSupport (z : ℂ) {φ : (Fin 2 → ℝ) → ℝ}
    (hc : HasCompactSupport φ) : HasCompactSupport (ellipticChartTest z φ) :=
  hc.comp_homeomorph (ellipticChart z).symm

theorem ellipticChartTest_tsupport (z : ℂ) {φ : (Fin 2 → ℝ) → ℝ}
    {U : Set (Fin 2 → ℝ)} (hs : tsupport φ ⊆ U)
    (hU : ellipticChart z '' U ⊆ modularInterior) :
    tsupport (ellipticChartTest z φ) ⊆ modularInterior := by
  rw [ellipticChartTest, tsupport_comp_eq_preimage φ (ellipticChart z).symm]
  intro w hw
  exact hU ⟨(ellipticChart z).symm w, hs hw, (ellipticChart z).apply_symm_apply w⟩

theorem ellipticChartTest_fderiv_one (z : ℂ) {φ : (Fin 2 → ℝ) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (v : Fin 2 → ℝ) :
    fderiv ℝ (ellipticChartTest z φ) (ellipticChart z v) 1 =
      fderiv ℝ φ v (basisVec 0) := by
  rw [ellipticChartTest, fderiv_comp _
    (hφ.differentiable (by simp)).differentiableAt
    ((ellipticChart_symm_contDiff z).differentiable (by simp)).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply, ellipticChart_symm_fderiv_one,
    Homeomorph.symm_apply_apply, basisVec]

theorem ellipticChartTest_fderiv_I (z : ℂ) {φ : (Fin 2 → ℝ) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (v : Fin 2 → ℝ) :
    fderiv ℝ (ellipticChartTest z φ) (ellipticChart z v) Complex.I =
      fderiv ℝ φ v (basisVec 1) := by
  rw [ellipticChartTest, fderiv_comp _
    (hφ.differentiable (by simp)).differentiableAt
    ((ellipticChart_symm_contDiff z).differentiable (by simp)).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply, ellipticChart_symm_fderiv_I,
    Homeomorph.symm_apply_apply, basisVec]

theorem ellipticScalar_pullback_memLp (L : ℂ →L[ℝ] ℝ) (z : ℂ)
    {U : Set (Fin 2 → ℝ)} {K : Set ℂ} {f : ℂ → ℂ}
    (hf : MemLp f 2 (volume.restrict K)) (hUK : ellipticChart z '' U ⊆ K) :
    MemLp (fun v => L (f (ellipticChart z v))) 2 (volume.restrict U) := by
  apply (memLp_comp_ellipticChart_image_iff z U (fun w => L (f w)) 2).mpr
  exact (L.comp_memLp' hf).mono_measure (Measure.restrict_mono_set volume hUK)

theorem ellipticScalar_pullback_weak_x (L : ℂ →L[ℝ] ℝ)
    (u : closedGradient.domain) (z : ℂ) {U : Set (Fin 2 → ℝ)}
    (hU : ellipticChart z '' U ⊆ modularInterior) :
    HasWeakPartialDerivOn U 0
      (fun v => L (coordinateValue u (ellipticChart z v)))
      (fun v => L (coordinateDx u (ellipticChart z v))) := by
  intro φ hφ hc hs
  have hφ' : ContDiff ℝ ∞ φ := hφ
  have hψ := ellipticChartTest_contDiff z hφ'
  have hψc := ellipticChartTest_hasCompactSupport z hc
  have hψs := ellipticChartTest_tsupport z hs hU
  have hleft := ellipticChart_test_integral z U
    (fun w => L (coordinateValue u w) * fderiv ℝ (ellipticChartTest z φ) w 1) hU
    (by
      intro v hv
      rw [ellipticChartTest_fderiv_one z hφ' v,
        fderiv_of_notMem_tsupport ℝ (fun ht => hv (hs ht))]
      simp)
  have hright := ellipticChart_test_integral z U
    (fun w => L (coordinateDx u w) * ellipticChartTest z φ w) hU
    (by
      intro v hv
      rw [ellipticChartTest_apply, image_eq_zero_of_notMem_tsupport (fun ht => hv (hs ht))]
      simp)
  simp only [ellipticChartTest_fderiv_one z hφ'] at hleft
  simp only [ellipticChartTest_apply] at hright
  rw [hleft, ellipticScalar_weak_x L u _ hψ hψc hψs, hright]

theorem ellipticScalar_pullback_weak_y (L : ℂ →L[ℝ] ℝ)
    (u : closedGradient.domain) (z : ℂ) {U : Set (Fin 2 → ℝ)}
    (hU : ellipticChart z '' U ⊆ modularInterior) :
    HasWeakPartialDerivOn U 1
      (fun v => L (coordinateValue u (ellipticChart z v)))
      (fun v => L (coordinateDy u (ellipticChart z v))) := by
  intro φ hφ hc hs
  have hφ' : ContDiff ℝ ∞ φ := hφ
  have hψ := ellipticChartTest_contDiff z hφ'
  have hψc := ellipticChartTest_hasCompactSupport z hc
  have hψs := ellipticChartTest_tsupport z hs hU
  have hleft := ellipticChart_test_integral z U
    (fun w => L (coordinateValue u w) * fderiv ℝ (ellipticChartTest z φ) w Complex.I) hU
    (by
      intro v hv
      rw [ellipticChartTest_fderiv_I z hφ' v,
        fderiv_of_notMem_tsupport ℝ (fun ht => hv (hs ht))]
      simp)
  have hright := ellipticChart_test_integral z U
    (fun w => L (coordinateDy u w) * ellipticChartTest z φ w) hU
    (by
      intro v hv
      rw [ellipticChartTest_apply, image_eq_zero_of_notMem_tsupport (fun ht => hv (hs ht))]
      simp)
  simp only [ellipticChartTest_fderiv_I z hφ'] at hleft
  simp only [ellipticChartTest_apply] at hright
  rw [hleft, ellipticScalar_weak_y L u _ hψ hψc hψs, hright]

/-- The actual modular value and its proved weak derivatives, in real coordinates. -/
def ellipticH1 (L : ℂ →L[ℝ] ℝ) (u : laplacian.domain) (z : ℂ)
    (U : Set (Fin 2 → ℝ)) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ modularInterior) (hUK : ellipticChart z '' U ⊆ K) : H1Function U where
  toFun := fun v => L (coordinateValue ⟨u, laplacian_domain_le u.property⟩ (ellipticChart z v))
  grad := fun v => ![L (coordinateDx ⟨u, laplacian_domain_le u.property⟩ (ellipticChart z v)),
    L (coordinateDy ⟨u, laplacian_domain_le u.property⟩ (ellipticChart z v))]
  memL2 := ellipticScalar_pullback_memLp L z
    (laplacian_coordinate_fields_memLp_on_compact u hK hKU).1 hUK
  gradMemL2 := by
    intro i
    fin_cases i
    · exact ellipticScalar_pullback_memLp L z
        (laplacian_coordinate_fields_memLp_on_compact u hK hKU).2.1 hUK
    · exact ellipticScalar_pullback_memLp L z
        (laplacian_coordinate_fields_memLp_on_compact u hK hKU).2.2.1 hUK
  hasWeakGradient := by
    intro i
    fin_cases i
    · exact ellipticScalar_pullback_weak_x L ⟨u, laplacian_domain_le u.property⟩ z (hUK.trans hKU)
    · exact ellipticScalar_pullback_weak_y L ⟨u, laplacian_domain_le u.property⟩ z (hUK.trans hKU)

@[simp] theorem ellipticH1_toFun (L : ℂ →L[ℝ] ℝ) (u : laplacian.domain) (z : ℂ)
    (U : Set (Fin 2 → ℝ)) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ modularInterior) (hUK : ellipticChart z '' U ⊆ K) :
    (ellipticH1 L u z U hK hKU hUK).toFun =
      fun v => L (coordinateValue ⟨u, laplacian_domain_le u.property⟩ (ellipticChart z v)) := rfl

@[simp] theorem ellipticH1_grad (L : ℂ →L[ℝ] ℝ) (u : laplacian.domain) (z : ℂ)
    (U : Set (Fin 2 → ℝ)) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ modularInterior) (hUK : ellipticChart z '' U ⊆ K) :
    (ellipticH1 L u z U hK hKU hUK).grad = fun v =>
      ![L (coordinateDx ⟨u, laplacian_domain_le u.property⟩ (ellipticChart z v)),
        L (coordinateDy ⟨u, laplacian_domain_le u.property⟩ (ellipticChart z v))] := rfl

theorem ellipticH1_source_memL2 (L : ℂ →L[ℝ] ℝ) (u : laplacian.domain) (z : ℂ)
    {U : Set (Fin 2 → ℝ)} {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ modularInterior) (hUK : ellipticChart z '' U ⊆ K) :
    MemScalarL2 U (fun v => L (coordinateSource u (ellipticChart z v))) :=
  ellipticScalar_pullback_memLp L z
    (laplacian_coordinate_fields_memLp_on_compact u hK hKU).2.2.2 hUK

/-- The actual divided operator source drives the chartwise weak Poisson equation. -/
theorem ellipticH1_weakPoisson (L : ℂ →L[ℝ] ℝ) (u : laplacian.domain) (z : ℂ)
    (U : Set (Fin 2 → ℝ)) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ modularInterior) (hUK : ellipticChart z '' U ⊆ K) :
    WeakPoissonEquationOn U (ellipticH1 L u z U hK hKU hUK)
      (fun v => L (coordinateSource u (ellipticChart z v))) := by
  intro φ hφ hc hs
  have hφ' : ContDiff ℝ ∞ φ := hφ
  have hU := hUK.trans hKU
  have hψ := ellipticChartTest_contDiff z hφ'
  have hψc := ellipticChartTest_hasCompactSupport z hc
  have hψs := ellipticChartTest_tsupport z hs hU
  have hleft := ellipticChart_test_integral z U
    (fun w =>
      L (coordinateDx ⟨u, laplacian_domain_le u.property⟩ w) *
        fderiv ℝ (ellipticChartTest z φ) w 1 +
      L (coordinateDy ⟨u, laplacian_domain_le u.property⟩ w) *
        fderiv ℝ (ellipticChartTest z φ) w Complex.I) hU
    (by
      intro v hv
      rw [ellipticChartTest_fderiv_one z hφ' v, ellipticChartTest_fderiv_I z hφ' v,
        fderiv_of_notMem_tsupport ℝ (fun ht => hv (hs ht))]
      simp)
  have hright := ellipticChart_test_integral z U
    (fun w => L (coordinateSource u w) * ellipticChartTest z φ w) hU
    (by
      intro v hv
      rw [ellipticChartTest_apply, image_eq_zero_of_notMem_tsupport (fun ht => hv (hs ht))]
      simp)
  simp only [ellipticChartTest_fderiv_one z hφ', ellipticChartTest_fderiv_I z hφ'] at hleft
  simp only [ellipticChartTest_apply] at hright
  simp only [ellipticH1_grad, vecDot, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, euclideanGradient, euclideanCoordDeriv]
  rw [hleft, ellipticScalar_poisson L u _ hψ hψc hψs, hright]

end GapFamily.Analytic.ModularGradient
