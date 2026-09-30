import GapFamily.Analytic.Elliptic.LocalPoissonRegularityScalar
import GapFamily.Analytic.Modular.Elliptic.ModularUpperEllipticH1

/-! Centered real-chart Sobolev and Poisson data from an actual ordinary L² Poisson jet. -/
noncomputable section
namespace GapFamily.Analytic.LocalPoisson
open Set MeasureTheory Homogenization ModularGradient
open scoped ContDiff

theorem scalar_pullback_weak_x (L : ℂ →L[ℝ] ℝ)
    (U : Set ℂ)
    (u : JetSpace U) (z : ℂ) {S : Set (Fin 2 → ℝ)}
    (hSU : ellipticChart z '' S ⊆ U) :
    HasWeakPartialDerivOn S 0
      (fun v => L (valueCLM U u (ellipticChart z v)))
      (fun v => L (dxCLM U u (ellipticChart z v))) := by
  intro φ hφ hcφ hsφ
  have hφ' : ContDiff ℝ ∞ φ := hφ
  have hψ := ellipticChartTest_contDiff z hφ'
  have hψc := ellipticChartTest_hasCompactSupport z hcφ
  have hψs := upperEllipticChartTest_tsupport z hsφ hSU
  have hleft := upperEllipticChart_test_integral z S
    (fun w => L (valueCLM U u w) * fderiv ℝ (ellipticChartTest z φ) w 1)
    (by
      intro v hv
      rw [ellipticChartTest_fderiv_one z hφ' v,
        fderiv_of_notMem_tsupport ℝ (fun ht => hv (hsφ ht))]
      simp)
  have hright := upperEllipticChart_test_integral z S
    (fun w => L (dxCLM U u w) * ellipticChartTest z φ w)
    (by
      intro v hv
      rw [ellipticChartTest_apply, image_eq_zero_of_notMem_tsupport (fun ht => hv (hsφ ht))]
      simp)
  simp only [ellipticChartTest_fderiv_one z hφ'] at hleft
  simp only [ellipticChartTest_apply] at hright
  rw [hleft, scalar_weak_x L U u _ hψ hψc hψs, hright]

theorem scalar_pullback_weak_y (L : ℂ →L[ℝ] ℝ)
    (U : Set ℂ)
    (u : JetSpace U) (z : ℂ) {S : Set (Fin 2 → ℝ)}
    (hSU : ellipticChart z '' S ⊆ U) :
    HasWeakPartialDerivOn S 1
      (fun v => L (valueCLM U u (ellipticChart z v)))
      (fun v => L (dyCLM U u (ellipticChart z v))) := by
  intro φ hφ hcφ hsφ
  have hφ' : ContDiff ℝ ∞ φ := hφ
  have hψ := ellipticChartTest_contDiff z hφ'
  have hψc := ellipticChartTest_hasCompactSupport z hcφ
  have hψs := upperEllipticChartTest_tsupport z hsφ hSU
  have hleft := upperEllipticChart_test_integral z S
    (fun w => L (valueCLM U u w) * fderiv ℝ (ellipticChartTest z φ) w Complex.I)
    (by
      intro v hv
      rw [ellipticChartTest_fderiv_I z hφ' v,
        fderiv_of_notMem_tsupport ℝ (fun ht => hv (hsφ ht))]
      simp)
  have hright := upperEllipticChart_test_integral z S
    (fun w => L (dyCLM U u w) * ellipticChartTest z φ w)
    (by
      intro v hv
      rw [ellipticChartTest_apply, image_eq_zero_of_notMem_tsupport (fun ht => hv (hsφ ht))]
      simp)
  simp only [ellipticChartTest_fderiv_I z hφ'] at hleft
  simp only [ellipticChartTest_apply] at hright
  rw [hleft, scalar_weak_y L U u _ hψ hψc hψs, hright]

/-- The actual Poisson jet value and its proved derivatives in a centered real chart. -/
def chartH1 (L : ℂ →L[ℝ] ℝ)
    (U : Set ℂ)
    (u : JetSpace U) (z : ℂ) (S : Set (Fin 2 → ℝ))
    (hSU : ellipticChart z '' S ⊆ U) : H1Function S where
  toFun := fun v => L (valueCLM U u (ellipticChart z v))
  grad := fun v => ![L (dxCLM U u (ellipticChart z v)),
    L (dyCLM U u (ellipticChart z v))]
  memL2 := ellipticScalar_pullback_memLp L z
    ((Lp.memLp (valueCLM U u)).restrict Set.univ) (subset_univ _)
  gradMemL2 := by
    intro i
    fin_cases i
    · exact ellipticScalar_pullback_memLp L z
        ((Lp.memLp (dxCLM U u)).restrict Set.univ) (subset_univ _)
    · exact ellipticScalar_pullback_memLp L z
        ((Lp.memLp (dyCLM U u)).restrict Set.univ)
        (subset_univ _)
  hasWeakGradient := by
    intro i
    fin_cases i
    · exact scalar_pullback_weak_x L U u z hSU
    · exact scalar_pullback_weak_y L U u z hSU

@[simp] theorem chartH1_toFun (L : ℂ →L[ℝ] ℝ)
    (U : Set ℂ)
    (u : JetSpace U) (z : ℂ) (S : Set (Fin 2 → ℝ))
    (hSU : ellipticChart z '' S ⊆ U) :
    (chartH1 L U u z S hSU).toFun =
      fun v => L (valueCLM U u (ellipticChart z v)) := rfl

@[simp] theorem chartH1_grad (L : ℂ →L[ℝ] ℝ)
    (U : Set ℂ)
    (u : JetSpace U) (z : ℂ) (S : Set (Fin 2 → ℝ))
    (hSU : ellipticChart z '' S ⊆ U) :
    (chartH1 L U u z S hSU).grad = fun v =>
      ![L (dxCLM U u (ellipticChart z v)),
        L (dyCLM U u (ellipticChart z v))] := rfl

theorem chartH1_source_memL2 (L : ℂ →L[ℝ] ℝ)
    (U : Set ℂ) (u : JetSpace U) (z : ℂ) (S : Set (Fin 2 → ℝ)) :
    MemScalarL2 S (fun v => L (sourceCLM U u (ellipticChart z v))) :=
  ellipticScalar_pullback_memLp L z
    ((Lp.memLp (sourceCLM U u)).restrict Set.univ) (subset_univ _)

/-- The actual global L² jet source supplies the weak Poisson equation. -/
theorem chartH1_weakPoisson (L : ℂ →L[ℝ] ℝ)
    (U : Set ℂ)
    (u : JetSpace U) (z : ℂ) (S : Set (Fin 2 → ℝ))
    (hSU : ellipticChart z '' S ⊆ U) :
    WeakPoissonEquationOn S (chartH1 L U u z S hSU)
      (fun v => L (sourceCLM U u (ellipticChart z v))) := by
  intro φ hφ hcφ hsφ
  have hφ' : ContDiff ℝ ∞ φ := hφ
  have hψ := ellipticChartTest_contDiff z hφ'
  have hψc := ellipticChartTest_hasCompactSupport z hcφ
  have hψs := upperEllipticChartTest_tsupport z hsφ hSU
  have hleft := upperEllipticChart_test_integral z S
    (fun w =>
      L (dxCLM U u w) *
        fderiv ℝ (ellipticChartTest z φ) w 1 +
      L (dyCLM U u w) *
        fderiv ℝ (ellipticChartTest z φ) w Complex.I)
    (by
      intro v hv
      rw [ellipticChartTest_fderiv_one z hφ' v, ellipticChartTest_fderiv_I z hφ' v,
        fderiv_of_notMem_tsupport ℝ (fun ht => hv (hsφ ht))]
      simp)
  have hright := upperEllipticChart_test_integral z S
    (fun w => L (sourceCLM U u w) * ellipticChartTest z φ w)
    (by
      intro v hv
      rw [ellipticChartTest_apply, image_eq_zero_of_notMem_tsupport (fun ht => hv (hsφ ht))]
      simp)
  simp only [ellipticChartTest_fderiv_one z hφ', ellipticChartTest_fderiv_I z hφ'] at hleft
  simp only [ellipticChartTest_apply] at hright
  simp only [chartH1_grad, vecDot, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, euclideanGradient, euclideanCoordDeriv]
  rw [hleft, scalar_poisson L U u _ hψ hψc hψs, hright]

end GapFamily.Analytic.LocalPoisson
