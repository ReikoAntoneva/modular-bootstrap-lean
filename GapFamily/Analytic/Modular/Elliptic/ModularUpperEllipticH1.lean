import GapFamily.Analytic.Modular.Elliptic.ModularUpperEllipticScalar
import GapFamily.Analytic.Modular.Elliptic.ModularEllipticH1

/-!
# Actual upper-chart Sobolev and Poisson data

The cutoff value and completed gradient satisfy the ordinary weak derivative
identities on every open plateau of the cutoff. Centered measure-preserving
charts turn these proved identities into actual H¹ and weak Poisson data,
including across modular seams. No regularity or PDE witness is an input.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set MeasureTheory Homogenization UpperHalfPlane
open scoped ContDiff

/-- Transport a compactly supported test integrand to ordinary plane volume. -/
theorem upperEllipticChart_test_integral (z : ℂ) (S : Set (Fin 2 → ℝ)) (g : ℂ → ℝ)
    (hz : ∀ v, v ∉ S → g (ellipticChart z v) = 0) :
    (∫ v in S, g (ellipticChart z v)) = ∫ w : ℂ, g w := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  exact (ellipticChart_measurePreserving z).integral_comp
    (ellipticChart z).toMeasurableEquiv.measurableEmbedding g

theorem upperEllipticChartTest_tsupport (z : ℂ) {φ : (Fin 2 → ℝ) → ℝ}
    {S : Set (Fin 2 → ℝ)} {U : Set ℂ} (hs : tsupport φ ⊆ S)
    (hSU : ellipticChart z '' S ⊆ U) : tsupport (ellipticChartTest z φ) ⊆ U := by
  rw [ellipticChartTest, tsupport_comp_eq_preimage φ (ellipticChart z).symm]
  intro w hw
  exact hSU ⟨(ellipticChart z).symm w, hs hw, (ellipticChart z).apply_symm_apply w⟩

theorem upperEllipticScalar_pullback_weak_x (L : ℂ →L[ℝ] ℝ)
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (u : laplacian.domain) (z : ℂ) {S : Set (Fin 2 → ℝ)}
    (hSU : ellipticChart z '' S ⊆ U) :
    HasWeakPartialDerivOn S 0
      (fun v => L (upperEllipticValue χ hχ hc hs u (ellipticChart z v)))
      (fun v => L (upperEllipticGradient χ hχ hc hs u 1 (ellipticChart z v))) := by
  intro φ hφ hcφ hsφ
  have hφ' : ContDiff ℝ ∞ φ := hφ
  have hψ := ellipticChartTest_contDiff z hφ'
  have hψc := ellipticChartTest_hasCompactSupport z hcφ
  have hψs := upperEllipticChartTest_tsupport z hsφ hSU
  have hleft := upperEllipticChart_test_integral z S
    (fun w => L (upperEllipticValue χ hχ hc hs u w) * fderiv ℝ (ellipticChartTest z φ) w 1)
    (by
      intro v hv
      rw [ellipticChartTest_fderiv_one z hφ' v,
        fderiv_of_notMem_tsupport ℝ (fun ht => hv (hsφ ht))]
      simp)
  have hright := upperEllipticChart_test_integral z S
    (fun w => L (upperEllipticGradient χ hχ hc hs u 1 w) * ellipticChartTest z φ w)
    (by
      intro v hv
      rw [ellipticChartTest_apply, image_eq_zero_of_notMem_tsupport (fun ht => hv (hsφ ht))]
      simp)
  simp only [ellipticChartTest_fderiv_one z hφ'] at hleft
  simp only [ellipticChartTest_apply] at hright
  rw [hleft, upperEllipticScalar_weak L χ hχ hc hs U hU hχU u _ hψ hψc hψs 1, hright]

theorem upperEllipticScalar_pullback_weak_y (L : ℂ →L[ℝ] ℝ)
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (u : laplacian.domain) (z : ℂ) {S : Set (Fin 2 → ℝ)}
    (hSU : ellipticChart z '' S ⊆ U) :
    HasWeakPartialDerivOn S 1
      (fun v => L (upperEllipticValue χ hχ hc hs u (ellipticChart z v)))
      (fun v => L (upperEllipticGradient χ hχ hc hs u Complex.I (ellipticChart z v))) := by
  intro φ hφ hcφ hsφ
  have hφ' : ContDiff ℝ ∞ φ := hφ
  have hψ := ellipticChartTest_contDiff z hφ'
  have hψc := ellipticChartTest_hasCompactSupport z hcφ
  have hψs := upperEllipticChartTest_tsupport z hsφ hSU
  have hleft := upperEllipticChart_test_integral z S
    (fun w => L (upperEllipticValue χ hχ hc hs u w) * fderiv ℝ (ellipticChartTest z φ) w Complex.I)
    (by
      intro v hv
      rw [ellipticChartTest_fderiv_I z hφ' v,
        fderiv_of_notMem_tsupport ℝ (fun ht => hv (hsφ ht))]
      simp)
  have hright := upperEllipticChart_test_integral z S
    (fun w => L (upperEllipticGradient χ hχ hc hs u Complex.I w) * ellipticChartTest z φ w)
    (by
      intro v hv
      rw [ellipticChartTest_apply, image_eq_zero_of_notMem_tsupport (fun ht => hv (hsφ ht))]
      simp)
  simp only [ellipticChartTest_fderiv_I z hφ'] at hleft
  simp only [ellipticChartTest_apply] at hright
  rw [hleft, upperEllipticScalar_weak L χ hχ hc hs U hU hχU u _ hψ hψc hψs Complex.I, hright]

/-- The actual cutoff value and its proved derivatives in a centered real chart. -/
def upperEllipticH1 (L : ℂ →L[ℝ] ℝ)
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (u : laplacian.domain) (z : ℂ) (S : Set (Fin 2 → ℝ))
    (hSU : ellipticChart z '' S ⊆ U) : H1Function S where
  toFun := fun v => L (upperEllipticValue χ hχ hc hs u (ellipticChart z v))
  grad := fun v => ![L (upperEllipticGradient χ hχ hc hs u 1 (ellipticChart z v)),
    L (upperEllipticGradient χ hχ hc hs u Complex.I (ellipticChart z v))]
  memL2 := ellipticScalar_pullback_memLp L z
    ((upperEllipticValue_memLp χ hχ hc hs u).restrict Set.univ) (subset_univ _)
  gradMemL2 := by
    intro i
    fin_cases i
    · exact ellipticScalar_pullback_memLp L z
        ((upperEllipticGradient_memLp χ hχ hc hs u 1).restrict Set.univ) (subset_univ _)
    · exact ellipticScalar_pullback_memLp L z
        ((upperEllipticGradient_memLp χ hχ hc hs u Complex.I).restrict Set.univ)
        (subset_univ _)
  hasWeakGradient := by
    intro i
    fin_cases i
    · exact upperEllipticScalar_pullback_weak_x L χ hχ hc hs U hU hχU u z hSU
    · exact upperEllipticScalar_pullback_weak_y L χ hχ hc hs U hU hχU u z hSU

@[simp] theorem upperEllipticH1_toFun (L : ℂ →L[ℝ] ℝ)
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (u : laplacian.domain) (z : ℂ) (S : Set (Fin 2 → ℝ))
    (hSU : ellipticChart z '' S ⊆ U) :
    (upperEllipticH1 L χ hχ hc hs U hU hχU u z S hSU).toFun =
      fun v => L (upperEllipticValue χ hχ hc hs u (ellipticChart z v)) := rfl

@[simp] theorem upperEllipticH1_grad (L : ℂ →L[ℝ] ℝ)
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (u : laplacian.domain) (z : ℂ) (S : Set (Fin 2 → ℝ))
    (hSU : ellipticChart z '' S ⊆ U) :
    (upperEllipticH1 L χ hχ hc hs U hU hχU u z S hSU).grad = fun v =>
      ![L (upperEllipticGradient χ hχ hc hs u 1 (ellipticChart z v)),
        L (upperEllipticGradient χ hχ hc hs u Complex.I (ellipticChart z v))] := rfl

theorem upperEllipticH1_source_memL2 (L : ℂ →L[ℝ] ℝ)
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hχU : EqOn χ (fun _ => 1) U)
    (u : laplacian.domain) (z : ℂ) {S : Set (Fin 2 → ℝ)} {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ U) (hSK : ellipticChart z '' S ⊆ K) :
    MemScalarL2 S (fun v => L (upperEllipticSource χ hχ hc hs u (ellipticChart z v))) :=
  ellipticScalar_pullback_memLp L z
    (upperEllipticSource_memLp_on_compact χ hχ hc hs u hK
      (hKU.trans (upperCutoff_plateau_subset_upperHalfPlane hs hχU))) hSK

/-- The actual divided modular source supplies the weak Poisson equation. -/
theorem upperEllipticH1_weakPoisson (L : ℂ →L[ℝ] ℝ)
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (u : laplacian.domain) (z : ℂ) (S : Set (Fin 2 → ℝ))
    (hSU : ellipticChart z '' S ⊆ U) :
    WeakPoissonEquationOn S (upperEllipticH1 L χ hχ hc hs U hU hχU u z S hSU)
      (fun v => L (upperEllipticSource χ hχ hc hs u (ellipticChart z v))) := by
  intro φ hφ hcφ hsφ
  have hφ' : ContDiff ℝ ∞ φ := hφ
  have hψ := ellipticChartTest_contDiff z hφ'
  have hψc := ellipticChartTest_hasCompactSupport z hcφ
  have hψs := upperEllipticChartTest_tsupport z hsφ hSU
  have hleft := upperEllipticChart_test_integral z S
    (fun w =>
      L (upperEllipticGradient χ hχ hc hs u 1 w) *
        fderiv ℝ (ellipticChartTest z φ) w 1 +
      L (upperEllipticGradient χ hχ hc hs u Complex.I w) *
        fderiv ℝ (ellipticChartTest z φ) w Complex.I)
    (by
      intro v hv
      rw [ellipticChartTest_fderiv_one z hφ' v, ellipticChartTest_fderiv_I z hφ' v,
        fderiv_of_notMem_tsupport ℝ (fun ht => hv (hsφ ht))]
      simp)
  have hright := upperEllipticChart_test_integral z S
    (fun w => L (upperEllipticSource χ hχ hc hs u w) * ellipticChartTest z φ w)
    (by
      intro v hv
      rw [ellipticChartTest_apply, image_eq_zero_of_notMem_tsupport (fun ht => hv (hsφ ht))]
      simp)
  simp only [ellipticChartTest_fderiv_one z hφ', ellipticChartTest_fderiv_I z hφ'] at hleft
  simp only [ellipticChartTest_apply] at hright
  simp only [upperEllipticH1_grad, vecDot, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, euclideanGradient, euclideanCoordDeriv]
  rw [hleft, upperEllipticScalar_poisson L χ hχ hc hs U hU hχU u _ hψ hψc hψs, hright]

end GapFamily.Analytic.ModularGradient
