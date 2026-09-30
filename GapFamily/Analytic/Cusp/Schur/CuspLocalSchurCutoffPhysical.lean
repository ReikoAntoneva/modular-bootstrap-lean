import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurCutoff
import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurGradientPhysical
import GapFamily.Analytic.Cusp.Schur.CuspSchurNearThreshold
import GapFamily.Analytic.Modular.Geometry.ModularCutoffCoordinate

/-!
# Physical operator equation for the continued cutoff response

The height-restricted value and gradient fields reproduce the actual smooth
cutoff commutator. On one physical neighborhood, the two continued operator
families therefore lie in the graph of the true modular Laplacian for every
Hilbert source.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchurLocal
open ModularGradient ModularGradient.InteriorCutoff Set
open scoped ContDiff

theorem continuedCutoffSchur_eq_physical
    (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hH : tsupport χ ⊆ {z : ℂ | z.im ≤ Real.exp L})
    {κ : ℂ} (hκ : 0 < κ.re) (f : ModularHilbert) :
    continuedCutoffSchur χ hχ hc L T κ f = valueMultiplier χ hχ hc
      (CuspSchur.actualSchurResolvent (parameter κ) (modularLowCut (Real.exp T) f)) := by
  rw [continuedCutoffSchur, continuedLocalSchur_eq_physical hL hT hκ]
  simp only [ContinuousLinearMap.comp_apply]
  exact valueMultiplier_lowCut χ hχ hc (Real.exp L) hH _

theorem continuedCutoffLaplacian_eq_commutatorValue
    (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hH : tsupport χ ⊆ {z : ℂ | z.im ≤ Real.exp L})
    {κ : ℂ} (hκ : 0 < κ.re) (f : ModularHilbert)
    (hu : CuspSchur.actualSchurResolvent (parameter κ)
      (modularLowCut (Real.exp T) f) ∈ laplacian.domain)
    (hAu : laplacian ⟨CuspSchur.actualSchurResolvent (parameter κ)
        (modularLowCut (Real.exp T) f), hu⟩ -
      parameter κ • CuspSchur.actualSchurResolvent (parameter κ)
        (modularLowCut (Real.exp T) f) = modularLowCut (Real.exp T) f) :
    continuedCutoffLaplacian χ hχ hc L T κ f = commutatorValue χ hχ hc
      ⟨CuspSchur.actualSchurResolvent (parameter κ) (modularLowCut (Real.exp T) f), hu⟩ := by
  let u : laplacian.domain :=
    ⟨CuspSchur.actualSchurResolvent (parameter κ) (modularLowCut (Real.exp T) f), hu⟩
  have hform : operatorForm u =
      CuspSchur.actualSchurSolution (parameter κ) (modularLowCut (Real.exp T) f) := by
    apply formEmbedding_injective
    rfl
  have hA : laplacian u = modularLowCut (Real.exp T) f + parameter κ • (u : ModularHilbert) :=
    sub_eq_iff_eq_add.mp hAu
  have hx := continuedLocalSchurGradientX_apply_eq_physical (L := L) hT hκ f
  have hy := continuedLocalSchurGradientY_apply_eq_physical hL hT hκ f
  simp only [continuedCutoffLaplacian, add_apply,
    sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply]
  rw [continuedCutoffSchur_eq_physical χ hχ hc hL hT hH hκ f,
    continuedLocalSchur_eq_physical hL hT hκ]
  simp only [ContinuousLinearMap.comp_apply,
    secondMultiplier_lowCut χ hχ hc 1 (Real.exp L) hH,
    secondMultiplier_lowCut χ hχ hc Complex.I (Real.exp L) hH]
  rw [hx, hy, derivativeMultiplier_lowCut χ hχ hc 1 (Real.exp L) hH,
    derivativeMultiplier_lowCut χ hχ hc Complex.I (Real.exp L) hH]
  change _ = commutatorValue χ hχ hc u
  rw [commutatorValue, hA, map_add, map_smul, hform]
  abel

/-- A source-independent physical neighborhood satisfies the actual graph equation. -/
theorem exists_radius_continuedCutoff_graph_physical
    (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ modularInterior)
    {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hH : tsupport χ ⊆ {z : ℂ | z.im ≤ Real.exp L}) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ κ : ℂ, ‖κ‖ < ε → 0 < κ.re →
      ∀ f : ModularHilbert,
        (continuedCutoffSchur χ hχ hc L T κ f,
         continuedCutoffLaplacian χ hχ hc L T κ f) ∈ laplacian.graph := by
  obtain ⟨ε, hε, hphysical⟩ := CuspSchur.exists_radius_actualSchur_inverse_physical
  refine ⟨ε, hε, ?_⟩
  intro κ hnorm hκ f
  obtain ⟨hu, hAu⟩ := (hphysical κ hnorm hκ).1 (modularLowCut (Real.exp T) f)
  let u : laplacian.domain :=
    ⟨CuspSchur.actualSchurResolvent (parameter κ) (modularLowCut (Real.exp T) f), hu⟩
  have hv := continuedCutoffSchur_eq_physical χ hχ hc hL hT hH hκ f
  have hA := continuedCutoffLaplacian_eq_commutatorValue χ hχ hc hL hT hH hκ f hu hAu
  rw [hv, hA]
  change (valueMultiplier χ hχ hc u, commutatorValue χ hχ hc u) ∈ laplacian.graph
  rw [← operatorCutoff_value χ hχ hc hs u]
  have hop : laplacian (operatorCutoff χ hχ hc hs u) = commutatorValue χ hχ hc u :=
    laplacian_formMultiplier χ hχ hc hs u
  rw [← hop]
  exact laplacian.mem_graph _

end GapFamily.Analytic.CuspSchurLocal
