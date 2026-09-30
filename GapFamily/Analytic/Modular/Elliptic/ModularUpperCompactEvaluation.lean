import GapFamily.Analytic.Modular.Elliptic.ModularUpperEvaluation
import GapFamily.Analytic.Modular.Elliptic.ModularUpperEvaluationCutoff

/-!
# Bounded evaluation on arbitrary compact upper-half-plane sets

The compact observation set needs no interior. A larger regular compact chart
provides the graph-norm bound, and ordinary restriction gives the actual
continuous representative on the requested observation set.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set Filter MeasureTheory Dirichlet UpperHalfPlane
open scoped Topology ContDiff

variable (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
  (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
  (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)

/-- Enlarging the compact observation set eliminates any dense-interior
hypothesis on that set itself. -/
theorem laplacianUpperLocalMap_continuous (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ U) : Continuous (laplacianUpperLocalMap χ hχ hcχ hsχ U hU hχU K hKU) := by
  have hK : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
  obtain ⟨V, hV, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  let L := closure V
  let : CompactSpace L := isCompact_iff_compactSpace.mp hVc
  have hKL : K ⊆ L := hKV.trans subset_closure
  have hreg : L ⊆ closure (interior L) := closure_mono hV.subset_interior_closure
  let R := laplacianUpperLocalRestriction χ hχ hcχ hsχ U hU hχU L hVU hreg
  let A : LaplacianGraphDomain →L[ℂ] C(K, ℂ) :=
    (ContinuousMap.compCLM ℂ ℂ (ContinuousMap.inclusion hKL)).comp R
  have hA : (laplacianUpperLocalMap χ hχ hcχ hsχ U hU hχU K hKU :
      LaplacianGraphDomain → C(K, ℂ)) = A := by
    funext u
    apply ContinuousMap.ext
    intro z
    rfl
  rw [hA]
  exact A.continuous

/-- The actual graph vector's continuous value on an arbitrary compact subset
of the open upper cutoff plateau. -/
def laplacianUpperCompactRestriction (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ U) : LaplacianGraphDomain →L[ℂ] C(K, ℂ) where
  toLinearMap := laplacianUpperLocalMap χ hχ hcχ hsχ U hU hχU K hKU
  cont := laplacianUpperLocalMap_continuous χ hχ hcχ hsχ U hU hχU K hKU

theorem laplacianUpperCompactRestriction_ae (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ U) (u : LaplacianGraphDomain) :
    localContinuousExtend (laplacianUpperCompactRestriction χ hχ hcχ hsχ U hU hχU K hKU u)
      =ᵐ[volume.restrict K] (fun z => laplacianUpperGraphValue χ hχ hcχ hsχ u z) :=
  laplacianUpperLocalMap_ae χ hχ hcχ hsχ U hU hχU
    (isCompact_iff_compactSpace.mpr inferInstance).measurableSet hKU u

theorem laplacianUpperCompactRestriction_bound (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : LaplacianGraphDomain) (z : K),
      ‖laplacianUpperCompactRestriction χ hχ hcχ hsχ U hU hχU K hKU u z‖ ≤ C * ‖u‖ := by
  let T := laplacianUpperCompactRestriction χ hχ hcχ hsχ U hU hχU K hKU
  refine ⟨‖T‖ + 1, by positivity, fun u z => ?_⟩
  exact ((T u).norm_coe_le_norm z).trans ((T.le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (by linarith : ‖T‖ ≤ ‖T‖ + 1) (norm_nonneg u)))

/-- Literal point evaluation is bounded in the actual Laplacian graph norm. -/
def laplacianUpperCompactEvaluation (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ U) (z : K) : LaplacianGraphDomain →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ z).comp
    (laplacianUpperCompactRestriction χ hχ hcχ hsχ U hU hχU K hKU)

theorem laplacianUpperCompactEvaluation_graph_bound (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : laplacian.domain) (z : K),
      ‖laplacianUpperCompactEvaluation χ hχ hcχ hsχ U hU hχU K hKU z
        (gradientLift laplacian u)‖^2 ≤
          C^2 * (‖(u : ModularHilbert)‖^2 + ‖laplacian u‖^2) := by
  obtain ⟨C, hC, hbound⟩ :=
    laplacianUpperCompactRestriction_bound χ hχ hcχ hsχ U hU hχU K hKU
  refine ⟨C, hC, fun u z => ?_⟩
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC.le (norm_nonneg _))).mpr
    (hbound (gradientLift laplacian u) z)
  rw [mul_pow, gradientGraph_norm_sq, gradientEmbedding_lift, gradientValue_lift] at hs
  exact hs

/-- Evaluation agrees pointwise with every genuine local continuous
representative of the same actual ordinary value field. -/
theorem laplacianUpperCompactEvaluation_eq_localRepresentative
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U)
    (z : K) (u : LaplacianGraphDomain) {V : Set ℂ} (hV : IsOpen V)
    (hz : (z : ℂ) ∈ V) (hVU : V ⊆ U) {G : ℂ → ℂ} (hG : ContinuousOn G V)
    (hGae : G =ᵐ[volume.restrict V] (fun w => laplacianUpperGraphValue χ hχ hcχ hsχ u w)) :
    laplacianUpperCompactEvaluation χ hχ hcχ hsχ U hU hχU K hKU z u = G z := by
  have hr : laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU u
      =ᵐ[volume.restrict V] (fun w => laplacianUpperGraphValue χ hχ hcχ hsχ u w) :=
    ae_restrict_of_ae_restrict_of_subset hVU
      (laplacianUpperRepresentative_ae χ hχ hcχ hsχ U hU hχU u)
  exact Measure.eqOn_open_of_ae_eq (μ := volume) (hr.trans hGae.symm) hV
    ((laplacianUpperRepresentative_continuousOn χ hχ hcχ hsχ U hU hχU u).mono hVU) hG hz

/-- Every actual compact upper-half-plane set has a proved admissible chart
and bounded continuous evaluation; no PDE or regularity witness is an input. -/
theorem exists_laplacianUpperCompactRestriction
    (K : Set ℂ) [CompactSpace K] (hKH : K ⊆ upperHalfPlaneSet) :
    ∃ (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
      (hsχ : tsupport χ ⊆ upperHalfPlaneSet) (U : Set ℂ) (hU : IsOpen U)
      (hχU : EqOn χ (fun _ => 1) U) (hKU : K ⊆ U),
      ∃ C : ℝ, 0 < C ∧ ∀ (u : laplacian.domain) (z : K),
        ‖laplacianUpperCompactEvaluation χ hχ hcχ hsχ U hU hχU K hKU z
          (gradientLift laplacian u)‖^2 ≤
            C^2 * (‖(u : ModularHilbert)‖^2 + ‖laplacian u‖^2) := by
  obtain ⟨L, U, χ, _hL, _hreg, hKL, hU, hLU, _hUc, _hUH, hχ, hcχ, hsχ, hχU⟩ :=
    exists_upperEvaluationCutoff (isCompact_iff_compactSpace.mpr inferInstance) hKH
  have hKU : K ⊆ U := hKL.trans (interior_subset.trans hLU)
  exact ⟨χ, hχ, hcχ, hsχ, U, hU, hχU, hKU,
    laplacianUpperCompactEvaluation_graph_bound χ hχ hcχ hsχ U hU hχU K hKU⟩

end GapFamily.Analytic.ModularGradient
