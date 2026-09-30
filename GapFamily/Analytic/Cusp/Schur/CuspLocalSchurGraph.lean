import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurCutoffPhysical
import GapFamily.Analytic.Modular.ModularAnalyticGraphContinuation
import GapFamily.Analytic.Modular.ModularGraphAnalytic

/-!
# The continued cutoff Schur response in the actual Laplacian graph

The proved physical graph equation continues to a common complex parameter
disk. Bounded graph packaging is analytic in operator norm and has exactly
the continued cutoff value and Laplacian coordinates throughout that disk.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchurLocal

open ModularGradient Dirichlet Set
open scoped ContDiff

/-- One disk works simultaneously for every Hilbert source. -/
theorem exists_ball_continuedCutoff_graph
    (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ modularInterior)
    {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hH : tsupport χ ⊆ {z : ℂ | z.im ≤ Real.exp L}) :
    ∃ r : ℝ, 0 < r ∧
      AnalyticOnNhd ℂ (continuedCutoffSchur χ hχ hc L T) (Metric.ball (0 : ℂ) r) ∧
      AnalyticOnNhd ℂ (continuedCutoffLaplacian χ hχ hc L T) (Metric.ball (0 : ℂ) r) ∧
      ∀ κ : ℂ, ‖κ‖ < r → ∀ f : ModularHilbert,
        (continuedCutoffSchur χ hχ hc L T κ f,
          continuedCutoffLaplacian χ hχ hc L T κ f) ∈ laplacian.graph :=
  exists_ball_laplacian_graph_of_physical
    (continuedCutoffSchur χ hχ hc L T) (continuedCutoffLaplacian χ hχ hc L T)
    (continuedCutoffSchur_analyticAt_zero χ hχ hc L T)
    (continuedCutoffLaplacian_analyticAt_zero χ hχ hc L T)
    (exists_radius_continuedCutoff_graph_physical χ hχ hc hs hL hT hH)

/-- The actual bounded graph-valued cutoff response. -/
def continuedCutoffGraph (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (L T : ℝ) (κ : ℂ) :
    ModularHilbert →L[ℂ] LaplacianGraphDomain :=
  laplacianGraphOperator ModularHilbert
    (continuedCutoffSchur χ hχ hc L T κ, continuedCutoffLaplacian χ hχ hc L T κ)

@[simp] theorem continuedCutoffGraph_apply (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (L T : ℝ) (κ : ℂ) (f : ModularHilbert) :
    continuedCutoffGraph χ hχ hc L T κ f = laplacianGraphPairMap
      (continuedCutoffSchur χ hχ hc L T κ f,
        continuedCutoffLaplacian χ hχ hc L T κ f) := rfl

theorem continuedCutoffGraph_analyticAt_zero (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (L T : ℝ) :
    AnalyticAt ℂ (continuedCutoffGraph χ hχ hc L T) 0 :=
  laplacianGraphOperator_analyticAt ModularHilbert
    (continuedCutoffSchur_analyticAt_zero χ hχ hc L T)
    (continuedCutoffLaplacian_analyticAt_zero χ hχ hc L T)

theorem continuedCutoffGraph_embedding_of_mem
    (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (L T : ℝ) (κ : ℂ)
    (h : ∀ f : ModularHilbert,
      (continuedCutoffSchur χ hχ hc L T κ f,
        continuedCutoffLaplacian χ hχ hc L T κ f) ∈ laplacian.graph) :
    (gradientEmbedding laplacian).comp (continuedCutoffGraph χ hχ hc L T κ) =
      continuedCutoffSchur χ hχ hc L T κ :=
  laplacianGraphOperator_embedding ModularHilbert _ _ h

theorem continuedCutoffGraph_value_of_mem
    (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (L T : ℝ) (κ : ℂ)
    (h : ∀ f : ModularHilbert,
      (continuedCutoffSchur χ hχ hc L T κ f,
        continuedCutoffLaplacian χ hχ hc L T κ f) ∈ laplacian.graph) :
    (gradientValue laplacian).comp (continuedCutoffGraph χ hχ hc L T κ) =
      continuedCutoffLaplacian χ hχ hc L T κ :=
  laplacianGraphOperator_value ModularHilbert _ _ h

/-- On a common disk, analytic graph packaging retains both original coordinates. -/
theorem exists_ball_continuedCutoffGraph_coordinates
    (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ modularInterior)
    {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hH : tsupport χ ⊆ {z : ℂ | z.im ≤ Real.exp L}) :
    ∃ r : ℝ, 0 < r ∧
      AnalyticOnNhd ℂ (continuedCutoffGraph χ hχ hc L T) (Metric.ball (0 : ℂ) r) ∧
      ∀ κ : ℂ, ‖κ‖ < r →
        (gradientEmbedding laplacian).comp (continuedCutoffGraph χ hχ hc L T κ) =
            continuedCutoffSchur χ hχ hc L T κ ∧
          (gradientValue laplacian).comp (continuedCutoffGraph χ hχ hc L T κ) =
            continuedCutoffLaplacian χ hχ hc L T κ := by
  obtain ⟨r, hr, hF, hG, hgraph⟩ :=
    exists_ball_continuedCutoff_graph χ hχ hc hs hL hT hH
  refine ⟨r, hr, laplacianGraphOperator_analyticOnNhd ModularHilbert hF hG, ?_⟩
  intro κ hκ
  exact ⟨continuedCutoffGraph_embedding_of_mem χ hχ hc L T κ (hgraph κ hκ),
    continuedCutoffGraph_value_of_mem χ hχ hc L T κ (hgraph κ hκ)⟩

theorem continuedCutoffGraph_coordinates_zero
    (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ modularInterior)
    {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hH : tsupport χ ⊆ {z : ℂ | z.im ≤ Real.exp L}) :
    (gradientEmbedding laplacian).comp (continuedCutoffGraph χ hχ hc L T 0) =
        continuedCutoffSchur χ hχ hc L T 0 ∧
      (gradientValue laplacian).comp (continuedCutoffGraph χ hχ hc L T 0) =
        continuedCutoffLaplacian χ hχ hc L T 0 := by
  obtain ⟨r, hr, _, hcoordinates⟩ :=
    exists_ball_continuedCutoffGraph_coordinates χ hχ hc hs hL hT hH
  exact hcoordinates 0 (by simpa only [norm_zero] using hr)

end GapFamily.Analytic.CuspSchurLocal
