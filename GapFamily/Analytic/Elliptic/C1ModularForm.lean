import GapFamily.Analytic.Elliptic.C1ModularFiniteForm
import GapFamily.Analytic.Elliptic.C1ModularTruncationLp

noncomputable section
namespace GapFamily.Analytic.C1ModularForm
open Set Filter MeasureTheory UpperHalfPlane ModularGradient FormTruncation
open scoped ContDiff MatrixGroups Topology

/-- A genuinely modular C1 field of finite mass and frame energy belongs to the original closed form. -/
theorem exists_form_of_C1 (F : ℂ → ℂ)
    (hF : ContDiffOn ℝ 1 F upperHalfPlaneSet)
    (hinv : ∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, F (γ • τ : UpperHalfPlane) = F τ)
    (hf : MemLp (fun τ : UpperHalfPlane => F τ) 2 modularMeasure)
    (hx : MemLp (directional F 1) 2 modularMeasure)
    (hy : MemLp (directional F Complex.I) 2 modularMeasure) :
    ∃ u : FormDomain,
      formEmbedding u = hf.toLp (fun τ : UpperHalfPlane => F τ) ∧
      (WithLp.ofLp (formGradient u)).1 = hx.toLp (directional F 1) ∧
      (WithLp.ofLp (formGradient u)).2 = hy.toLp (directional F Complex.I) := by
  have hu (n : ℕ) := exists_form_of_C1_finite_height (truncateC1 n F)
    (contDiffOn_truncateC1 hF n) (truncateC1_invariant hinv n) (2 * scale n)
    (fun τ hτ ht => truncateC1_zero_above n F τ hτ ht.le)
  choose un hun hxn hyn using hu
  let fn : ℕ → ModularHilbert := fun n => (truncateC1_memLp_value hF hf n).toLp
    (fun τ : UpperHalfPlane => truncateC1 n F τ)
  let xn : ℕ → ModularHilbert := fun n => (truncateC1_memLp_directional hF hf 1 hx n).toLp
    (directional (truncateC1 n F) 1)
  let yn : ℕ → ModularHilbert := fun n => (truncateC1_memLp_directional hF hf Complex.I hy n).toLp
    (directional (truncateC1 n F) Complex.I)
  have he (n) : formEmbedding (un n) = fn n :=
    Lp.ext ((hun n).trans (MemLp.coeFn_toLp _).symm)
  have hxe (n) : (WithLp.ofLp (formGradient (un n))).1 = xn n :=
    Lp.ext ((hxn n).trans (MemLp.coeFn_toLp _).symm)
  have hye (n) : (WithLp.ofLp (formGradient (un n))).2 = yn n :=
    Lp.ext ((hyn n).trans (MemLp.coeFn_toLp _).symm)
  let U : ModularHilbert := hf.toLp (fun τ : UpperHalfPlane => F τ)
  let G : GradientSpace := WithLp.toLp 2 (hx.toLp (directional F 1), hy.toLp (directional F Complex.I))
  have hv : Tendsto (fun n => formEmbedding (un n)) atTop (𝓝 U) := by
    simpa only [he] using truncateC1_value_tendsto hF hf
  have hg : Tendsto (fun n => formGradient (un n)) atTop (𝓝 G) := by
    have heq (n) : formGradient (un n) = WithLp.toLp 2 (xn n, yn n) := by
      apply (WithLp.linearEquiv 2 ℂ (ModularHilbert × ModularHilbert)).injective
      exact Prod.ext (hxe n) (hye n)
    simp_rw [heq]
    exact (WithLp.prodContinuousLinearEquiv 2 ℂ ModularHilbert ModularHilbert).symm.continuous.continuousAt.tendsto.comp
      ((truncateC1_directional_tendsto hF hf 1 hx).prodMk_nhds
        (truncateC1_directional_tendsto hF hf Complex.I hy))
  have hp : (U, G) ∈ closedGradient.graph := by
    apply closedGradient_isClosed.mem_of_tendsto (hv.prodMk_nhds hg)
    exact Eventually.of_forall fun n => (un n).property
  exact ⟨⟨WithLp.toLp 2 (U, G), hp⟩, rfl, rfl, rfl⟩

end GapFamily.Analytic.C1ModularForm
