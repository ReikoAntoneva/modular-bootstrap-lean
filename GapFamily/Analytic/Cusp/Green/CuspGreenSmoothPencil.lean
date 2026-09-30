import GapFamily.Analytic.Cusp.Green.CuspGreenPhysicalWeak
import GapFamily.Analytic.Cusp.Green.CuspGreenSmoothForm
import GapFamily.Analytic.Cusp.Profile.CuspProfileInner
import GapFamily.Analytic.Cusp.Green.CuspGreenSourceLift
import GapFamily.Analytic.Cusp.Scalar.CuspScalarPencilRegular
import GapFamily.Analytic.Cusp.Profile.CuspProfileLaplacian

/-!
# The actual smooth Green integral is the scalar pencil solution

The literal compact-test equation extends through the closed scalar form space.
Its uniqueness identifies the genuine smooth Green graph limit with the actual
Riesz/pencil response, with the logarithmic source normalization retained.
-/

noncomputable section

namespace GapFamily.Analytic
open Set MeasureTheory ModularGradient
open scoped ContDiff

private theorem cuspGreen_test_value_ae (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi 1) :
    value (cuspProfileCore b hb hc hs) =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => if 1 < τ.im then b τ.im else 0 := by
  filter_upwards [cuspProfileCore_value_ae b hb hc hs] with τ hτ
  rw [hτ]
  split_ifs with hy
  · rfl
  · exact image_eq_zero_of_notMem_tsupport (fun h => hy (hs h))

/-- The actual smooth Green form obeys the weak equation against every genuine
compact scalar profile, with the literal collar L² source pairing. -/
theorem cuspGreenSmoothForm_compact_test_weak {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hfS : tsupport f ⊆ Ioo 0 T) (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi 1) :
    inner ℂ (coreGradient (cuspProfileCore b hb hc hs))
      (formGradient (cuspGreenSmoothForm hT hκ hf hfS)) -
      (1/4 - κ^2) * inner ℂ (value (cuspProfileCore b hb hc hs))
        (formEmbedding (cuspGreenSmoothForm hT hκ hf hfS)) =
      ∫ u : CuspGreenCollar 0 T, inner ℂ (cuspLogCoordinate b u)
        (cuspGreenCollarSource 0 T f hf.continuous u) ∂cuspGreenCollarMeasure 0 T := by
  let F := cuspGreenCollarSource 0 T f hf.continuous
  let V := cuspGreenCollarResponse 0 T κ F
  have hfT : ∀ u, T < u → f u = 0 := by
    intro u hu
    exact image_eq_zero_of_notMem_tsupport (fun h => (hfS h).2.not_ge hu.le)
  have hrep : formEmbedding (cuspGreenSmoothForm hT hκ hf hfS) =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => if 1 < τ.im then cuspLift V τ.im else 0 := by
    have he := cuspGreenSmoothForm_embedding_ae hT hκ hf hfS
    simpa only [V, F, cuspLift,
      cuspGreenCollarResponse_source_eq_solution T hT κ f hf.continuous hfT] using he
  have hmass := cuspProfile_inner_integral
    (value (cuspProfileCore b hb hc hs)) (formEmbedding (cuspGreenSmoothForm hT hκ hf hfS))
    b (cuspLift V) (cuspGreen_test_value_ae b hb hc hs) hrep
  have hlap := cuspProfile_inner_integral
    (cuspProfileLaplacianValue b hb hc hs) (formEmbedding (cuspGreenSmoothForm hT hκ hf hfS))
    (cuspProfileSecondOrder b) (cuspLift V)
    (cuspGreen_test_value_ae _ (contDiff_cuspProfileSecondOrder hb)
      (cuspProfileSecondOrder_hasCompactSupport hc)
      ((cuspProfileSecondOrder_tsupport_subset b).trans hs)) hrep
  rw [← cuspProfileCore_form_energy, hlap.2, hmass.2]
  calc
    _ = ∫ y in Ioi (1 : ℝ),
      (inner ℂ (cuspProfileSecondOrder b y) (cuspLift V y) -
        (1/4 - κ^2) * inner ℂ (b y) (cuspLift V y)) / (y : ℂ)^2 := by
      rw [← integral_const_mul, ← integral_sub hlap.1 (hmass.1.const_mul _)]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _
      ring
    _ = _ := (cuspGreenCollarResponse_physical_test T hT κ F hb hc hs).2.2

end GapFamily.Analytic

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory ModularGradient
open scoped ContDiff

/-- The actual compact collar source pairing is its ordinary half-line integral. -/
theorem cuspGreenCollarSource_test_integral (T : ℝ) (f : ℝ → ℂ) (hf : Continuous f)
    (hfS : tsupport f ⊆ Ioo 0 T) (ψ : ℝ → ℂ) :
    (∫ u : CuspGreenCollar 0 T, inner ℂ (ψ u)
      (cuspGreenCollarSource 0 T f hf u) ∂cuspGreenCollarMeasure 0 T) =
      ∫ t in Ioi (0 : ℝ), inner ℂ (ψ t) (f t) := by
  calc
    _ = ∫ u : CuspGreenCollar 0 T, inner ℂ (ψ u) (f u)
        ∂cuspGreenCollarMeasure 0 T := by
      apply integral_congr_ae
      filter_upwards [cuspGreenCollarSource_coeFn 0 T f hf] with u hu
      rw [hu]
    _ = ∫ t in Icc (0 : ℝ) T, inner ℂ (ψ t) (f t) :=
      integral_subtype_comap measurableSet_Icc (fun t : ℝ => inner ℂ (ψ t) (f t))
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc]
      symm
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        Ioc_subset_Ioi_self
      intro t ht
      have hnot : t ∉ tsupport f := by
        intro h
        exact ht.2 ⟨(hfS h).1, (hfS h).2.le⟩
      rw [image_eq_zero_of_notMem_tsupport hnot, inner_zero_right]

/-- The smooth logarithmic source is its actual modular Hilbert vector in every compact test. -/
theorem cuspGreenSourceLift_compact_pairing {T : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hfS : tsupport f ⊆ Ioo 0 T)
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi 1) :
    inner ℂ (value (cuspProfileCore b hb hc hs))
      (cuspGreenSourceLift f hf hfc (hfS.trans Ioo_subset_Ioi_self)) =
      ∫ u : CuspGreenCollar 0 T, inner ℂ (cuspLogCoordinate b u)
        (cuspGreenCollarSource 0 T f hf.continuous u) ∂cuspGreenCollarMeasure 0 T := by
  have hrep := cuspGreenSourceLift_ae f hf hfc
    (hfS.trans Ioo_subset_Ioi_self)
  change cuspGreenSourceLift f hf hfc _ =ᵐ[modularMeasure]
    (fun τ : UpperHalfPlane => if 1 < τ.im then cuspLift f τ.im else 0) at hrep
  rw [cuspProfile_inner_eq_integral _ _ b (cuspLift f)
    (cuspGreen_test_value_ae b hb hc hs) hrep,
    integral_cuspLogCoordinate_inner, cuspGreenCollarSource_test_integral T f hf.continuous hfS]

/-- A compact-test identity with an actual source extends to every vector in W. -/
theorem cuspGreen_weak_extend {U : FormDomain} {z : ℂ} {F : ModularHilbert}
    (hgen : ∀ (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
      (hs : tsupport b ⊆ Ioi (1 : ℝ)),
      inner ℂ (coreGradient (cuspProfileCore b hb hc hs)) (formGradient U) -
        z * inner ℂ (value (cuspProfileCore b hb hc hs)) (formEmbedding U) =
        inner ℂ (value (cuspProfileCore b hb hc hs)) F)
    (w : cuspScalarForm) :
    inner ℂ (formGradient (w : FormDomain)) (formGradient U) -
      z * inner ℂ (formEmbedding (w : FormDomain)) (formEmbedding U) =
      inner ℂ (formEmbedding (w : FormDomain)) F := by
  let A : FormDomain →L[ℂ] ℂ :=
    (innerSL ℂ (formGradient U)).comp formGradient -
      ((starRingEnd ℂ) z) • (innerSL ℂ (formEmbedding U)).comp formEmbedding -
      (innerSL ℂ F).comp formEmbedding
  have hW : cuspScalarForm ≤ A.ker := by
    apply cuspScalarForm_le_of_isClosed _ A.isClosed_ker
    intro b hb hc hs
    change inner ℂ (formGradient U) (formGradient (coreForm (cuspProfileCore b hb hc hs))) -
      (starRingEnd ℂ) z * inner ℂ (formEmbedding U) (formEmbedding (coreForm (cuspProfileCore b hb hc hs))) -
      inner ℂ F (formEmbedding (coreForm (cuspProfileCore b hb hc hs))) = 0
    rw [formGradient_coreForm, formEmbedding_coreForm]
    have h := congrArg (starRingEnd ℂ) (hgen b hb hc hs)
    simp only [map_sub, map_mul, inner_conj_symm] at h
    exact sub_eq_zero.mpr h
  have h := hW w.property
  change inner ℂ (formGradient U) (formGradient (w : FormDomain)) -
    (starRingEnd ℂ) z * inner ℂ (formEmbedding U) (formEmbedding (w : FormDomain)) -
    inner ℂ F (formEmbedding (w : FormDomain)) = 0 at h
  have hs := congrArg (starRingEnd ℂ) h
  simpa only [map_sub, map_mul, starRingEnd_self_apply, inner_conj_symm, map_zero, sub_eq_zero] using hs

/-- The literal Green integral, as an actual scalar form vector, solves every scalar form test. -/
theorem cuspGreenSmoothForm_test_weak {T : ℝ} (hT : 0 ≤ T) {κ : ℂ} (hκ : 0 < κ.re)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfS : tsupport f ⊆ Ioo 0 T) (w : cuspScalarForm) :
    inner ℂ (formGradient (w : FormDomain)) (formGradient (cuspGreenSmoothForm hT hκ hf hfS)) -
      (1/4 - κ^2) * inner ℂ (formEmbedding (w : FormDomain))
        (formEmbedding (cuspGreenSmoothForm hT hκ hf hfS)) =
      inner ℂ (formEmbedding (w : FormDomain))
        (cuspGreenSourceLift f hf hfc (hfS.trans Ioo_subset_Ioi_self)) := by
  apply cuspGreen_weak_extend
  intro b hb hc hs
  rw [cuspGreenSourceLift_compact_pairing hf hfc hfS b hb hc hs]
  exact cuspGreenSmoothForm_compact_test_weak hT hκ hf hfS b hb hc hs

/-- Genuine Green/Riesz identification on the dense class of smooth compact collar sources. -/
theorem cuspGreenSmoothForm_eq_pencilSolution {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hfS : tsupport f ⊆ Ioo 0 T) :
    (⟨cuspGreenSmoothForm hT hκ hf hfS,
      cuspGreenSmoothForm_mem_cuspScalarForm hT hκ hf hfS⟩ : cuspScalarForm) =
      cuspScalarPencilSolution (1/4 - κ^2)
        (cuspGreenSourceLift f hf hfc (hfS.trans Ioo_subset_Ioi_self)) := by
  apply cuspScalarPencilSolution_unique_physical hκ
  intro w
  exact cuspGreenSmoothForm_test_weak hT hκ hf hfc hfS w

end GapFamily.Analytic
