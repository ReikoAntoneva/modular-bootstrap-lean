import GapFamily.Analytic.Cusp.Green.CuspGreenSourceEmbedding
import GapFamily.Analytic.Cusp.Profile.CuspHalfLineSourceEmbedding
import GapFamily.Analytic.Cusp.Green.CuspGreenCoefficient

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory
open scoped ContDiff

/-- Every genuine smooth collar source defines an actual half-line `L²` class. -/
theorem cuspHalfLineCollarSmooth_memLp (T : ℝ) (f : cuspGreenSourceSpace T) :
    MemLp (f : ℝ → ℂ) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  f.property.1.continuous.memLp_of_hasCompactSupport f.property.2.1

/-- Literal restriction of a smooth compact collar profile to the whole half-line. -/
def cuspHalfLineCollarSmoothValue (T : ℝ) (f : cuspGreenSourceSpace T) :
    Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (cuspHalfLineCollarSmooth_memLp T f).toLp f

theorem cuspHalfLineCollarSmoothValue_ae (T : ℝ) (f : cuspGreenSourceSpace T) :
    cuspHalfLineCollarSmoothValue T f =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (f : ℝ → ℂ) :=
  (cuspHalfLineCollarSmooth_memLp T f).coeFn_toLp

def cuspHalfLineCollarOnSmooth (T : ℝ) :
    cuspGreenSourceSpace T →ₗ[ℂ] Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) where
  toFun := cuspHalfLineCollarSmoothValue T
  map_add' f g := by
    apply Lp.ext
    filter_upwards [cuspHalfLineCollarSmoothValue_ae T (f + g),
      cuspHalfLineCollarSmoothValue_ae T f, cuspHalfLineCollarSmoothValue_ae T g,
      Lp.coeFn_add (cuspHalfLineCollarSmoothValue T f) (cuspHalfLineCollarSmoothValue T g)]
      with t hfg hf hg hadd
    rw [hfg, hadd, Pi.add_apply, hf, hg]
    rfl
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [cuspHalfLineCollarSmoothValue_ae T (c • f),
      cuspHalfLineCollarSmoothValue_ae T f,
      Lp.coeFn_smul c (cuspHalfLineCollarSmoothValue T f)] with t hcf hf hsmul
    simp only [RingHom.id_apply]
    rw [hcf, hsmul, Pi.smul_apply, hf]
    rfl

theorem cuspHalfLineCollarOnSmooth_norm_sq (T : ℝ) (f : cuspGreenSourceSpace T) :
    ‖cuspHalfLineCollarOnSmooth T f‖ ^ 2 = ∫ t : ℝ in Ioi 0, ‖(f : ℝ → ℂ) t‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
  apply integral_congr_ae
  filter_upwards [cuspHalfLineCollarSmoothValue_ae T f] with t ht
  change ‖cuspHalfLineCollarSmoothValue T f t‖ ^ 2 = _
  rw [ht]

/-- The inclusion is isometric already on the actual dense smooth source space. -/
theorem cuspHalfLineCollarOnSmooth_norm (T : ℝ) (f : cuspGreenSourceSpace T) :
    ‖cuspHalfLineCollarOnSmooth T f‖ = ‖cuspGreenSourceRestriction T f‖ := by
  have hsq : ‖cuspHalfLineCollarOnSmooth T f‖ ^ 2 =
      ‖cuspGreenSourceOnSmooth T f‖ ^ 2 := by
    rw [cuspHalfLineCollarOnSmooth_norm_sq]
    exact (cuspGreenSourceLift_norm_sq f f.property.1 f.property.2.1
      (f.property.2.2.trans Ioo_subset_Ioi_self)).symm
  have hn : ‖cuspHalfLineCollarOnSmooth T f‖ = ‖cuspGreenSourceOnSmooth T f‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  exact hn.trans (cuspGreenSourceOnSmooth_norm T f)

/-- The actual collar Hilbert space embeds by zero extension into the complete logarithmic
half-line. The map is determined by the literal profiles on its proved dense source space. -/
def cuspHalfLineCollarInclusion (T : ℝ) :
    Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →ₗᵢ[ℂ]
      Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (cuspHalfLineCollarOnSmooth T).extendOfIsometry
    (cuspGreenSourceRestriction_denseRange T) (cuspHalfLineCollarOnSmooth_norm T)

theorem cuspHalfLineCollarInclusion_restriction (T : ℝ) (f : cuspGreenSourceSpace T) :
    cuspHalfLineCollarInclusion T (cuspGreenSourceRestriction T f) =
      cuspHalfLineCollarSmoothValue T f :=
  (cuspHalfLineCollarOnSmooth T).extendOfIsometry_eq
    (cuspGreenSourceRestriction_denseRange T) (cuspHalfLineCollarOnSmooth_norm T) f

theorem cuspHalfLineCollarInclusion_smooth_ae (T : ℝ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioo 0 T) :
    cuspHalfLineCollarInclusion T (cuspGreenCollarSource 0 T f hf.continuous)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
  rw [show cuspGreenCollarSource 0 T f hf.continuous =
      cuspGreenSourceRestriction T ⟨f, hf, hc, hs⟩ from rfl,
    cuspHalfLineCollarInclusion_restriction]
  exact cuspHalfLineCollarSmoothValue_ae T ⟨f, hf, hc, hs⟩

theorem cuspHalfLineCollarInclusion_norm (T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :
    ‖cuspHalfLineCollarInclusion T f‖ = ‖f‖ :=
  (cuspHalfLineCollarInclusion T).norm_map f

/-- Agreement of the actual full half-line lift and the old smooth collar lift. -/
theorem cuspHalfLineSourceEmbedding_collarSmooth (T : ℝ) (f : cuspGreenSourceSpace T) :
    cuspHalfLineSourceEmbedding (cuspHalfLineCollarSmoothValue T f) =
      cuspGreenSmoothSourceValue T f := by
  apply Lp.ext
  apply (cuspHalfLineSourceValue_ae (cuspHalfLineCollarSmoothValue T f)).trans
  apply (cuspHalfLine_lift_congr_ae (cuspHalfLineCollarSmoothValue_ae T f)).trans
  exact (cuspGreenSourceLift_ae f f.property.1 f.property.2.1
    (f.property.2.2.trans Ioo_subset_Ioi_self)).symm

/-- The actual finite-collar source embedding is exactly the full half-line embedding
after zero extension, for every collar `L²` source. -/
theorem cuspHalfLineSourceEmbedding_collarInclusion (T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :
    cuspHalfLineSourceEmbedding (cuspHalfLineCollarInclusion T f) =
      cuspGreenSourceEmbedding T f := by
  refine (cuspGreenSourceRestriction_denseRange T).induction_on f
    (isClosed_eq (cuspHalfLineSourceEmbedding.continuous.comp
      (cuspHalfLineCollarInclusion T).continuous) (cuspGreenSourceEmbedding T).continuous) ?_
  intro g
  rw [cuspHalfLineCollarInclusion_restriction, cuspHalfLineSourceEmbedding_collarSmooth]
  exact (cuspGreenSourceEmbedding_smooth T g g.property.1 g.property.2.1 g.property.2.2).symm

/-- The bounded collar restriction is the adjoint of actual zero extension. -/
def cuspHalfLineCollarRestriction (T : ℝ) :
    cuspHalfLineSourceHilbert →L[ℂ] Lp ℂ 2 (cuspGreenCollarMeasure 0 T) :=
  (cuspHalfLineCollarInclusion T).toContinuousLinearMap.adjoint

theorem cuspHalfLineCollarRestriction_inner_right (T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) (g : cuspHalfLineSourceHilbert) :
    inner ℂ f (cuspHalfLineCollarRestriction T g) =
      inner ℂ (cuspHalfLineCollarInclusion T f) g :=
  (cuspHalfLineCollarInclusion T).toContinuousLinearMap.adjoint_inner_right f g

@[simp]
theorem cuspHalfLineCollarRestriction_inclusion (T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :
    cuspHalfLineCollarRestriction T (cuspHalfLineCollarInclusion T f) = f := by
  apply ext_inner_left ℂ
  intro g
  rw [cuspHalfLineCollarRestriction_inner_right]
  exact (cuspHalfLineCollarInclusion T).inner_map_map g f

theorem cuspHalfLineCollarRestriction_opNorm_le (T : ℝ) :
    ‖cuspHalfLineCollarRestriction T‖ ≤ 1 := by
  unfold cuspHalfLineCollarRestriction
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact (cuspHalfLineCollarInclusion T).norm_toContinuousLinearMap_le

/-- Existing finite-height coefficient extraction is the true restriction of the
constructed full half-line coefficient. -/
theorem cuspHalfLineCollarRestriction_sourceCoefficient (T : ℝ) (F : ModularHilbert) :
    cuspHalfLineCollarRestriction T (cuspHalfLineSourceCoefficient F) =
      cuspGreenSourceCoefficient T F := by
  apply ext_inner_left ℂ
  intro g
  rw [cuspHalfLineCollarRestriction_inner_right, cuspHalfLineSourceCoefficient_inner_right,
    cuspHalfLineSourceEmbedding_collarInclusion, cuspGreenSourceCoefficient_inner_right]

end GapFamily.Analytic
