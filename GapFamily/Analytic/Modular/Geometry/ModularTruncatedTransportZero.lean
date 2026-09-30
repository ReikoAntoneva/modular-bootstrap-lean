import GapFamily.Analytic.Elliptic.LocalSobolevCompactRestriction

/-!
# Isometric zero extension from a compact Euclidean subset

The source measure is literal Lebesgue measure on the compact subtype. Extension
by zero preserves the ordinary L² norm and has its actual almost-everywhere
representative, including for restrictions of continuous functions.
-/

noncomputable section

namespace GapFamily.Analytic.LocalSobolev

open Set MeasureTheory

/-- Pointwise extension by zero from a subtype. -/
def zeroExtendFun (T : Set ℂ) (u : T → ℂ) : ℂ → ℂ :=
  Function.extend Subtype.val u 0

@[simp] theorem zeroExtendFun_coe (T : Set ℂ) (u : T → ℂ) (z : T) :
    zeroExtendFun T u z = u z :=
  Subtype.val_injective.extend_apply u 0 z

@[simp] theorem zeroExtendFun_notMem (T : Set ℂ) (u : T → ℂ) {z : ℂ} (hz : z ∉ T) :
    zeroExtendFun T u z = 0 := by
  apply Function.extend_apply'
  rintro ⟨w, rfl⟩
  exact hz w.property

private theorem compact_measurable (T : Set ℂ) [CompactSpace T] : MeasurableSet T :=
  (isCompact_iff_compactSpace.mpr inferInstance).measurableSet

theorem zeroExtendFun_stronglyMeasurable (T : Set ℂ) [CompactSpace T]
    (u : Lp ℂ 2 (restrictedVolume T)) : StronglyMeasurable (zeroExtendFun T u) :=
  (MeasurableEmbedding.subtype_coe (compact_measurable T)).stronglyMeasurable_extend
    (Lp.stronglyMeasurable u) stronglyMeasurable_zero

theorem zeroExtendFun_eLpNorm (T : Set ℂ) [CompactSpace T]
    (u : Lp ℂ 2 (restrictedVolume T)) :
    eLpNorm (zeroExtendFun T u) 2 (volume : Measure ℂ) = eLpNorm u 2 (restrictedVolume T) := by
  have hs : Function.support (zeroExtendFun T u) ⊆ T := by
    intro z hz
    by_contra hnot
    exact hz (zeroExtendFun_notMem T u hnot)
  rw [← eLpNorm_restrict_eq_of_support_subset
    (zeroExtendFun_stronglyMeasurable T u).aestronglyMeasurable hs,
    ← map_comap_subtype_coe (compact_measurable T) volume,
    (MeasurableEmbedding.subtype_coe (compact_measurable T)).eLpNorm_map_measure]
  congr 1
  funext z
  exact zeroExtendFun_coe T u z

theorem zeroExtendFun_memLp (T : Set ℂ) [CompactSpace T]
    (u : Lp ℂ 2 (restrictedVolume T)) : MemLp (zeroExtendFun T u) 2 (volume : Measure ℂ) := by
  rw [memLp_iff, zeroExtendFun_eLpNorm]
  exact Lp.memLp u

/-- Equality almost everywhere on the subtype persists after extension by zero. -/
theorem zeroExtendFun_ae_congr (T : Set ℂ) [CompactSpace T]
    {u v : T → ℂ} (h : u =ᵐ[restrictedVolume T] v) :
    zeroExtendFun T u =ᵐ[volume] zeroExtendFun T v := by
  have hr : zeroExtendFun T u =ᵐ[volume.restrict T] zeroExtendFun T v := by
    apply (ae_restrict_iff_subtype (compact_measurable T)).2
    simpa only [Filter.EventuallyEq, zeroExtendFun_coe, restrictedVolume] using h
  have hr' := (ae_restrict_iff' (compact_measurable T)).1 hr
  filter_upwards [hr'] with z hz
  by_cases hzT : z ∈ T
  · exact hz hzT
  · rw [zeroExtendFun_notMem T u hzT, zeroExtendFun_notMem T v hzT]

/-- Extension of the restriction of a function is its literal indicator. -/
theorem zeroExtendFun_eq_indicator (T : Set ℂ) (f : ℂ → ℂ) :
    zeroExtendFun T (fun z : T => f z) = T.indicator f := by
  funext z
  by_cases hz : z ∈ T
  · rw [Set.indicator_of_mem hz]
    exact zeroExtendFun_coe T _ ⟨z, hz⟩
  · rw [Set.indicator_of_notMem hz, zeroExtendFun_notMem T _ hz]

theorem zeroExtendFun_add (T : Set ℂ) (u v : T → ℂ) :
    zeroExtendFun T (u + v) = zeroExtendFun T u + zeroExtendFun T v := by
  funext z
  by_cases hz : z ∈ T
  · calc
      _ = (u + v) ⟨z, hz⟩ := zeroExtendFun_coe T (u + v) ⟨z, hz⟩
      _ = u ⟨z, hz⟩ + v ⟨z, hz⟩ := rfl
      _ = _ := congrArg₂ (· + ·) (zeroExtendFun_coe T u ⟨z, hz⟩).symm
        (zeroExtendFun_coe T v ⟨z, hz⟩).symm
  · simp only [Pi.add_apply, zeroExtendFun_notMem T _ hz, add_zero]

theorem zeroExtendFun_smul (T : Set ℂ) (c : ℂ) (u : T → ℂ) :
    zeroExtendFun T (c • u) = c • zeroExtendFun T u := by
  funext z
  by_cases hz : z ∈ T
  · calc
      _ = (c • u) ⟨z, hz⟩ := zeroExtendFun_coe T (c • u) ⟨z, hz⟩
      _ = c • u ⟨z, hz⟩ := rfl
      _ = _ := congrArg (c • ·) (zeroExtendFun_coe T u ⟨z, hz⟩).symm
  · simp only [Pi.smul_apply, zeroExtendFun_notMem T _ hz, smul_zero]

private def zeroExtensionLp (T : Set ℂ) [CompactSpace T]
    (u : Lp ℂ 2 (restrictedVolume T)) : Lp ℂ 2 (volume : Measure ℂ) :=
  (zeroExtendFun_memLp T u).toLp (zeroExtendFun T u)

private theorem zeroExtensionLp_ae (T : Set ℂ) [CompactSpace T]
    (u : Lp ℂ 2 (restrictedVolume T)) :
    zeroExtensionLp T u =ᵐ[volume] zeroExtendFun T u :=
  MemLp.coeFn_toLp (zeroExtendFun_memLp T u)

/-- Isometric complex-linear extension by zero from the actual Euclidean subtype measure. -/
def zeroExtension (T : Set ℂ) [CompactSpace T] :
    Lp ℂ 2 (restrictedVolume T) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℂ) where
  toFun := zeroExtensionLp T
  map_add' u v := by
    apply Lp.ext
    filter_upwards [zeroExtensionLp_ae T (u + v),
      zeroExtendFun_ae_congr T (Lp.coeFn_add u v), zeroExtensionLp_ae T u,
      zeroExtensionLp_ae T v, Lp.coeFn_add (zeroExtensionLp T u) (zeroExtensionLp T v)]
      with z hsum hsrc hu hv hadd
    rw [hsum, hsrc, zeroExtendFun_add, hadd]
    simp only [Pi.add_apply, hu, hv]
  map_smul' c u := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [zeroExtensionLp_ae T (c • u),
      zeroExtendFun_ae_congr T (Lp.coeFn_smul c u), zeroExtensionLp_ae T u,
      Lp.coeFn_smul c (zeroExtensionLp T u)] with z hsmul hsrc hu hcoe
    rw [hsmul, hsrc, zeroExtendFun_smul, hcoe]
    simp only [Pi.smul_apply, hu]
  norm_map' u := by
    change ‖zeroExtensionLp T u‖ = ‖u‖
    rw [zeroExtensionLp, Lp.norm_toLp, zeroExtendFun_eLpNorm, Lp.norm_def]

/-- The ambient representative is the genuine pointwise zero extension. -/
theorem zeroExtension_ae (T : Set ℂ) [CompactSpace T]
    (u : Lp ℂ 2 (restrictedVolume T)) :
    zeroExtension T u =ᵐ[volume] Function.extend Subtype.val (u : T → ℂ) 0 :=
  zeroExtensionLp_ae T u

/-- On restrictions of continuous functions, zero extension is multiplication by
the indicator of the compact set, almost everywhere in ordinary Euclidean area. -/
theorem zeroExtension_restrictedLp_ae (T : Set ℂ) [CompactSpace T]
    (f : ℂ → ℂ) (hf : Continuous f) :
    zeroExtension T (restrictedLp T f hf) =ᵐ[volume] T.indicator f := by
  exact (zeroExtension_ae T _).trans (by
    change zeroExtendFun T (restrictedLp T f hf) =ᵐ[volume] T.indicator f
    simpa only [zeroExtendFun_eq_indicator] using
      zeroExtendFun_ae_congr T (restrictedLp_ae T f hf))

end GapFamily.Analytic.LocalSobolev
