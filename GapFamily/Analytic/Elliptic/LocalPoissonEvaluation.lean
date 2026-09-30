import GapFamily.Analytic.Elliptic.LocalPoissonRegularity
import GapFamily.Analytic.Elliptic.LocalLpContinuousClosedGraph

/-! Bounded continuous observation of the actual local weak-Poisson jet. -/
noncomputable section
namespace GapFamily.Analytic.LocalPoisson
open Set Filter MeasureTheory
open scoped Topology

/-- The continuous representative supplied by actual weak elliptic regularity. -/
def representative (U : Set ℂ) (hU : IsOpen U) (u : JetSpace U) : ℂ → ℂ :=
  (exists_continuousRepresentative U hU u).choose

theorem representative_continuousOn (U : Set ℂ) (hU : IsOpen U) (u : JetSpace U) :
    ContinuousOn (representative U hU u) U :=
  (exists_continuousRepresentative U hU u).choose_spec.1

theorem representative_ae (U : Set ℂ) (hU : IsOpen U) (u : JetSpace U) :
    representative U hU u =ᵐ[volume.restrict U] (fun z => valueCLM U u z) :=
  (exists_continuousRepresentative U hU u).choose_spec.2

theorem representative_add (U : Set ℂ) (hU : IsOpen U) (u v : JetSpace U) :
    EqOn (representative U hU (u + v))
      (representative U hU u + representative U hU v) U := by
  apply Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hU
    (representative_continuousOn U hU (u + v))
    ((representative_continuousOn U hU u).add (representative_continuousOn U hU v))
  have ha := ae_restrict_of_ae (μ := (volume : Measure ℂ)) (s := U)
    (Lp.coeFn_add (valueCLM U u) (valueCLM U v))
  filter_upwards [representative_ae U hU (u + v), representative_ae U hU u,
    representative_ae U hU v, ha] with z huv hu hv ha
  change representative U hU (u + v) z = representative U hU u z + representative U hU v z
  rw [huv, hu, hv, map_add, ha]
  rfl

theorem representative_smul (U : Set ℂ) (hU : IsOpen U) (c : ℂ) (u : JetSpace U) :
    EqOn (representative U hU (c • u)) (c • representative U hU u) U := by
  apply Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hU
    (representative_continuousOn U hU (c • u))
    ((representative_continuousOn U hU u).const_smul c)
  have hs := ae_restrict_of_ae (μ := (volume : Measure ℂ)) (s := U)
    (Lp.coeFn_smul c (valueCLM U u))
  filter_upwards [representative_ae U hU (c • u), representative_ae U hU u, hs]
    with z hcu hu hs
  change representative U hU (c • u) z = c • representative U hU u z
  rw [hcu, hu, map_smul, hs]
  rfl

/-- Restriction of the continuous representative of an actual distributional jet. -/
def localMap (U : Set ℂ) (hU : IsOpen U) (K : Set ℂ) (hKU : K ⊆ U) :
    JetSpace U →ₗ[ℂ] C(K, ℂ) where
  toFun u := ⟨fun z => representative U hU u z,
    (representative_continuousOn U hU u).comp_continuous continuous_subtype_val
      (fun z => hKU z.property)⟩
  map_add' u v := by
    apply ContinuousMap.ext
    intro z
    exact representative_add U hU u v (hKU z.property)
  map_smul' c u := by
    apply ContinuousMap.ext
    intro z
    exact representative_smul U hU c u (hKU z.property)

theorem localMap_ae (U : Set ℂ) (hU : IsOpen U) {K : Set ℂ}
    (hK : MeasurableSet K) (hKU : K ⊆ U) (u : JetSpace U) :
    localContinuousExtend (localMap U hU K hKU u) =ᵐ[volume.restrict K]
      (fun z => valueCLM U u z) := by
  filter_upwards [ae_restrict_mem hK,
    ae_restrict_of_ae_restrict_of_subset hKU (representative_ae U hU u)] with z hz heq
  rw [localContinuousExtend_apply _ hz]
  exact heq

/-- The ordinary L² closed-graph criterion applies to the proved representative. -/
def regularRestriction (U : Set ℂ) (hU : IsOpen U) (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ U) (hreg : K ⊆ closure (interior K)) : JetSpace U →L[ℂ] C(K, ℂ) :=
  localLpContinuousLinearMap hreg (valueCLM U) (localMap U hU K hKU)
    (localMap_ae U hU (isCompact_iff_compactSpace.mpr inferInstance).measurableSet hKU)

/-- No regularity of the compact observation set is needed: enlarge it first. -/
theorem localMap_continuous (U : Set ℂ) (hU : IsOpen U) (K : Set ℂ)
    [CompactSpace K] (hKU : K ⊆ U) : Continuous (localMap U hU K hKU) := by
  have hK : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
  obtain ⟨V, hV, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  let L := closure V
  let : CompactSpace L := isCompact_iff_compactSpace.mp hVc
  have hKL : K ⊆ L := hKV.trans subset_closure
  have hreg : L ⊆ closure (interior L) := closure_mono hV.subset_interior_closure
  let R := regularRestriction U hU L hVU hreg
  let A : JetSpace U →L[ℂ] C(K, ℂ) :=
    (ContinuousMap.compCLM ℂ ℂ (ContinuousMap.inclusion hKL)).comp R
  have hA : (localMap U hU K hKU : JetSpace U → C(K, ℂ)) = A := by
    funext u
    apply ContinuousMap.ext
    intro z
    rfl
  rw [hA]
  exact A.continuous

/-- Actual bounded observation of every weak-Poisson jet on a compact set. -/
def restriction (U : Set ℂ) (hU : IsOpen U) (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ U) : JetSpace U →L[ℂ] C(K, ℂ) where
  toLinearMap := localMap U hU K hKU
  cont := localMap_continuous U hU K hKU

theorem restriction_ae (U : Set ℂ) (hU : IsOpen U) (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ U) (u : JetSpace U) :
    localContinuousExtend (restriction U hU K hKU u) =ᵐ[volume.restrict K]
      (fun z => valueCLM U u z) :=
  localMap_ae U hU (isCompact_iff_compactSpace.mpr inferInstance).measurableSet hKU u

theorem restriction_bound (U : Set ℂ) (hU : IsOpen U) (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : JetSpace U) (z : K),
      ‖restriction U hU K hKU u z‖ ≤ C * ‖u‖ := by
  let R := restriction U hU K hKU
  refine ⟨‖R‖ + 1, by positivity, fun u z => ?_⟩
  exact ((R u).norm_coe_le_norm z).trans ((R.le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (by linarith : ‖R‖ ≤ ‖R‖ + 1) (norm_nonneg u)))

/-- Genuine pointwise uniqueness is on an open neighborhood, not on the compact
set alone; it therefore includes isolated and measure-zero observation points. -/
theorem restriction_eq_localRepresentative
    (U : Set ℂ) (hU : IsOpen U) (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U)
    (z : K) (u : JetSpace U) {V : Set ℂ} (hV : IsOpen V)
    (hz : (z : ℂ) ∈ V) (hVU : V ⊆ U) {G : ℂ → ℂ} (hG : ContinuousOn G V)
    (hGae : G =ᵐ[volume.restrict V] (fun w => valueCLM U u w)) :
    restriction U hU K hKU u z = G z := by
  have hr : representative U hU u =ᵐ[volume.restrict V] (fun w => valueCLM U u w) :=
    ae_restrict_of_ae_restrict_of_subset hVU (representative_ae U hU u)
  exact Measure.eqOn_open_of_ae_eq (μ := volume) (hr.trans hGae.symm) hV
    ((representative_continuousOn U hU u).mono hVU) hG hz

/-- Nested compact observation is coherent for the same actual jet. -/
theorem restriction_nested (U : Set ℂ) (hU : IsOpen U)
    (K₁ K₂ : Set ℂ) [CompactSpace K₁] [CompactSpace K₂]
    (h₁₂ : K₁ ⊆ K₂) (h₂U : K₂ ⊆ U) :
    restriction U hU K₁ (h₁₂.trans h₂U) =
      (ContinuousMap.compCLM ℂ ℂ (ContinuousMap.inclusion h₁₂)).comp
        (restriction U hU K₂ h₂U) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousMap.ext
  intro z
  rfl

end GapFamily.Analytic.LocalPoisson
