import GapFamily.Analytic.Modular.Geometry.ModularSeamCompact

/-!
# Compact seam energy controlled below one finite height

The actual finite cover by translated truncated fundamental domains retains a
common height bound. Invariance and subadditivity control every compact upper
neighborhood by the modular energy below that height, including all seams.
-/

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory UpperHalfPlane
open scoped MatrixGroups Pointwise ENNReal

/-- Restriction of the modular measure below a height is exactly the ordinary
hyperbolic measure on the closed truncated fundamental domain. -/
theorem integral_modular_truncatedFundamentalDomain (H : ℝ) (g : UpperHalfPlane → ℝ) :
    (∫ τ in ModularGroup.truncatedFundamentalDomain H, g τ) =
      ∫ τ in {τ : UpperHalfPlane | τ.im ≤ H}, g τ ∂modularMeasure := by
  rw [modularMeasure, Measure.restrict_restrict
    (isClosed_le UpperHalfPlane.continuous_im continuous_const).measurableSet]
  have hset : ModularGroup.truncatedFundamentalDomain H =
      {τ : UpperHalfPlane | τ.im ≤ H} ∩ ModularGroup.fd := by
    ext τ
    exact and_comm
  rw [hset]

/-- A finite cover by actual truncated tiles retains the same finite-height
restriction on the controlling invariant integral. -/
theorem modular_integral_bound_of_finite_truncated_cover
    {K : Set UpperHalfPlane} (H : ℝ) (Γ : Finset SL(2, ℤ))
    (hcover : K ⊆ ⋃ γ ∈ Γ, (γ • ·) '' ModularGroup.truncatedFundamentalDomain H)
    (g : UpperHalfPlane → ℝ) (hpos : ∀ τ, 0 ≤ g τ)
    (hg : Integrable g modularMeasure)
    (hinv : ∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, g (γ • τ) = g τ) :
    IntegrableOn g K volume ∧
      (∫ τ in K, g τ) ≤ (Γ.card : ℝ) *
        ∫ τ in {τ : UpperHalfPlane | τ.im ≤ H}, g τ ∂modularMeasure := by
  classical
  have htiles (γ : SL(2, ℤ)) :
      IntegrableOn g ((γ • ·) '' ModularGroup.truncatedFundamentalDomain H) volume :=
    (integrableOn_modular_translate_of_invariant hg hinv γ).mono_set
      (Set.image_mono (fun _ hτ => hτ.1))
  have hint : IntegrableOn g K volume :=
    (integrableOn_finset_iUnion.mpr (fun γ _ => htiles γ)).mono_set hcover
  refine ⟨hint, ?_⟩
  have htileIntegral (γ : SL(2, ℤ)) :
      (∫⁻ τ in (γ • ·) '' ModularGroup.truncatedFundamentalDomain H, ENNReal.ofReal (g τ)) =
        ENNReal.ofReal (∫ τ in {τ : UpperHalfPlane | τ.im ≤ H}, g τ ∂modularMeasure) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (htiles γ) (Filter.Eventually.of_forall hpos)]
    congr 1
    rw [(measurePreserving_modularAction γ).setIntegral_image_emb
      (measurableEmbedding_modularAction γ) g (ModularGroup.truncatedFundamentalDomain H)]
    simp only [hinv γ, integral_modular_truncatedFundamentalDomain]
  have hfinite : ∀ Δ : Finset SL(2, ℤ),
      (∫⁻ τ in ⋃ γ ∈ Δ, (γ • ·) '' ModularGroup.truncatedFundamentalDomain H,
        ENNReal.ofReal (g τ)) ≤
        (Δ.card : ℝ≥0∞) *
          ENNReal.ofReal (∫ τ in {τ : UpperHalfPlane | τ.im ≤ H}, g τ ∂modularMeasure) := by
    intro Δ
    induction Δ using Finset.induction_on with
    | empty => simp
    | @insert γ Δ hγ ih =>
      rw [Finset.set_biUnion_insert]
      apply (lintegral_union_le _ _ _).trans
      rw [htileIntegral]
      calc
        _ ≤ ENNReal.ofReal (∫ τ in {τ : UpperHalfPlane | τ.im ≤ H}, g τ ∂modularMeasure) +
            (Δ.card : ℝ≥0∞) *
              ENNReal.ofReal (∫ τ in {τ : UpperHalfPlane | τ.im ≤ H}, g τ ∂modularMeasure) :=
          add_le_add le_rfl ih
        _ = _ := by
          rw [Finset.card_insert_of_notMem hγ, Nat.cast_add, Nat.cast_one, add_mul]
          simp [add_comm]
  have hbound :=
    (lintegral_mono_set hcover (f := fun τ => ENNReal.ofReal (g τ))).trans (hfinite Γ)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hpos)] at hbound
  have hmass : 0 ≤ ∫ τ in {τ : UpperHalfPlane | τ.im ≤ H}, g τ ∂modularMeasure :=
    integral_nonneg hpos
  have hcast : (Γ.card : ℝ≥0∞) *
      ENNReal.ofReal (∫ τ in {τ : UpperHalfPlane | τ.im ≤ H}, g τ ∂modularMeasure) =
      ENNReal.ofReal ((Γ.card : ℝ) *
        ∫ τ in {τ : UpperHalfPlane | τ.im ≤ H}, g τ ∂modularMeasure) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    simp
  rw [hcast] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound

/-- One height and one finite multiplicity control all nonnegative invariant
integrands on the given compact upper-half-plane set. -/
theorem exists_modular_compact_truncated_integral_bound
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ H : ℝ, 1 ≤ H ∧ ∃ N : ℕ, ∀ g : UpperHalfPlane → ℝ, (∀ τ, 0 ≤ g τ) →
      Integrable g modularMeasure →
      (∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, g (γ • τ) = g τ) →
      IntegrableOn g K volume ∧
        (∫ τ in K, g τ) ≤ (N : ℝ) *
          ∫ τ in {τ : UpperHalfPlane | τ.im ≤ H}, g τ ∂modularMeasure := by
  obtain ⟨H, Γ, hΓ⟩ := exists_finite_modular_truncated_cover hK
  have hcover : K ⊆ ⋃ γ ∈ Γ,
      (γ • ·) '' ModularGroup.truncatedFundamentalDomain (max 1 H) := by
    apply hΓ.trans
    apply Set.iUnion_mono
    intro γ
    apply Set.iUnion_mono
    intro hγ
    exact Set.image_mono (fun τ hτ => ⟨hτ.1, hτ.2.trans (le_max_right 1 H)⟩)
  exact ⟨max 1 H, le_max_left 1 H, Γ.card,
    fun g hp hg hi => modular_integral_bound_of_finite_truncated_cover
      (max 1 H) Γ hcover g hp hg hi⟩

namespace ModularGradient

/-- The actual frame energy on a compact neighborhood, including seams, is
controlled solely by the actual modular frame energy below one finite height. -/
theorem exists_compact_truncated_frameEnergy_bound
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ H : ℝ, 1 ≤ H ∧ ∃ N : ℕ, ∀ F : smoothCore,
      IntegrableOn (frameEnergy F.val) K volume ∧
        (∫ τ in K, frameEnergy F.val τ) ≤ (N : ℝ) *
          ∫ τ in {τ : UpperHalfPlane | τ.im ≤ H}, frameEnergy F.val τ ∂modularMeasure := by
  obtain ⟨H, hH, N, hN⟩ := exists_modular_compact_truncated_integral_bound hK
  exact ⟨H, hH, N, fun F => hN (frameEnergy F.val)
    (fun τ => add_nonneg (sq_nonneg _) (sq_nonneg _))
    (integrable_frameEnergy F) (frameEnergy_modularAction F)⟩

end ModularGradient
end GapFamily.Analytic
