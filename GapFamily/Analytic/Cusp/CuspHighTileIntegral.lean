import GapFamily.Analytic.Modular.Geometry.ModularSeamCompact

noncomputable section
namespace GapFamily.Analytic.CuspHighTileIntegral
open Set MeasureTheory UpperHalfPlane
open scoped MatrixGroups Pointwise ENNReal

/-- Finite actual subtile cover controls the genuine ordinary nonnegative integral.
The subset is arbitrary; no invariance of its boundary or height is assumed. -/
theorem modular_integral_bound_of_finite_subtile_cover
    {K S : Set UpperHalfPlane} (hS : S ⊆ ModularGroup.fd) (Γ : Finset SL(2, ℤ))
    (hcover : K ⊆ ⋃ γ ∈ Γ, (γ • ·) '' S)
    (g : UpperHalfPlane → ℝ) (hpos : ∀ τ, 0 ≤ g τ)
    (hg : Integrable g modularMeasure)
    (hinv : ∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, g (γ • τ) = g τ) :
    IntegrableOn g K volume ∧
      (∫ τ in K, g τ) ≤ (Γ.card : ℝ) *
        ∫ τ in S, g τ := by
  classical
  have htiles (γ : SL(2, ℤ)) :
      IntegrableOn g ((γ • ·) '' S) volume :=
    (integrableOn_modular_translate_of_invariant hg hinv γ).mono_set
      (Set.image_mono hS)
  have hint : IntegrableOn g K volume :=
    (integrableOn_finset_iUnion.mpr (fun γ _ => htiles γ)).mono_set hcover
  refine ⟨hint, ?_⟩
  have htileIntegral (γ : SL(2, ℤ)) :
      (∫⁻ τ in (γ • ·) '' S, ENNReal.ofReal (g τ)) =
        ENNReal.ofReal (∫ τ in S, g τ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (htiles γ) (Filter.Eventually.of_forall hpos)]
    congr 1
    rw [(measurePreserving_modularAction γ).setIntegral_image_emb
      (measurableEmbedding_modularAction γ) g (S)]
    simp only [hinv γ]
  have hfinite : ∀ Δ : Finset SL(2, ℤ),
      (∫⁻ τ in ⋃ γ ∈ Δ, (γ • ·) '' S,
        ENNReal.ofReal (g τ)) ≤
        (Δ.card : ℝ≥0∞) *
          ENNReal.ofReal (∫ τ in S, g τ) := by
    intro Δ
    induction Δ using Finset.induction_on with
    | empty => simp
    | @insert γ Δ hγ ih =>
      rw [Finset.set_biUnion_insert]
      apply (lintegral_union_le _ _ _).trans
      rw [htileIntegral]
      calc
        _ ≤ ENNReal.ofReal (∫ τ in S, g τ) +
            (Δ.card : ℝ≥0∞) *
              ENNReal.ofReal (∫ τ in S, g τ) :=
          add_le_add le_rfl ih
        _ = _ := by
          rw [Finset.card_insert_of_notMem hγ, Nat.cast_add, Nat.cast_one, add_mul]
          simp [add_comm]
  have hbound :=
    (lintegral_mono_set hcover (f := fun τ => ENNReal.ofReal (g τ))).trans (hfinite Γ)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hpos)] at hbound
  have hmass : 0 ≤ ∫ τ in S, g τ :=
    integral_nonneg hpos
  have hcast : (Γ.card : ℝ≥0∞) *
      ENNReal.ofReal (∫ τ in S, g τ) =
      ENNReal.ofReal ((Γ.card : ℝ) *
        ∫ τ in S, g τ) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    simp
  rw [hcast] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound

end GapFamily.Analytic.CuspHighTileIntegral
