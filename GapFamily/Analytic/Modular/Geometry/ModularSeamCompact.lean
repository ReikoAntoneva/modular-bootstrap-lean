import GapFamily.Analytic.Modular.Geometry.ModularSeamCover
import GapFamily.Analytic.Modular.Geometry.ModularSeamMeasure

/-!
# Uniform compact-neighborhood energy control across seams

A genuine finite closed-tile cover controls nonnegative invariant integrals
on every compact subset of the upper half-plane. Only subadditivity is used:
tile overlaps, boundary identifications, and the central matrix kernel do not
require a false disjointness assertion.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane
open scoped MatrixGroups Pointwise ENNReal

/-- A fixed finite tile cover controls the ordinary integral of every
nonnegative invariant integrable function, with no overlap restriction. -/
theorem modular_integral_bound_of_finite_cover
    {K : Set UpperHalfPlane} (Γ : Finset SL(2, ℤ))
    (hcover : K ⊆ ⋃ γ ∈ Γ, (γ • ·) '' ModularGroup.fd)
    (g : UpperHalfPlane → ℝ) (hpos : ∀ τ, 0 ≤ g τ)
    (hg : Integrable g modularMeasure)
    (hinv : ∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, g (γ • τ) = g τ) :
    IntegrableOn g K volume ∧
      (∫ τ in K, g τ) ≤ (Γ.card : ℝ) * ∫ τ, g τ ∂modularMeasure := by
  classical
  have htiles (γ : SL(2, ℤ)) : IntegrableOn g ((γ • ·) '' ModularGroup.fd) volume :=
    integrableOn_modular_translate_of_invariant hg hinv γ
  have hint : IntegrableOn g K volume :=
    (integrableOn_finset_iUnion.mpr (fun γ _ => htiles γ)).mono_set hcover
  refine ⟨hint, ?_⟩
  have htileIntegral (γ : SL(2, ℤ)) :
      (∫⁻ τ in (γ • ·) '' ModularGroup.fd, ENNReal.ofReal (g τ)) =
        ENNReal.ofReal (∫ τ, g τ ∂modularMeasure) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (htiles γ) (Filter.Eventually.of_forall hpos)]
    congr 1
    exact integral_modular_translate_of_invariant g hinv γ
  have hfinite : ∀ Δ : Finset SL(2, ℤ),
      (∫⁻ τ in ⋃ γ ∈ Δ, (γ • ·) '' ModularGroup.fd, ENNReal.ofReal (g τ)) ≤
        (Δ.card : ℝ≥0∞) * ENNReal.ofReal (∫ τ, g τ ∂modularMeasure) := by
    intro Δ
    induction Δ using Finset.induction_on with
    | empty => simp
    | @insert γ Δ hγ ih =>
      rw [Finset.set_biUnion_insert]
      apply (lintegral_union_le _ _ _).trans
      rw [htileIntegral]
      calc
        _ ≤ ENNReal.ofReal (∫ τ, g τ ∂modularMeasure) +
            (Δ.card : ℝ≥0∞) * ENNReal.ofReal (∫ τ, g τ ∂modularMeasure) :=
          add_le_add le_rfl ih
        _ = _ := by
          rw [Finset.card_insert_of_notMem hγ, Nat.cast_add, Nat.cast_one, add_mul]
          simp [add_comm]
  have hbound := (lintegral_mono_set hcover (f := fun τ => ENNReal.ofReal (g τ))).trans (hfinite Γ)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hpos)] at hbound
  have hmass : 0 ≤ ∫ τ, g τ ∂modularMeasure := integral_nonneg hpos
  have hcast : (Γ.card : ℝ≥0∞) * ENNReal.ofReal (∫ τ, g τ ∂modularMeasure) =
      ENNReal.ofReal ((Γ.card : ℝ) * ∫ τ, g τ ∂modularMeasure) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    simp
  rw [hcast] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound

/-- Every actual compact neighborhood has a uniform finite integral bound;
the constant depends only on its genuine finite closed-tile cover. -/
theorem exists_modular_compact_integral_bound {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ g : UpperHalfPlane → ℝ, (∀ τ, 0 ≤ g τ) →
      Integrable g modularMeasure →
      (∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, g (γ • τ) = g τ) →
      IntegrableOn g K volume ∧
        (∫ τ in K, g τ) ≤ (N : ℝ) * ∫ τ, g τ ∂modularMeasure := by
  obtain ⟨Γ, hΓ⟩ := exists_finite_modular_fd_cover hK
  exact ⟨Γ.card, fun g hp hg hi => modular_integral_bound_of_finite_cover Γ hΓ g hp hg hi⟩

namespace ModularGradient

/-- Value and gradient energy on every compact upper-half-plane neighborhood
are controlled by the actual modular graph norm, with one fixed constant. -/
theorem exists_compact_graphEnergy_bound {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ F : smoothCore,
      IntegrableOn (fun τ : UpperHalfPlane => ‖F.val τ‖ ^ 2 + frameEnergy F.val τ) K volume ∧
      (∫ τ in K, ‖F.val τ‖ ^ 2 + frameEnergy F.val τ) ≤
        (N : ℝ) * (‖value F‖ ^ 2 + ‖coreGradient F‖ ^ 2) := by
  obtain ⟨N, hN⟩ := exists_modular_compact_integral_bound hK
  refine ⟨N, fun F => ?_⟩
  have h := hN (fun τ => ‖F.val τ‖ ^ 2 + frameEnergy F.val τ)
    (fun τ => add_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    ((integrable_valueEnergy F).add (integrable_frameEnergy F))
    (fun γ τ => by rw [F.property.2.1 γ τ, frameEnergy_modularAction])
  rw [integral_add (integrable_valueEnergy F) (integrable_frameEnergy F),
    integral_valueEnergy_eq_norm_sq, integral_frameEnergy_eq_norm_sq] at h
  exact h

/-- The corresponding local value bound uses exactly the actual modular
`L²` norm of the smooth-core value. -/
theorem exists_compact_valueEnergy_bound {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ F : smoothCore,
      IntegrableOn (fun τ : UpperHalfPlane => ‖F.val τ‖ ^ 2) K volume ∧
      (∫ τ in K, ‖F.val τ‖ ^ 2) ≤ (N : ℝ) * ‖value F‖ ^ 2 := by
  obtain ⟨N, hN⟩ := exists_modular_compact_integral_bound hK
  refine ⟨N, fun F => ?_⟩
  have h := hN (fun τ => ‖F.val τ‖ ^ 2) (fun _ => sq_nonneg _)
    (integrable_valueEnergy F) (fun γ τ => by rw [F.property.2.1 γ τ])
  simpa only [integral_valueEnergy_eq_norm_sq] using h

/-- Full modular gradient energy controls ordinary hyperbolic energy on any
compact neighborhood, including all fundamental-domain seams. -/
theorem exists_compact_frameEnergy_bound {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ F : smoothCore, IntegrableOn (frameEnergy F.val) K volume ∧
      (∫ τ in K, frameEnergy F.val τ) ≤ (N : ℝ) * ‖coreGradient F‖ ^ 2 := by
  obtain ⟨N, hN⟩ := exists_modular_compact_integral_bound hK
  refine ⟨N, fun F => ?_⟩
  have h := hN (frameEnergy F.val) (fun τ => add_nonneg (sq_nonneg _) (sq_nonneg _))
    (integrable_frameEnergy F) (frameEnergy_modularAction F)
  simpa only [integral_frameEnergy_eq_norm_sq] using h

end ModularGradient
end GapFamily.Analytic
