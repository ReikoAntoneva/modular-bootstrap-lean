import GapFamily.NodeSpectrum
import GapFamily.GapFamilyContract

/-!
# The unique first primary of a strict node marker

A distinguished scalar node below every other node remains the unique first
primary after regrouping. Its multiplicity is the cardinality of its actual
singleton fibre; no choice of spectral multiplicities is made here.
-/

noncomputable section

namespace GapFamily

variable {ι : Type*}

/-- A coordinate with exactly one original node has multiplicity one. -/
theorem coordinateSpectrum_multiplicity_one_of_unique
    (coordinate : ι → ℝ × ℝ) (i₀ : ι)
    (hunique : ∀ i, coordinate i = coordinate i₀ → i = i₀) :
    (coordinateSpectrum coordinate).multiplicity (coordinate i₀) = 1 := by
  calc
    (coordinateSpectrum coordinate).multiplicity (coordinate i₀) =
        Regrouping.multiplicity coordinate ⟨coordinate i₀, ⟨i₀, rfl⟩⟩ :=
      coordinateSpectrum_multiplicity coordinate ⟨coordinate i₀, ⟨i₀, rfl⟩⟩
    _ = 1 := by
      unfold Regrouping.multiplicity
      apply Nat.card_eq_one_iff_exists.mpr
      refine ⟨⟨i₀, rfl⟩, ?_⟩
      intro i
      apply Subtype.ext
      exact hunique i.val (congrArg Subtype.val i.property)

/-- A scalar marker strictly below all other nodes is the unique unit primary
at the attained minimum of the regrouped spectrum. -/
theorem nodeSpectrum_hasUnitScalarGap
    (c : ℝ) (E : ι → ℝ) (J : ι → ℤ) (b : ℝ) (i₀ : ι)
    (hmarker : E i₀ = b) (hscalar : J i₀ = 0)
    (hstrict : ∀ i, i ≠ i₀ → b < E i) :
    HasUnitScalarGap (nodeSpectrum c E J) (shift c + b) := by
  have hlower : ∀ i, b ≤ E i := by
    intro i
    by_cases hi : i = i₀
    · simp [hi, hmarker]
    · exact (hstrict i hi).le
  have hfirst : ∀ i, E i = b → i = i₀ := by
    intro i hi
    by_contra hne
    have := hstrict i hne
    linarith
  have hcoordinate : nodeCoordinate c E J i₀ =
      ((shift c + b) / 2, (shift c + b) / 2) := by
    simp [nodeCoordinate, hmarker, hscalar]
  refine ⟨nodeSpectrum_hasGap c E J b hlower ⟨i₀, hmarker⟩, ?_, ?_, ?_⟩
  · rw [← hcoordinate]
    exact ⟨i₀, rfl⟩
  · rw [← hcoordinate]
    apply coordinateSpectrum_multiplicity_one_of_unique
    intro i hi
    apply hfirst i
    have he := congrArg (energy c) hi
    simpa only [energy_nodeCoordinate, hmarker] using he
  · rintro p ⟨i, rfl⟩ hi
    rw [dimension_nodeCoordinate] at hi
    have he : E i = b := by linarith
    simpa only [hfirst i he] using hcoordinate

end GapFamily
