import BTZEntropy.Construction.FixedFamilyData

/-!
# Selectors retaining the complete fixed-cutoff construction

A selector chooses actual initial and tail cell data at each admitted
charge and marker. Its spectrum is the permanent spectrum of that datum.
Admission predicates can impose common quantitative bounds and fix the
reference density, while allowing all node choices satisfying those bounds.
-/

noncomputable section

open Set

namespace BTZEntropy.Construction

open GapFamily

/-- One simultaneous choice of actual construction data. The charge
threshold precedes every marker and every individual node selector. -/
abbrev FixedFamilySelector {B : ℝ} (g : FixedFamilyGeometry B) (a₀ : ℝ) :=
  ∀ (a : ℝ), a₀ ≤ a → ∀ (δ : ℝ), δ ∈ Ico (0 : ℝ) B → FixedFamilyDatum g a δ

namespace FixedFamilySelector

variable {B : ℝ} {g : FixedFamilyGeometry B} {a₀ : ℝ}

/-- Parameters below the threshold and excluded marker parameters are filled
with the empty spectrum. All admitted entries keep their actual data. -/
def spectrum (σ : FixedFamilySelector g a₀) (a : ℝ) (δ : ℝ) : Spectrum :=
  if h : a₀ ≤ a ∧ δ ∈ Ico (0 : ℝ) B then
    (σ a h.1 δ h.2).spectrum
  else ⟨∅, fun _ => 0⟩

theorem spectrum_eq (σ : FixedFamilySelector g a₀) {a : ℝ} (ha : a₀ ≤ a)
    {δ : ℝ} (hδ : δ ∈ Ico (0 : ℝ) B) :
    σ.spectrum a δ = (σ a ha δ hδ).spectrum := by
  simp [spectrum, ha, hδ]

/-- Admission can express common degree, mass, variation, and reference
constraints on actual data, without choosing spectra independently. -/
def admitted (accept : ∀ (a : ℝ) (δ : ℝ), FixedFamilyDatum g a δ → Prop) :
    Set (FixedFamilySelector g a₀) :=
  {σ | ∀ (a : ℝ) (ha : a₀ ≤ a) (δ : ℝ) (hδ : δ ∈ Ico (0 : ℝ) B),
    accept a δ (σ a ha δ hδ)}

/-- Pointwise actual data suffice to inhabit the entire selector class.
The premise concerns finite cells and local repair choices, not spectra. -/
theorem admitted_nonempty
    (accept : ∀ (a : ℝ) (δ : ℝ), FixedFamilyDatum g a δ → Prop)
    (hdata : ∀ (a : ℝ), a₀ ≤ a → ∀ (δ : ℝ), δ ∈ Ico (0 : ℝ) B →
      ∃ d : FixedFamilyDatum g a δ, accept a δ d) :
    (admitted (a₀ := a₀) accept).Nonempty := by
  classical
  let σ : FixedFamilySelector g a₀ :=
    fun a ha δ hδ => Classical.choose (hdata a ha δ hδ)
  refine ⟨σ, ?_⟩
  intro a ha δ hδ
  exact Classical.choose_spec (hdata a ha δ hδ)

/-- Every retained datum realizes the fixed cutoff in its own literal
permanent spectrum, uniformly in every selector of any nonempty subclass. -/
theorem uniformFixedCutoffFamily (hB : 0 < B) (ha₀ : 1 ≤ a₀)
    (selectors : Set (FixedFamilySelector g a₀)) (hselectors : selectors.Nonempty) :
    UniformFixedCutoffFamily B selectors spectrum := by
  refine ⟨hB, hselectors, a₀, ha₀, ?_⟩
  intro σ _ a ha δ hδ
  rw [σ.spectrum_eq ha hδ]
  exact (σ a ha δ hδ).realizesFixedCutoff

/-- Uniform construction from a specified common admission condition.
The nonempty class retains all admitted node choices and their histories. -/
theorem uniformFixedCutoffFamily_of_data (hB : 0 < B) (ha₀ : 1 ≤ a₀)
    (accept : ∀ (a : ℝ) (δ : ℝ), FixedFamilyDatum g a δ → Prop)
    (hdata : ∀ (a : ℝ), a₀ ≤ a → ∀ (δ : ℝ), δ ∈ Ico (0 : ℝ) B →
      ∃ d : FixedFamilyDatum g a δ, accept a δ d) :
    UniformFixedCutoffFamily B (admitted (a₀ := a₀) accept) spectrum :=
  uniformFixedCutoffFamily hB ha₀ _ (admitted_nonempty accept hdata)

/-- The selected spectrum and finite state prefix refer to the same datum.
This exposes the exact node list needed by compact-support observables. -/
theorem permanentAtomList_eq (σ : FixedFamilySelector g a₀) {a : ℝ} (ha : a₀ ≤ a)
    {δ : ℝ} (hδ : δ ∈ Ico (0 : ℝ) B) (n : ℕ) :
    (σ a ha δ hδ).permanentData.permanentAtomList (g.start + n) =
      (δ, 0) :: ((σ a ha δ hδ).state n).nodes :=
  (σ a ha δ hδ).permanentAtomList_eq n

end FixedFamilySelector

end BTZEntropy.Construction
