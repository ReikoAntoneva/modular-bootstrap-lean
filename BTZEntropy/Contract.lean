import BTZEntropy.Observable
import BTZEntropy.Coefficient
import GapFamily.GapFamilyContract

/-!
# The uniform smooth-entropy target

These predicates describe families at every sufficiently large real shift
`a`, with charge `c = 12*a + 1`. The selector class is nonempty, and all
thresholds and error constants are uniform over the fixed gap band and
admitted selectors. The coefficients are given by the finite saddle
algorithm in `Coefficient`.
-/

noncomputable section

open Set
open scoped BigOperators

namespace BTZEntropy

universe u

/-- A spectrum at gap `δ`, with every other primary strictly above the fixed
clearing cutoff `B`. The scalar marker itself is allowed below `B`. -/
def RealizesFixedCutoff (B : ℝ) (a : ℝ) (δ : ℝ)
    (s : GapFamily.Spectrum) : Prop :=
  GapFamily.RealizesGap a δ s ∧
    ∀ p ∈ s.support,
      p ≠ ((a + δ) / 2,
        (a + δ) / 2) →
      B < GapFamily.energy (GapFamily.gapFamilyCharge a) p

/-- The fixed-cutoff family property, with one threshold for all admitted
selectors and all `δ ∈ [0,B)`. This is stronger than `FixedGapFamilyExists`.
The selector class is nonempty; identifying it with actual construction
choices is not hidden in the definition. -/
def UniformFixedCutoffFamily {ι : Type u} (B : ℝ) (selectors : Set ι)
    (family : ι → ℝ → ℝ → GapFamily.Spectrum) : Prop :=
  0 < B ∧ selectors.Nonempty ∧
    ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ σ ∈ selectors, ∀ a, a₀ ≤ a →
      ∀ δ ∈ Ico (0 : ℝ) B, RealizesFixedCutoff B a δ (family σ a δ)

/-- Explicit uniform big-O on any compact positive energy-ratio interval.
The constant and real threshold precede the selector, gap and energy
ratio, so they cannot depend on those individual choices. They may depend
on the fixed class and its common construction bounds. -/
def UniformRemainder {ι : Type u} (B : ℝ) (selectors : Set ι) (q : ℕ)
    (error : ι → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ L U : ℝ, 0 < L → L ≤ U →
    ∃ C : ℝ, 0 < C ∧ ∃ a₀ : ℝ, 1 ≤ a₀ ∧
      ∀ σ ∈ selectors, ∀ a, a₀ ≤ a → ∀ δ ∈ Ico (0 : ℝ) B,
        ∀ x ∈ Icc L U,
          |error σ a δ x| ≤ C / (GapFamily.gapFamilyCharge a) ^ q

/-- The entropy is used only where its full-state count is strictly positive,
uniformly on the same parameter sets as the asymptotic expansion. -/
def UniformCountPositive {ι : Type u} (B : ℝ) (selectors : Set ι)
    (family : ι → ℝ → ℝ → GapFamily.Spectrum) (φ : SmoothKernel) : Prop :=
  ∀ L U : ℝ, 0 < L → L ≤ U →
    ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ σ ∈ selectors, ∀ a, a₀ ≤ a →
      ∀ δ ∈ Ico (0 : ℝ) B, ∀ x ∈ Icc L U,
        0 < smoothCount φ (GapFamily.gapFamilyCharge a) (family σ a δ)
          (x * GapFamily.gapFamilyCharge a)

/-- The prescribed entropy polynomial, including its constant term. The
coefficient sequence depends only on the kernel and the energy ratio. -/
def entropyTruncation (φ : SmoothKernel) (x c : ℝ) (P : ℕ) : ℝ :=
  leadingAction x c - (1 / 2 : ℝ) * Real.log c +
    ∑ m ∈ Finset.range (P + 1), entropyCoefficient φ x m / c ^ m

/-- Proposition 2.3's expansion property for a supplied family. `P = 0`
is included, and the remainder has order `c ^ (-(P+1))`. -/
def UniformSmoothEntropyExpansion {ι : Type u} (B : ℝ) (selectors : Set ι)
    (family : ι → ℝ → ℝ → GapFamily.Spectrum) (φ : SmoothKernel) : Prop :=
  UniformCountPositive B selectors family φ ∧
    ∀ P : ℕ, UniformRemainder B selectors (P + 1)
      (fun σ a δ x =>
        smoothEntropy φ (GapFamily.gapFamilyCharge a) (family σ a δ)
            (x * GapFamily.gapFamilyCharge a) -
          entropyTruncation φ x (GapFamily.gapFamilyCharge a) P)

/-- The full smooth BTZ property of a fixed-cutoff family and its
admissible selector class. -/
def SmoothBTZFamily {ι : Type u} (B : ℝ) (selectors : Set ι)
    (family : ι → ℝ → ℝ → GapFamily.Spectrum) : Prop :=
  UniformFixedCutoffFamily B selectors family ∧
    ∀ φ : SmoothKernel, UniformSmoothEntropyExpansion B selectors family φ

/-- Proposition 2.3 for each fixed nonnegative gap. A single spectral family
has both limits from Theorem 2.2(ii) and works for every compact smooth kernel
and every expansion order. The error
bound is uniform over each compact positive energy-ratio interval, at every
sufficiently large real `a`; the energy is exactly `x * (12*a + 1)`. -/
def FixedGapSmoothEntropyFamilyExists : Prop :=
  ∀ δ : ℝ, 0 ≤ δ → ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∃ family : ℝ → GapFamily.Spectrum,
    (∀ a : ℝ, a₀ ≤ a → GapFamily.RealizesGap a δ (family a)) ∧
    Filter.Tendsto
      (fun a => GapFamily.firstShiftedEnergy (GapFamily.gapFamilyCharge a) (family a))
      Filter.atTop (nhds δ) ∧
    Filter.Tendsto
      (fun a => GapFamily.firstShiftedEnergy (GapFamily.gapFamilyCharge a) (family a) / a)
      Filter.atTop (nhds 0) ∧
    ∀ (φ : SmoothKernel) (P : ℕ) (L U : ℝ), 0 < L → L ≤ U →
      ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, a₀ ≤ A ∧
        ∀ a : ℝ, A ≤ a → ∀ x ∈ Icc L U,
          0 < smoothCount φ (GapFamily.gapFamilyCharge a) (family a)
            (x * GapFamily.gapFamilyCharge a) ∧
          |smoothEntropy φ (GapFamily.gapFamilyCharge a) (family a)
              (x * GapFamily.gapFamilyCharge a) -
            entropyTruncation φ x (GapFamily.gapFamilyCharge a) P| ≤
            C / GapFamily.gapFamilyCharge a ^ (P + 1)

end BTZEntropy
