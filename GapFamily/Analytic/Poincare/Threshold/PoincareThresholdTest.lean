import GapFamily.Analytic.Foundation.CompactTestIntegral
import GapFamily.Analytic.Poincare.PoincareLaplacianTest
import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdModular

/-! Literal hyperbolic compact testing of the canonical full threshold seed. -/
noncomputable section
namespace GapFamily.Analytic.PoincareThresholdWeak
open Set MeasureTheory UpperHalfPlane PoincareCanonical PoincareWeak
open scoped ContDiff

/-- The entire hyperbolic volume density is part of the fixed compact test. -/
def hyperbolicTestWeight (ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  star (ψ z / (z.im : ℂ) ^ 2)

theorem hyperbolicTestWeight_tsupport_subset (ψ : ℂ → ℂ) :
    tsupport (hyperbolicTestWeight ψ) ⊆ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport ψ)
  intro z hz
  apply subset_tsupport ψ
  intro he
  apply hz
  simp [hyperbolicTestWeight, he]

theorem hyperbolicTestWeight_continuous {ψ : ℂ → ℂ} (hψ : Continuous ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) : Continuous (hyperbolicTestWeight ψ) :=
  (testDivideHeightSquare_continuous hψ hs).star

theorem hyperbolicTestWeight_hasCompactSupport {ψ : ℂ → ℂ}
    (hc : HasCompactSupport ψ) : HasCompactSupport (hyperbolicTestWeight ψ) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (hyperbolicTestWeight_tsupport_subset ψ)

/-- A bounded complex-linear functional on the actual compact uniform-norm space. -/
def hyperbolicCompactTest (K : Set ℂ) [CompactSpace K] (ψ : ℂ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) (hψK : tsupport ψ ⊆ K) : C(K, ℂ) →L[ℂ] ℂ :=
  compactTestIntegral K (hyperbolicTestWeight ψ)
    (hyperbolicTestWeight_continuous hψ hs) (hyperbolicTestWeight_hasCompactSupport hc)
    ((hyperbolicTestWeight_tsupport_subset ψ).trans hψK)

/-- Compact-family testing is an ordinary convergent integral, even if the
ambient representative is specified only on the compact observation set. -/
theorem hyperbolicCompactTest_integrable (K : Set ℂ) [CompactSpace K] (ψ : ℂ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) (hψK : tsupport ψ ⊆ K)
    (A : C(K, ℂ)) (f : ℂ → ℂ) (hmatch : ∀ z : K, A z = f z) :
    Integrable (fun z : ℂ => star (ψ z) * f z / (z.im : ℂ) ^ 2) := by
  have h := compactTestIntegral_integrable K (hyperbolicTestWeight ψ)
    (hyperbolicTestWeight_continuous hψ hs) (hyperbolicTestWeight_hasCompactSupport hc)
    ((hyperbolicTestWeight_tsupport_subset ψ).trans hψK) A f hmatch
  simpa [hyperbolicTestWeight, div_mul_eq_mul_div] using h

/-- The functional is literally the required test integral, with the test alone conjugated. -/
theorem hyperbolicCompactTest_apply (K : Set ℂ) [CompactSpace K] (ψ : ℂ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) (hψK : tsupport ψ ⊆ K)
    (A : C(K, ℂ)) (f : ℂ → ℂ) (hmatch : ∀ z : K, A z = f z) :
    hyperbolicCompactTest K ψ hψ hc hs hψK A =
      ∫ z : ℂ, star (ψ z) * f z / (z.im : ℂ) ^ 2 := by
  have h := compactTestIntegral_apply K (hyperbolicTestWeight ψ)
    (hyperbolicTestWeight_continuous hψ hs) (hyperbolicTestWeight_hasCompactSupport hc)
    ((hyperbolicTestWeight_tsupport_subset ψ).trans hψK) A f hmatch
  simpa [hyperbolicCompactTest, hyperbolicTestWeight, div_mul_eq_mul_div] using h

/-- The canonical upper function is the actual compact continuation's zero value. -/
theorem thresholdSeed_ofComplex_eq_continuation {K : Set ℂ} [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (D : Continuation K) (J : ℤ) (z : K) :
    D.family J 0 z = thresholdSeed J (ofComplex z) := by
  let τ : UpperHalfPlane := ⟨z, hKH z.property⟩
  change D.family J 0 z = thresholdSeed J (ofComplex (τ : ℂ))
  rw [ofComplex_apply]
  exact (thresholdSeed_eq_continuation D J τ z.property).symm

end GapFamily.Analytic.PoincareThresholdWeak
