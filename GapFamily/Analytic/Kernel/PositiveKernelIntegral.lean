import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import GapFamily.Analytic.Transform.LaplaceTest
import GapFamily.Analytic.Kernel.PositiveKernelFeature

/-!
# Positive kernels under integral tests

Ordinary Bochner integration of Hilbert-space features turns finite Fourier
and height tests into a Gram matrix. Every integral is certified integrable;
this does not presume positivity of the still-unconstructed continued kernel.
-/

namespace GapFamily.Analytic

open MeasureTheory

attribute [local instance] Measure.Subtype.measureSpace
open scoped InnerProductSpace ComplexOrder ComplexConjugate BigOperators

local instance unitIntervalVolume_finite :
    IsFiniteMeasure (volume : Measure (Set.Icc (0 : ℝ) 1)) where
  measure_univ_lt_top := by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    simp

theorem integral_integral_inner {α β H : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {μ : Measure α} {ν : Measure β} {f : α → H} {g : β → H}
    (hf : Integrable f μ) (hg : Integrable g ν) :
    (∫ x, ∫ y, ⟪f x, g y⟫_ℂ ∂ν ∂μ) = ⟪∫ x, f x ∂μ, ∫ y, g y ∂ν⟫_ℂ := by
  simp_rw [integral_inner hg]
  calc
    _ = ∫ x, conj ⟪∫ y, g y ∂ν, f x⟫_ℂ ∂μ := by simp only [inner_conj_symm]
    _ = _ := by rw [integral_conj, integral_inner hf, inner_conj_symm]

/-- Any finite family of integrable feature tests has an actual positive Gram
pairing, with both integrations performed before taking the finite matrix. -/
theorem posSemidef_integral_feature {α ι H : Type*} [MeasurableSpace α] [Finite ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (μ : Measure α) (f : ι → α → H) (hf : ∀ i, Integrable (f i) μ) :
    Matrix.PosSemidef (Matrix.of fun i j => ∫ x, ∫ y, ⟪f i x, f j y⟫_ℂ ∂μ ∂μ) := by
  simp_rw [integral_integral_inner (hf _) (hf _)]
  exact Matrix.posSemidef_gram ℂ (fun i => ∫ x, f i x ∂μ)

noncomputable def laplaceHeightWeight (k : ℕ) : ℂ :=
  (Real.sqrt (laplaceHeight k) : ℂ)⁻¹

noncomputable def normalizedHeightDifference
    (K : Matrix UpperHalfPlane UpperHalfPlane ℂ) (k l : ℕ) (x y : ℝ) : ℂ :=
  laplaceHeightWeight k * laplaceHeightWeight l * K (laplacePoint k x) (laplacePoint l y) -
  laplaceHeightWeight k * laplaceHeightWeight (l+1) * K (laplacePoint k x) (laplacePoint (l+1) y) -
  laplaceHeightWeight (k+1) * laplaceHeightWeight l * K (laplacePoint (k+1) x) (laplacePoint l y) +
  laplaceHeightWeight (k+1) * laplaceHeightWeight (l+1) *
    K (laplacePoint (k+1) x) (laplacePoint (l+1) y)

noncomputable def fourierHeightFeature {H : Type*} [AddCommGroup H] [Module ℂ H]
    (φ : UpperHalfPlane → H) (j : ℤ) (k : ℕ) (x : Set.Icc (0 : ℝ) 1) : H :=
  horizontalPhase j x •
    (laplaceHeightWeight k • φ (laplacePoint k x) -
      laplaceHeightWeight (k+1) • φ (laplacePoint (k+1) x))

theorem conj_horizontalPhase (j : ℤ) (x : ℝ) :
    conj (horizontalPhase j x) = horizontalPhase (-j) x := by
  simp only [horizontalPhase, ← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, map_intCast,
    Complex.conj_I]
  ring

theorem inner_fourierHeightFeature {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (K : Matrix UpperHalfPlane UpperHalfPlane ℂ)
    (φ : UpperHalfPlane → H) (hφ : ∀ z w, ⟪φ z, φ w⟫_ℂ = K z w)
    (j J : ℤ) (k l : ℕ) (x y : Set.Icc (0 : ℝ) 1) :
    ⟪fourierHeightFeature φ j k x, fourierHeightFeature φ J l y⟫_ℂ =
      horizontalPhase (-j) x * normalizedHeightDifference K k l x y * horizontalPhase J y := by
  simp only [fourierHeightFeature, inner_smul_left, inner_smul_right,
    inner_sub_left, inner_sub_right, hφ, conj_horizontalPhase]
  simp only [normalizedHeightDifference, laplaceHeightWeight, map_inv₀, Complex.conj_ofReal]
  ring

theorem continuous_laplacePoint (k : ℕ) : Continuous (laplacePoint k) := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun x : ℝ => (⟨x, laplaceHeight k⟩ : ℂ))
  have h : Continuous (fun x : ℝ => (x : ℂ) + (laplaceHeight k : ℂ) * Complex.I) := by
    fun_prop
  convert h using 1
  funext x
  apply Complex.ext <;> simp

theorem continuous_fourierHeightFeature {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] {φ : UpperHalfPlane → H} (hφ : Continuous φ) (j : ℤ) (k : ℕ) :
    Continuous (fourierHeightFeature φ j k) := by
  have hp : Continuous (fun x : Set.Icc (0 : ℝ) 1 => horizontalPhase j x) := by
    unfold horizontalPhase
    fun_prop
  exact hp.smul (((hφ.comp (continuous_laplacePoint k)).comp continuous_subtype_val).const_smul
    (laplaceHeightWeight k) |>.sub
      (((hφ.comp (continuous_laplacePoint (k+1))).comp continuous_subtype_val).const_smul
        (laplaceHeightWeight (k+1))))

/-- The actual horizontal Fourier integrals of the four normalized heights are
positive whenever their continuous kernel has a Hilbert feature realization. -/
theorem posSemidef_fourierHeight_of_feature {ι H : Type*} [Finite ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : Matrix UpperHalfPlane UpperHalfPlane ℂ) (φ : UpperHalfPlane → H)
    (hφ : Continuous φ) (hinner : ∀ z w, ⟪φ z, φ w⟫_ℂ = K z w)
    (j : ι → ℤ) (k : ι → ℕ) :
    Matrix.PosSemidef (Matrix.of fun i l => ∫ x : Set.Icc (0 : ℝ) 1, ∫ y : Set.Icc (0 : ℝ) 1,
      horizontalPhase (-j i) x * normalizedHeightDifference K (k i) (k l) x y *
        horizontalPhase (j l) y) := by
  have hi (i : ι) : Integrable (fourierHeightFeature φ (j i) (k i)) :=
    (continuous_fourierHeightFeature hφ _ _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simpa only [inner_fourierHeightFeature K φ hinner] using
    posSemidef_integral_feature volume (fun i => fourierHeightFeature φ (j i) (k i)) hi

/-- A continuous positive kernel remains positive after the actual horizontal
Fourier projections and normalized adjacent-height differences. The Hilbert
space and its features are constructed from the given kernel internally. -/
theorem posSemidef_fourierHeight {ι : Type*} [Finite ι]
    (K : Matrix UpperHalfPlane UpperHalfPlane ℂ) (hK : K.PosSemidef)
    (hcont : Continuous (Function.uncurry K)) (j : ι → ℤ) (k : ι → ℕ) :
    Matrix.PosSemidef (Matrix.of fun i l => ∫ x : Set.Icc (0 : ℝ) 1, ∫ y : Set.Icc (0 : ℝ) 1,
      horizontalPhase (-j i) x * normalizedHeightDifference K (k i) (k l) x y *
        horizontalPhase (j l) y) :=
  posSemidef_fourierHeight_of_feature K (positiveKernelFeature K hK)
    (continuous_positiveKernelFeature K hK hcont) (inner_positiveKernelFeature K hK) j k

/-- The same result with the ordinary real interval integrals appearing in
the source's finite Fourier tests. -/
theorem posSemidef_fourierHeight_interval {ι : Type*} [Finite ι]
    (K : Matrix UpperHalfPlane UpperHalfPlane ℂ) (hK : K.PosSemidef)
    (hcont : Continuous (Function.uncurry K)) (j : ι → ℤ) (k : ι → ℕ) :
    Matrix.PosSemidef (Matrix.of fun i l => ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1,
      horizontalPhase (-j i) x * normalizedHeightDifference K (k i) (k l) x y *
        horizontalPhase (j l) y) := by
  have h := posSemidef_fourierHeight K hK hcont j k
  have hint (f : ℝ → ℂ) : (∫ x : Set.Icc (0 : ℝ) 1, f x) = ∫ x in 0..1, f x := by
    rw [integral_subtype measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have heq : (Matrix.of fun i l => ∫ x : Set.Icc (0 : ℝ) 1, ∫ y : Set.Icc (0 : ℝ) 1,
      horizontalPhase (-j i) x * normalizedHeightDifference K (k i) (k l) x y *
        horizontalPhase (j l) y) = (Matrix.of fun i l => ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1,
      horizontalPhase (-j i) x * normalizedHeightDifference K (k i) (k l) x y *
        horizontalPhase (j l) y) := by
    ext i l
    change (∫ x : Set.Icc (0 : ℝ) 1, ∫ y : Set.Icc (0 : ℝ) 1,
      horizontalPhase (-j i) x * normalizedHeightDifference K (k i) (k l) x y *
        horizontalPhase (j l) y) = ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1,
      horizontalPhase (-j i) x * normalizedHeightDifference K (k i) (k l) x y *
        horizontalPhase (j l) y
    calc
      _ = ∫ x : Set.Icc (0 : ℝ) 1, ∫ y : ℝ in 0..1,
          horizontalPhase (-j i) x * normalizedHeightDifference K (k i) (k l) x y *
            horizontalPhase (j l) y := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => hint (fun y =>
          horizontalPhase (-j i) x * normalizedHeightDifference K (k i) (k l) x y *
            horizontalPhase (j l) y))
      _ = _ := hint (fun x => ∫ y : ℝ in 0..1,
        horizontalPhase (-j i) x * normalizedHeightDifference K (k i) (k l) x y *
          horizontalPhase (j l) y)
  rw [heq] at h
  exact h

end GapFamily.Analytic
