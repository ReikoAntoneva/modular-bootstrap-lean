import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Hilbert features of a scalar positive kernel

Finite scalar combinations carry the kernel's actual semidefinite form.
Completing the resulting seminormed inner product space removes its null vectors
and gives a complete Hilbert space. The point features have the prescribed
inner product, and a jointly continuous kernel gives continuous features.
-/

open scoped ComplexConjugate ComplexOrder Topology
open InnerProductSpace

noncomputable section

namespace GapFamily.Analytic

/-- Finite scalar combinations of kernel sections. -/
def PositiveKernelSpan {α : Type*} (K : Matrix α α ℂ) (_hK : K.PosSemidef) := α →₀ ℂ

instance {α : Type*} (K : Matrix α α ℂ) (hK : K.PosSemidef) :
    AddCommGroup (PositiveKernelSpan K hK) := inferInstanceAs (AddCommGroup (α →₀ ℂ))

instance {α : Type*} (K : Matrix α α ℂ) (hK : K.PosSemidef) :
    Module ℂ (PositiveKernelSpan K hK) := inferInstanceAs (Module ℂ (α →₀ ℂ))

instance {α : Type*} (K : Matrix α α ℂ) (hK : K.PosSemidef) :
    PreInnerProductSpace.Core ℂ (PositiveKernelSpan K hK) where
  inner f g := (f : α →₀ ℂ).sum fun i fi => (g : α →₀ ℂ).sum fun j gj => star fi * K i j * gj
  conj_inner_symm f g := by
    change α →₀ ℂ at f g
    simp only [map_finsuppSum, starRingEnd_apply, star_mul, star_star]
    rw [Finsupp.sum_comm]
    congr! 6
    rw [hK.isHermitian.apply]
    ring
  add_left f g h := by
    change α →₀ ℂ at f g h
    change ((f + g : α →₀ ℂ).sum _) = _
    rw [Finsupp.sum_add_index'] <;> simp [← Finsupp.sum_add, add_mul]
  smul_left f g r := by
    change α →₀ ℂ at f g
    change ((r • f : α →₀ ℂ).sum _) = _
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.mul_sum, ← mul_assoc]
  re_inner_nonneg f := by
    exact (Complex.nonneg_iff.mp (hK.2 (f : α →₀ ℂ))).1

instance {α : Type*} (K : Matrix α α ℂ) (hK : K.PosSemidef) :
    SeminormedAddCommGroup (PositiveKernelSpan K hK) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)

instance {α : Type*} (K : Matrix α α ℂ) (hK : K.PosSemidef) :
    InnerProductSpace ℂ (PositiveKernelSpan K hK) := .ofCore _

/-- The Hilbert space of the scalar kernel, obtained by completion of its
finite combinations with their actual semidefinite inner product. -/
abbrev PositiveKernelHilbert {α : Type*} (K : Matrix α α ℂ) (hK : K.PosSemidef) :=
  UniformSpace.Completion (PositiveKernelSpan K hK)

/-- The Hilbert feature corresponding to the unit point mass at `x`. -/
noncomputable def positiveKernelFeature {α : Type*} (K : Matrix α α ℂ) (hK : K.PosSemidef)
    (x : α) : PositiveKernelHilbert K hK :=
  UniformSpace.Completion.coe' (show PositiveKernelSpan K hK from Finsupp.single x 1)

/-- Mathlib's inner product is conjugate-linear in the first variable; the
feature orientation agrees exactly with `K x y`. -/
theorem inner_positiveKernelFeature {α : Type*} (K : Matrix α α ℂ) (hK : K.PosSemidef)
    (x y : α) : ⟪positiveKernelFeature K hK x, positiveKernelFeature K hK y⟫_ℂ = K x y := by
  have h := UniformSpace.Completion.inner_coe (𝕜 := ℂ)
    (show PositiveKernelSpan K hK from Finsupp.single x 1)
    (show PositiveKernelSpan K hK from Finsupp.single y 1)
  apply h.trans
  change (Finsupp.single x (1 : ℂ)).sum (fun i fi =>
    (Finsupp.single y (1 : ℂ)).sum (fun j gj => star fi * K i j * gj)) = _
  simp

/-- An inner-product representation of a jointly continuous scalar kernel
has continuous features, independently of the particular representation. -/
theorem continuous_feature_of_inner
    {α H : Type*} [TopologicalSpace α] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (φ : α → H) (K : α → α → ℂ)
    (hinner : ∀ x y, inner ℂ (φ x) (φ y) = K x y)
    (hK : Continuous (fun p : α × α => K p.1 p.2)) : Continuous φ := by
  apply continuous_iff_continuous_dist.mpr
  have hdist : (fun p : α × α => dist (φ p.1) (φ p.2)) =
      fun p => Real.sqrt ((K p.1 p.1).re - 2 * (K p.1 p.2).re + (K p.2 p.2).re) := by
    funext p
    rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg (φ p.1 - φ p.2)),
      norm_sub_sq (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      norm_sq_eq_re_inner (𝕜 := ℂ)]
    simp only [hinner, RCLike.re_to_complex]
  rw [hdist]
  exact (((Complex.continuous_re.comp (hK.comp (continuous_fst.prodMk continuous_fst))).sub
    (continuous_const.mul (Complex.continuous_re.comp hK))).add
      (Complex.continuous_re.comp (hK.comp (continuous_snd.prodMk continuous_snd)))).sqrt

/-- Joint continuity of the actual kernel implies continuity of its
constructed complete-Hilbert-space feature map. -/
theorem continuous_positiveKernelFeature {α : Type*} [TopologicalSpace α]
    (K : Matrix α α ℂ) (hK : K.PosSemidef)
    (hcontinuous : Continuous (fun p : α × α => K p.1 p.2)) :
    Continuous (positiveKernelFeature K hK) :=
  continuous_feature_of_inner (positiveKernelFeature K hK) K
    (inner_positiveKernelFeature K hK) hcontinuous

/-- The squared feature norm is the real diagonal of the given kernel. -/
theorem norm_positiveKernelFeature_sq {α : Type*}
    (K : Matrix α α ℂ) (hK : K.PosSemidef) (x : α) :
    ‖positiveKernelFeature K hK x‖ ^ 2 = (K x x).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_positiveKernelFeature]
  rfl

end GapFamily.Analytic
