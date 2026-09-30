import GapFamily.Analytic.Modular.Elliptic.ModularUpperWeakPoisson
import GapFamily.Analytic.Modular.Elliptic.ModularEllipticScalar

/-!
# Real projections of the actual upper-half-plane weak fields

The local value, gradient, and divided operator source are the constructed
upper-cutoff fields. On an open plateau they satisfy the ordinary scalar weak
derivative and Poisson identities, including across fundamental-domain seams.
No Sobolev regularity or weak-equation witness is assumed.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

def upperEllipticValue (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (u : laplacian.domain) : ℂ → ℂ :=
  upperCutoffValueOperator χ hχ hc hs (formLift ⟨u, laplacian_domain_le u.property⟩)

def upperEllipticGradient (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (u : laplacian.domain) (v : ℂ) : ℂ → ℂ :=
  upperCutoffGradientOperator χ hχ hc hs v (formLift ⟨u, laplacian_domain_le u.property⟩)

def upperEllipticSource (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (u : laplacian.domain) : ℂ → ℂ :=
  upperCutoffSourceField χ hχ hc hs (laplacian u)

theorem upperEllipticValue_memLp (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (u : laplacian.domain) : MemLp (upperEllipticValue χ hχ hc hs u) 2 volume :=
  Lp.memLp _

theorem upperEllipticGradient_memLp (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (u : laplacian.domain) (v : ℂ) :
    MemLp (upperEllipticGradient χ hχ hc hs u v) 2 volume := Lp.memLp _

theorem upperEllipticSource_memLp_on_compact (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (u : laplacian.domain) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ upperHalfPlaneSet) :
    MemLp (upperEllipticSource χ hχ hc hs u) 2 (volume.restrict K) :=
  upperCutoffSourceField_memLp_on_compact χ hχ hc hs (laplacian u) hK hKU

theorem upperCutoff_plateau_subset_upperHalfPlane {χ : ℂ → ℂ} {U : Set ℂ}
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (hχU : EqOn χ (fun _ => 1) U) :
    U ⊆ upperHalfPlaneSet := by
  intro z hz
  apply hs
  apply subset_tsupport χ
  rw [Function.mem_support, hχU hz]
  exact one_ne_zero

/-- Any real continuous linear projection preserves the actual weak derivative
identity on the plateau, with ordinary convergent test integrals. -/
theorem upperEllipticScalar_weak (L : ℂ →L[ℝ] ℝ)
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (u : laplacian.domain) (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (v : ℂ) :
    (∫ z : ℂ, L (upperEllipticValue χ hχ hc hs u z) * fderiv ℝ φ z v) =
      -(∫ z : ℂ, L (upperEllipticGradient χ hχ hc hs u v z) * φ z) := by
  have hφC : ContDiff ℝ ∞ (fun z => (φ z : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  have hcC : HasCompactSupport (fun z => (φ z : ℂ)) := hcφ.comp_left Complex.ofReal_zero
  have hsC : tsupport (fun z => (φ z : ℂ)) ⊆ U :=
    (tsupport_comp_subset Complex.ofReal_zero φ).trans hφU
  have h := upperCutoff_weakDerivative_local χ hχ hc hs v
    (formLift ⟨u, laplacian_domain_le u.property⟩) _ hφC hcC U hU hχU hsC
  have hi₁ := euclideanCompactTest_integrable _ hφC.continuous hcC
    (upperCutoffGradientOperator χ hχ hc hs v (formLift ⟨u, laplacian_domain_le u.property⟩))
  have hi₂ := euclideanCompactTest_integrable _
    (contDiff_upperCutoffDerivative hφC v).continuous (hcC.fderiv_apply ℝ v)
    (upperCutoffValueOperator χ hχ hc hs (formLift ⟨u, laplacian_domain_le u.property⟩))
  have hL := congrArg L h
  rw [map_neg, ← L.integral_comp_comm hi₁, ← L.integral_comp_comm hi₂] at hL
  simp only [fderiv_realTest φ hφ, Complex.star_def, Complex.conj_ofReal,
    ellipticScalar_real_mul] at hL
  change (∫ z : ℂ, L (upperEllipticGradient χ hχ hc hs u v z) * φ z) =
    -(∫ z : ℂ, L (upperEllipticValue χ hχ hc hs u z) * fderiv ℝ φ z v) at hL
  linarith

/-- The actual divided operator source drives the projected upper-half-plane
Poisson equation; the compact test may cross modular seams. -/
theorem upperEllipticScalar_poisson (L : ℂ →L[ℝ] ℝ)
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (u : laplacian.domain) (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (∫ z : ℂ,
      L (upperEllipticGradient χ hχ hc hs u 1 z) * fderiv ℝ φ z 1 +
      L (upperEllipticGradient χ hχ hc hs u Complex.I z) * fderiv ℝ φ z Complex.I) =
      ∫ z : ℂ, L (upperEllipticSource χ hχ hc hs u z) * φ z := by
  have hφC : ContDiff ℝ ∞ (fun z => (φ z : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  have hcC : HasCompactSupport (fun z => (φ z : ℂ)) := hcφ.comp_left Complex.ofReal_zero
  have hsC : tsupport (fun z => (φ z : ℂ)) ⊆ U :=
    (tsupport_comp_subset Complex.ofReal_zero φ).trans hφU
  have hsH := hsC.trans (upperCutoff_plateau_subset_upperHalfPlane hs hχU)
  have h := congrArg L (laplacian_upper_weakPoisson_local χ hχ hc hs U hU hχU u
    _ hφC hcC hsC).2
  have hi := laplacian_upper_weakPoisson_integrable χ hχ hc hs _ hφC hcC hsH u
  rw [← L.integral_comp_comm hi.1, ← L.integral_comp_comm hi.2] at h
  simpa only [fderiv_realTest φ hφ, Complex.star_def, Complex.conj_ofReal, map_add,
    ellipticScalar_real_mul, upperEllipticGradient, upperEllipticSource] using h

end GapFamily.Analytic.ModularGradient
