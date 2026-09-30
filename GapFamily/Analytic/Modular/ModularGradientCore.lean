import GapFamily.Analytic.Modular.Geometry.ModularCoordinate
import GapFamily.Analytic.Elliptic.DirichletCore
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The actual smooth automorphic gradient core

Raw functions are smooth over the real field on the upper half-plane and
invariant under the full modular group. Values and hyperbolic derivatives
belong to the actual modular `L²` space. Quotienting by equality of value
classes produces a well-defined partially defined gradient operator.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory UpperHalfPlane
open scoped ContDiff MatrixGroups

/-- A directional derivative in the hyperbolic orthonormal frame. -/
def directional (F : ℂ → ℂ) (v : ℂ) (τ : UpperHalfPlane) : ℂ :=
  (τ.im : ℂ) * fderiv ℝ F τ v

theorem smooth_differentiableAt {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ ∞ F upperHalfPlaneSet) (τ : UpperHalfPlane) :
    DifferentiableAt ℝ F (τ : ℂ) :=
  (hF.differentiableOn (by simp) _ τ.im_pos).differentiableAt
    (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

theorem directional_add {F G : ℂ → ℂ}
    (hF : ContDiffOn ℝ ∞ F upperHalfPlaneSet)
    (hG : ContDiffOn ℝ ∞ G upperHalfPlaneSet) (v : ℂ) :
    directional (F + G) v = directional F v + directional G v := by
  funext τ
  simp only [directional, fderiv_add (smooth_differentiableAt hF τ)
    (smooth_differentiableAt hG τ), add_apply, mul_add, Pi.add_apply]

theorem directional_smul {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ ∞ F upperHalfPlaneSet) (c v : ℂ) :
    directional (c • F) v = c • directional F v := by
  funext τ
  simp [directional, fderiv_const_smul (smooth_differentiableAt hF τ), mul_left_comm]

@[simp] theorem directional_const (c v : ℂ) : directional (fun _ => c) v = 0 := by
  funext τ
  simp [directional]

/-- Smooth invariant functions with finite actual value and frame-gradient norms. -/
def smoothCore : Submodule ℂ (ℂ → ℂ) where
  carrier := {F | ContDiffOn ℝ ∞ F upperHalfPlaneSet ∧
    (∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane), F (↑(γ • τ : UpperHalfPlane) : ℂ) = F τ) ∧
    MemLp (fun τ : UpperHalfPlane => F τ) 2 modularMeasure ∧
    MemLp (directional F 1) 2 modularMeasure ∧
    MemLp (directional F Complex.I) 2 modularMeasure}
  zero_mem' := by
    refine ⟨contDiffOn_const, ?_, memLp_const (0 : ℂ), ?_, ?_⟩
    · intro γ τ; rfl
    · change MemLp (directional (fun _ => 0) 1) 2 modularMeasure
      rw [directional_const]
      exact MemLp.zero
    · change MemLp (directional (fun _ => 0) Complex.I) 2 modularMeasure
      rw [directional_const]
      exact MemLp.zero
  add_mem' := by
    intro F G hF hG
    refine ⟨hF.1.add hG.1, ?_, hF.2.2.1.add hG.2.2.1, ?_, ?_⟩
    · intro γ τ
      simp only [Pi.add_apply, hF.2.1 γ τ, hG.2.1 γ τ]
    · rw [directional_add hF.1 hG.1]
      exact hF.2.2.2.1.add hG.2.2.2.1
    · rw [directional_add hF.1 hG.1]
      exact hF.2.2.2.2.add hG.2.2.2.2
  smul_mem' := by
    intro c F hF
    refine ⟨hF.1.const_smul c, ?_, hF.2.2.1.const_smul c, ?_, ?_⟩
    · intro γ τ
      simp only [Pi.smul_apply, hF.2.1 γ τ]
    · rw [directional_smul hF.1]
      exact hF.2.2.2.1.const_smul c
    · rw [directional_smul hF.1]
      exact hF.2.2.2.2.const_smul c

/-- The actual ambient `L²` class of a smooth automorphic core function. -/
def value : smoothCore →ₗ[ℂ] ModularHilbert where
  toFun F := F.property.2.2.1.toLp (fun τ : UpperHalfPlane => F.val τ)
  map_add' _ _ := MemLp.toLp_add _ _
  map_smul' c _ := MemLp.toLp_const_smul c _

theorem value_ae (F : smoothCore) :
    value F =ᵐ[modularMeasure] fun τ : UpperHalfPlane => F.val τ :=
  MemLp.coeFn_toLp F.property.2.2.1

/-- The two derivative directions are packaged in the Hilbert sum norm. -/
abbrev GradientSpace := WithLp 2 (ModularHilbert × ModularHilbert)

/-- A core gradient component with its actual integrability certificate. -/
def component (v : ℂ) (hmem : ∀ F : smoothCore, MemLp (directional F.val v) 2 modularMeasure) :
    smoothCore →ₗ[ℂ] ModularHilbert where
  toFun F := (hmem F).toLp (directional F.val v)
  map_add' F G := by
    rw [← MemLp.toLp_add (hmem F) (hmem G)]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall
      (congrFun (directional_add F.property.1 G.property.1 v))
  map_smul' c F := by
    simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul c (hmem F)]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (congrFun (directional_smul F.property.1 c v))

theorem component_ae (v : ℂ)
    (hmem : ∀ F : smoothCore, MemLp (directional F.val v) 2 modularMeasure) (F : smoothCore) :
    component v hmem F =ᵐ[modularMeasure] directional F.val v :=
  MemLp.coeFn_toLp (hmem F)

def xComponent : smoothCore →ₗ[ℂ] ModularHilbert := component 1 (fun F => F.property.2.2.2.1)

def yComponent : smoothCore →ₗ[ℂ] ModularHilbert :=
  component Complex.I (fun F => F.property.2.2.2.2)

/-- The actual gradient of a raw core function in the Hilbert sum norm. -/
def coreGradient : smoothCore →ₗ[ℂ] GradientSpace :=
  (WithLp.linearEquiv 2 ℂ (ModularHilbert × ModularHilbert)).symm.toLinearMap.comp
    (xComponent.prod yComponent)

@[simp] theorem coreGradient_fst (F : smoothCore) :
    (WithLp.ofLp (coreGradient F)).1 = xComponent F := rfl

@[simp] theorem coreGradient_snd (F : smoothCore) :
    (WithLp.ofLp (coreGradient F)).2 = yComponent F := rfl

theorem core_continuousOn_interior (F : smoothCore) : ContinuousOn F.val modularInterior :=
  F.property.1.continuousOn.mono (fun _ hz => im_pos_of_mem_modularInterior hz)

/-- Equality of the value classes forces equality of every actual derivative class. -/
theorem component_eq_of_value_eq (v : ℂ)
    (hmem : ∀ F : smoothCore, MemLp (directional F.val v) 2 modularMeasure)
    {F G : smoothCore} (hFG : value F = value G) :
    component v hmem F = component v hmem G := by
  have hF := value_ae F
  rw [hFG] at hF
  have heq := hF.symm.trans (value_ae G)
  have hdir := modularDirectional_ae_eq (core_continuousOn_interior F)
    (core_continuousOn_interior G) heq v
  apply Lp.ext
  exact (component_ae v hmem F).trans (hdir.trans (component_ae v hmem G).symm)

theorem coreGradient_eq_of_value_eq {F G : smoothCore} (hFG : value F = value G) :
    coreGradient F = coreGradient G := by
  apply (WithLp.linearEquiv 2 ℂ (ModularHilbert × ModularHilbert)).injective
  change (xComponent F, yComponent F) = (xComponent G, yComponent G)
  exact Prod.ext (component_eq_of_value_eq _ _ hFG) (component_eq_of_value_eq _ _ hFG)

theorem value_ker_le_coreGradient_ker : value.ker ≤ coreGradient.ker := by
  intro F hF
  have h := coreGradient_eq_of_value_eq (F := F) (G := 0) (by simpa using hF)
  simpa using h

/-- The actual first-order modular gradient, defined on value classes of the
smooth invariant finite-energy core. No density or closability is assumed. -/
def gradient : ModularHilbert →ₗ.[ℂ] GradientSpace where
  domain := value.range
  toFun := (value.ker.liftQ coreGradient value_ker_le_coreGradient_ker).comp
    value.quotKerEquivRange.symm.toLinearMap

@[simp] theorem gradient_domain : gradient.domain = value.range := rfl

/-- On a genuine core function the quotient-defined operator has its literal derivatives. -/
theorem gradient_apply_value (F : smoothCore) :
    gradient ⟨value F, LinearMap.mem_range_self value F⟩ = coreGradient F := by
  change value.ker.liftQ coreGradient value_ker_le_coreGradient_ker
    (value.quotKerEquivRange.symm ⟨value F, LinearMap.mem_range_self value F⟩) = _
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

/-- Constants are genuine smooth automorphic finite-energy core functions. -/
def constantCore (c : ℂ) : smoothCore :=
  ⟨fun _ => c, contDiffOn_const, (fun _ _ => rfl), memLp_const c,
    by rw [directional_const]; exact MemLp.zero,
    by rw [directional_const]; exact MemLp.zero⟩

theorem value_constantCore_one : value (constantCore 1) = modularConstant := rfl

theorem coreGradient_constantCore (c : ℂ) : coreGradient (constantCore c) = 0 := by
  apply (WithLp.linearEquiv 2 ℂ (ModularHilbert × ModularHilbert)).injective
  change (xComponent (constantCore c), yComponent (constantCore c)) = (0, 0)
  apply Prod.ext
  · apply Lp.ext
    exact (component_ae 1 _ (constantCore c)).trans (by
      simpa only [constantCore, directional_const] using
        (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := modularMeasure)).symm)
  · apply Lp.ext
    exact (component_ae Complex.I _ (constantCore c)).trans (by
      simpa only [constantCore, directional_const] using
        (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := modularMeasure)).symm)

theorem modularConstant_mem_gradient_domain : modularConstant ∈ gradient.domain :=
  ⟨constantCore 1, value_constantCore_one⟩

theorem gradient_modularConstant :
    gradient ⟨modularConstant, modularConstant_mem_gradient_domain⟩ = 0 := by
  simpa only [value_constantCore_one] using
    (gradient_apply_value (constantCore 1)).trans (coreGradient_constantCore 1)

end GapFamily.Analytic.ModularGradient
