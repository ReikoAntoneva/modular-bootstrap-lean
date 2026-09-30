import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroKernel
import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroResolventBound
import GapFamily.Analytic.Foundation.CompactPositiveContraction
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Actual coercivity after removing the ordinary cusp-average channel

The genuine compact positive constrained response has no nonzero fixed vector.
It is consequently a strict contraction. The response is the embedding times
its adjoint, so this gives positive coercivity for the actual closed-gradient
energy on the complete constrained form domain. No full modular spectral gap
or density in an independently specified ambient constrained space is assumed.
-/

noncomputable section

namespace GapFamily.Analytic

open ModularGradient

/-- The actual compact constrained response is strictly contractive. -/
theorem cuspMeanZeroWeakResolvent_norm_lt_one : ‖cuspMeanZeroWeakResolvent‖ < 1 :=
  norm_lt_one_of_isCompact_isPositive_no_fixed cuspMeanZeroWeakResolvent
    cuspMeanZeroWeakResolvent_isCompact cuspMeanZeroWeakResolvent_isPositive
    cuspMeanZeroWeakResolvent_norm_le_one
    (fun f hf => (cuspMeanZeroWeakResolvent_eq_self_iff f).mp hf)

/-- The actual weak equation controls the complete solution norm by the response norm. -/
theorem cuspMeanZeroWeakSolution_norm_sq_le (f : ModularHilbert) :
    ‖cuspMeanZeroWeakSolution f‖ ^ 2 ≤ ‖cuspMeanZeroWeakResolvent‖ * ‖f‖ ^ 2 := by
  have heq := cuspMeanZeroWeakSolution_equation f (cuspMeanZeroWeakSolution f)
  rw [← cuspMeanZeroWeakResolvent_apply] at heq
  have hre := congrArg Complex.re heq
  rw [Complex.add_re] at hre
  change RCLike.re (inner ℂ (cuspMeanZeroGradient (cuspMeanZeroWeakSolution f))
    (cuspMeanZeroGradient (cuspMeanZeroWeakSolution f))) +
    RCLike.re (inner ℂ (cuspMeanZeroWeakResolvent f) (cuspMeanZeroWeakResolvent f)) =
    RCLike.re (inner ℂ f (cuspMeanZeroWeakResolvent f)) at hre
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at hre
  have hn := cuspMeanZeroForm_norm_sq (cuspMeanZeroWeakSolution f)
  rw [← cuspMeanZeroWeakResolvent_apply] at hn
  have hc := re_inner_le_norm (𝕜 := ℂ) f (cuspMeanZeroWeakResolvent f)
  have hop := mul_le_mul_of_nonneg_left (cuspMeanZeroWeakResolvent.le_opNorm f)
    (norm_nonneg f)
  nlinarith

/-- The actual adjoint pairing bounds the mass of every constrained form vector. -/
theorem meanZeroCuspEmbedding_norm_sq_le_response (u : cuspMeanZeroForm) :
    ‖meanZeroCuspEmbedding u‖ ^ 2 ≤ ‖cuspMeanZeroWeakResolvent‖ * ‖u‖ ^ 2 := by
  have hpair : inner ℂ (cuspMeanZeroWeakSolution (meanZeroCuspEmbedding u)) u =
      inner ℂ (meanZeroCuspEmbedding u) (meanZeroCuspEmbedding u) := by
    have h := cuspMeanZeroWeakSolution_equation (meanZeroCuspEmbedding u) u
    rw [← cuspMeanZeroForm_energy] at h
    unfold Dirichlet.formEnergy at h
    rw [← cuspMeanZeroWeakResolvent_apply, sub_add_cancel] at h
    exact h
  have hp := congrArg Complex.re hpair
  change RCLike.re (inner ℂ (cuspMeanZeroWeakSolution (meanZeroCuspEmbedding u)) u) =
    RCLike.re (inner ℂ (meanZeroCuspEmbedding u) (meanZeroCuspEmbedding u)) at hp
  rw [inner_self_eq_norm_sq] at hp
  have hc := re_inner_le_norm (𝕜 := ℂ)
    (cuspMeanZeroWeakSolution (meanZeroCuspEmbedding u)) u
  rw [hp] at hc
  have hc2 := pow_le_pow_left₀ (sq_nonneg _) hc 2
  rw [mul_pow] at hc2
  have hsol := mul_le_mul_of_nonneg_right
    (cuspMeanZeroWeakSolution_norm_sq_le (meanZeroCuspEmbedding u)) (sq_nonneg ‖u‖)
  by_cases hm : ‖meanZeroCuspEmbedding u‖ = 0
  · simp only [hm, zero_pow (by norm_num : 2 ≠ 0)]
    positivity
  · have hm2 : 0 < ‖meanZeroCuspEmbedding u‖ ^ 2 := sq_pos_of_ne_zero hm
    apply (mul_le_mul_iff_left₀ hm2).mp
    nlinarith only [hc2, hsol]

/-- A concrete positive coercivity constant for the actual constrained energy. -/
def cuspMeanZeroCoercivity : ℝ := 1 - ‖cuspMeanZeroWeakResolvent‖

theorem cuspMeanZeroCoercivity_pos : 0 < cuspMeanZeroCoercivity :=
  sub_pos.mpr cuspMeanZeroWeakResolvent_norm_lt_one

/-- The genuine closed-gradient energy controls the full constrained form norm. -/
theorem cuspMeanZero_energy_coercive (u : cuspMeanZeroForm) :
    cuspMeanZeroCoercivity * ‖u‖ ^ 2 ≤ ‖cuspMeanZeroGradient u‖ ^ 2 := by
  have hmass := meanZeroCuspEmbedding_norm_sq_le_response u
  have he := cuspMeanZeroForm_norm_sq u
  change (1 - ‖cuspMeanZeroWeakResolvent‖) * ‖u‖ ^ 2 ≤ ‖cuspMeanZeroGradient u‖ ^ 2
  nlinarith

/-- Actual invertibility of identity minus the constrained weak response. -/
theorem cuspMeanZero_one_sub_resolvent_isUnit :
    IsUnit (1 - cuspMeanZeroWeakResolvent) :=
  isUnit_one_sub_of_norm_lt_one cuspMeanZeroWeakResolvent_norm_lt_one

/-- The actual continuous linear equivalence associated with identity minus
its strictly contractive constrained response. -/
def cuspMeanZeroOneSubEquiv : ModularHilbert ≃L[ℂ] ModularHilbert :=
  ContinuousLinearEquiv.unitsEquiv ℂ ModularHilbert
    cuspMeanZero_one_sub_resolvent_isUnit.unit

@[simp] theorem cuspMeanZeroOneSubEquiv_apply (f : ModularHilbert) :
    cuspMeanZeroOneSubEquiv f = f - cuspMeanZeroWeakResolvent f := by
  change (cuspMeanZero_one_sub_resolvent_isUnit.unit :
    ModularHilbert →L[ℂ] ModularHilbert) f = _
  rw [cuspMeanZero_one_sub_resolvent_isUnit.unit_spec]
  rfl

/-- A bounded actual weak solution of the pure constrained gradient equation. -/
def cuspMeanZeroEnergySolution : ModularHilbert →L[ℂ] cuspMeanZeroForm :=
  cuspMeanZeroWeakSolution.comp cuspMeanZeroOneSubEquiv.symm.toContinuousLinearMap

/-- Every constrained test vector satisfies the actual pure-energy equation. -/
theorem cuspMeanZeroEnergySolution_equation (f : ModularHilbert) (v : cuspMeanZeroForm) :
    inner ℂ (cuspMeanZeroGradient (cuspMeanZeroEnergySolution f))
        (cuspMeanZeroGradient v) = inner ℂ f (meanZeroCuspEmbedding v) := by
  let g := cuspMeanZeroOneSubEquiv.symm f
  have hsub : g - cuspMeanZeroWeakResolvent g = f := by
    rw [← cuspMeanZeroOneSubEquiv_apply]
    exact cuspMeanZeroOneSubEquiv.apply_symm_apply f
  have hweak := cuspMeanZeroWeakSolution_equation g v
  change inner ℂ (cuspMeanZeroGradient (cuspMeanZeroWeakSolution g))
      (cuspMeanZeroGradient v) = _
  rw [← hsub, inner_sub_left]
  exact eq_sub_iff_add_eq.mpr hweak

/-- The actual constrained energy solution is unique in the completed form domain. -/
theorem cuspMeanZeroEnergySolution_unique (f : ModularHilbert) (u : cuspMeanZeroForm)
    (hu : ∀ v : cuspMeanZeroForm,
      inner ℂ (cuspMeanZeroGradient u) (cuspMeanZeroGradient v) =
        inner ℂ f (meanZeroCuspEmbedding v)) :
    u = cuspMeanZeroEnergySolution f := by
  have hzero (v : cuspMeanZeroForm) :
      inner ℂ (cuspMeanZeroGradient (u - cuspMeanZeroEnergySolution f))
        (cuspMeanZeroGradient v) = 0 := by
    rw [map_sub, inner_sub_left, hu v, cuspMeanZeroEnergySolution_equation, sub_self]
  have hg := inner_self_eq_zero.mp (hzero (u - cuspMeanZeroEnergySolution f))
  exact sub_eq_zero.mp ((cuspMeanZeroGradient_eq_zero_iff _).mp hg)

end GapFamily.Analytic
