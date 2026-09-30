import GapFamily.Analytic.Cusp.Fourier.CuspFourierCutoffProfile
import GapFamily.Analytic.Cusp.Fourier.CuspFourierCutoffCommutator
import GapFamily.Analytic.Cusp.Fourier.CuspFourierBounded
import GapFamily.Analytic.Cusp.Fourier.CuspFourierCutoffAnalytic
import GapFamily.Analytic.Cusp.Fourier.CuspFourierCutoffResponse

/-!
The actual compact collar component of the zero-energy Fourier cutoff source.
The profile has the algebraic plus sign in the equation for the Poincaré series
minus its cutoff direct term. The remaining shifted Poincaré forcing, including
the nonidentity tail and the low-height direct remnant, is not included.
-/

noncomputable section
namespace GapFamily.Analytic.CuspFourierCutoff
open Set MeasureTheory ModularGradient Dirichlet
open scoped ContDiff BoundedContinuousFunction

theorem exponent_eigenvalue (κ : ℂ) :
    exponent κ * (1 - exponent κ) = CuspSchurLocal.parameter κ := by
  unfold exponent CuspSchurLocal.parameter
  ring

theorem radial_commutator_parameter (κ : ℂ) {y : ℝ} (hy : 0 < y) :
    -(y : ℂ) ^ 2 * deriv (deriv (radial κ)) y -
      CuspSchurLocal.parameter κ * radial κ y = -profile κ y := by
  rw [← exponent_eigenvalue κ]
  exact radial_commutator κ hy

/-- The compact collar forcing, formed by the original normalized full-SL₂ periodization. -/
def forcingCore (J : ℤ) (κ : ℂ) : smoothCore :=
  cuspFourierProfileCore J (profile κ) (contDiff_profile κ)
    (hasCompactSupport_profile κ) (tsupport_profile_subset_Ioi κ)

def forcing (J : ℤ) (κ : ℂ) : ModularHilbert := value (forcingCore J κ)

theorem forcingCore_seed_hasCompactSupport (J : ℤ) (κ : ℂ) :
    HasCompactSupport (cuspFourierProfileSeed J (profile κ)) :=
  cuspFourierProfileSeed_hasCompactSupport J (hasCompactSupport_profile κ)

theorem forcingCore_eq_on_fd (J : ℤ) (κ : ℂ) {τ : UpperHalfPlane}
    (hτ : τ ∈ ModularGroup.fd) :
    (forcingCore J κ).val τ = profile κ τ.im * cuspFourierMode J τ.re :=
  cuspFourierProfileCore_eq_on_fd _ _ _ _ _ hτ

theorem forcing_ae (J : ℤ) (κ : ℂ) :
    forcing J κ =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => profile κ τ.im * cuspFourierMode J τ.re) :=
  cuspFourierProfileCore_value_ae _ _ _ _ _

theorem forcingCore_mem_cuspMeanZeroForm (J : ℤ) (hJ : J ≠ 0) (κ : ℂ) :
    coreForm (forcingCore J κ) ∈ cuspMeanZeroForm :=
  cuspFourierProfileCore_mem_cuspMeanZeroForm J hJ _ _ _ _

theorem forcing_highCut_eq_zero (J : ℤ) (κ : ℂ) :
    modularHighCut 3 (forcing J κ) = 0 := by
  apply Lp.ext
  filter_upwards [modularHighCut_ae 3 (forcing J κ), forcing_ae J κ,
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := modularMeasure)] with τ hcut hf hzero
  rw [hcut, hzero]
  by_cases ht : 3 < τ.im
  · rw [indicator_of_mem (show τ ∈ {τ : UpperHalfPlane | 3 < τ.im} from ht), hf]
    have hz : profile κ τ.im = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => ht.not_ge (tsupport_profile κ h).2)
    simp only [hz, zero_mul, Pi.zero_apply]
  · exact indicator_of_notMem (show τ ∉ {τ : UpperHalfPlane | 3 < τ.im} from ht) _

theorem forcing_lowCut_eq_self (J : ℤ) (κ : ℂ) :
    modularLowCut 3 (forcing J κ) = forcing J κ := by
  rw [modularLowCut_apply, forcing_highCut_eq_zero, sub_zero]

def boundedConstantProfile (J : ℤ) : UpperHalfPlane →ᵇ ℂ :=
  boundedFourierProfile J (profile 0) (contDiff_profile 0).continuous
    (hasCompactSupport_profile 0)

def boundedLinearProfile (J : ℤ) : UpperHalfPlane →ᵇ ℂ :=
  boundedFourierProfile J linearProfile contDiff_linearProfile.continuous
    hasCompactSupport_linearProfile

theorem boundedForcing_profile (J : ℤ) (κ : ℂ) (τ : UpperHalfPlane) :
    boundedForcing (boundedConstantProfile J) (boundedLinearProfile J) boundedLogHeight κ τ =
      profile κ τ.im * cuspFourierMode J τ.re := by
  rw [boundedForcing_apply]
  change Complex.exp (κ * boundedLogHeight τ) *
    (profile 0 τ.im * cuspFourierMode J τ.re +
      κ * (linearProfile τ.im * cuspFourierMode J τ.re)) = _
  by_cases ht : τ.im ∈ Icc (2 : ℝ) 3
  · rw [boundedLogHeight_apply_of_mem τ ht, profile_factorization τ.im_pos κ]
    ring
  · have h0 : profile 0 τ.im = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => ht (tsupport_profile 0 h))
    have h1 : linearProfile τ.im = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => ht (tsupport_linearProfile h))
    have hk : profile κ τ.im = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => ht (tsupport_profile κ h))
    simp [h0, h1, hk]

theorem forcing_eq_hilbertForcing (J : ℤ) (κ : ℂ) :
    forcing J κ = hilbertForcing (boundedConstantProfile J)
      (boundedLinearProfile J) boundedLogHeight κ := by
  apply Lp.ext
  apply (forcing_ae J κ).trans
  apply Filter.EventuallyEq.symm
  apply (BoundedContinuousFunction.coeFn_toLp 2 modularMeasure ℂ
    (boundedForcing (boundedConstantProfile J) (boundedLinearProfile J) boundedLogHeight κ)).trans
  exact Filter.Eventually.of_forall (boundedForcing_profile J κ)

/-- Entire dependence in the actual modular L² norm, not only pointwise analyticity. -/
theorem forcing_analyticAt (J : ℤ) (κ : ℂ) : AnalyticAt ℂ (forcing J) κ := by
  have hfun : forcing J = hilbertForcing (boundedConstantProfile J)
      (boundedLinearProfile J) boundedLogHeight := funext (forcing_eq_hilbertForcing J)
  rw [hfun]
  exact hilbertForcing_analyticAt _ _ _ _

/-- The actual compact Fourier forcing has a continuous local response analytic through
the threshold. On a common physical half-disk it is the full modular Schur inverse. -/
theorem exists_analytic_forcingLocalResponse (J : ℤ)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ modularInterior)
    (hreg : K ⊆ closure (interior K)) :
    ∃ (U : ℂ → C(K, ℂ)) (ε : ℝ), 0 < ε ∧ AnalyticAt ℂ U 0 ∧
      ∀ κ : ℂ, ‖κ‖ < ε → 0 < κ.re →
        ∃ hu : CuspSchur.actualSchurResolvent (CuspSchurLocal.parameter κ) (forcing J κ) ∈
            laplacian.domain,
          U κ = laplacianLocalRestriction K hKU hreg (gradientLift laplacian
            ⟨CuspSchur.actualSchurResolvent (CuspSchurLocal.parameter κ) (forcing J κ), hu⟩) :=
  exists_analytic_heightSupportedResponse (forcing J) (forcing_analyticAt J 0)
    (forcing_lowCut_eq_self J) K hKU hreg

end GapFamily.Analytic.CuspFourierCutoff
