import GapFamily.Analytic.Cusp.CuspPoincareComplement
import GapFamily.Analytic.Cusp.CuspHeightFundamentalDomain
import GapFamily.Analytic.Cusp.CuspPoincareResidualSplit
import GapFamily.Analytic.Cusp.Profile.CuspWeightedTailAnalytic
import GapFamily.Analytic.Cusp.CuspPoincareDirectRemnant

noncomputable section
namespace GapFamily.Analytic.PoincareComplement

open Set MeasureTheory

/-- Every nonidentity cusp term on the closed fundamental domain has height
where the actual cutoff vanishes. No convergence parameter restriction is needed. -/
theorem term_eq_raw_of_mem_fd (J : ℤ) (s : ℂ) (q : CuspCoset)
    (hq : q ≠ identityCuspCoset) {τ : UpperHalfPlane} (hτ : τ ∈ ModularGroup.fd) :
    term J s τ q = complexPoincareTerm 0 J s τ q := by
  have hr : (1 : ℝ) ≤ ‖cuspBottomRow q‖ :=
    one_le_norm_int_pair _ (cuspBottomRow_ne_zero q)
  have hy : (q.out • τ).im ≤ 2 := by
    apply (nonidentity_cusp_height_le q hq hτ).trans
    apply (div_le_iff₀ (zero_lt_one.trans_le hr)).mpr
    linarith
  rw [term_out, pointSeed, complexPoincareTerm_out,
    CuspFourierCutoff.cutoff_eq_zero hy]
  simp

/-- The literal complement series splits into its identity contribution and
its genuinely convergent nonidentity part. -/
theorem series_direct_term (J : ℤ) {s : ℂ} (hs : 1 < s.re) (τ : UpperHalfPlane) :
    series J s τ = pointSeed J s τ +
      ∑' q : {q : CuspCoset // q ≠ identityCuspCoset}, term J s τ q := by
  classical
  have h := (summable_norm_term J hs τ).of_norm.sum_add_tsum_compl
    (s := {identityCuspCoset})
  simp only [Finset.sum_singleton, term_identity] at h
  let e : {q : CuspCoset // q ≠ identityCuspCoset} ≃
      ↑((↑({identityCuspCoset} : Finset CuspCoset) : Set CuspCoset)ᶜ) :=
    Equiv.subtypeEquivRight (fun _ => by simp)
  calc
    _ = pointSeed J s τ + ∑' q :
        ↑((↑({identityCuspCoset} : Finset CuspCoset) : Set CuspCoset)ᶜ),
          term J s τ q := h.symm
    _ = _ := congrArg (pointSeed J s τ + ·)
      (e.tsum_eq (fun q => term J s τ q)).symm

/-- On the full closed fundamental domain the complement series is exactly
the actual Poincare series with its cutoff direct seed subtracted. -/
theorem series_eq_residual_of_mem_fd (J : ℤ) {s : ℂ} (hs : 1 < s.re)
    {τ : UpperHalfPlane} (hτ : τ ∈ ModularGroup.fd) :
    series J s τ = complexPoincareSeries 0 J s τ -
      (CuspFourierCutoff.cutoff τ.im : ℂ) * complexPointSeed 0 J s τ := by
  rw [series_direct_term J hs τ,
    complexPoincareSeries_residual_split 0 J hs τ (CuspFourierCutoff.cutoff τ.im : ℂ)]
  have ht : (∑' q : {q : CuspCoset // q ≠ identityCuspCoset}, term J s τ q) =
      ∑' q : {q : CuspCoset // q ≠ identityCuspCoset}, complexPoincareTerm 0 J s τ q := by
    apply tsum_congr
    intro q
    exact term_eq_raw_of_mem_fd J s q q.property hτ
  rw [ht, pointSeed]
  push_cast
  ring

/-- The already constructed actual Hilbert tail and direct remnant represent
the true complement series almost everywhere, on the proved L² convergence region. -/
theorem hilbert_sum_ae_series (J : ℤ) {s : ℂ} (hs : 2 < s.re) :
    (cuspWeightedTailAnalytic J 0 (by norm_num) s + cuspPoincareDirectRemnant J 0 s)
      =ᵐ[modularMeasure] series J s := by
  let A := cuspWeightedTailAnalytic J 0 (by norm_num) s
  let B := cuspPoincareDirectRemnant J 0 s
  have hfd : ∀ᵐ τ ∂modularMeasure, τ ∈ ModularGroup.fd := ae_restrict_mem measurableSet_fd
  filter_upwards [Lp.coeFn_add A B,
    cuspWeightedTailAnalytic_ae J 0 (by norm_num) (by simpa using hs),
    cuspPoincareDirectRemnant_ae J 0 (by linarith), hfd] with τ hab ha hb hτ
  change (A + B) τ = series J s τ
  change A τ = _ at ha
  change B τ = _ at hb
  change (A + B) τ = A τ + B τ at hab
  rw [hab, ha, hb, series_eq_residual_of_mem_fd J (by linarith) hτ,
    complexPoincareSeries_residual_split 0 J (by linarith) τ
      (CuspFourierCutoff.cutoff τ.im : ℂ)]
  simp only [cuspWeightedTailTerm, cuspPoincareDirectRemnantTerm, Real.rpow_zero,
    Complex.ofReal_one, one_mul, Complex.ofReal_sub]

/-- Ordinary L² membership of the actual complement sum follows from the
proved representative equality, rather than from a totalized integral. -/
theorem series_memLp (J : ℤ) {s : ℂ} (hs : 2 < s.re) :
    MemLp (series J s) 2 modularMeasure :=
  (memLp_congr_ae (hilbert_sum_ae_series J hs)).mp (Lp.memLp _)


end GapFamily.Analytic.PoincareComplement
