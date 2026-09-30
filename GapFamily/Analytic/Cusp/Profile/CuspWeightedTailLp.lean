import GapFamily.Analytic.Cusp.CuspHeightFundamentalDomain
import GapFamily.Analytic.Modular.ModularHilbert
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

noncomputable section
namespace GapFamily.Analytic

open MeasureTheory Set
open scoped ENNReal

/-- The literal height-weighted zero-energy Poincare summand. -/
def cuspWeightedTailTerm (J : ℤ) (s : ℂ) (α : ℝ) (q : CuspCoset)
    (τ : UpperHalfPlane) : ℂ :=
  (τ.im ^ α : ℝ) * complexPoincareTerm 0 J s τ q

private theorem continuous_complexPointSeed_spatial (E : ℂ) (J : ℤ) (s : ℂ) :
    Continuous (complexPointSeed E J s) := by
  have hp : Continuous (fun τ : UpperHalfPlane => (τ.im : ℂ) ^ s) := by
    apply continuous_iff_continuousAt.mpr
    intro τ
    exact (Complex.continuousAt_ofReal_cpow_const τ.im s (Or.inr τ.im_pos.ne')).comp
      UpperHalfPlane.continuous_im.continuousAt
  exact hp.mul (by fun_prop)

/-- The actual summand is measurable because it is continuous on the upper half-plane. -/
theorem cuspWeightedTailTerm_continuous (J : ℤ) (s : ℂ) {α : ℝ} (hα : 0 ≤ α)
    (q : CuspCoset) : Continuous (cuspWeightedTailTerm J s α q) := by
  have hw : Continuous (fun τ : UpperHalfPlane => ((τ.im ^ α : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((Real.continuous_rpow_const hα).comp UpperHalfPlane.continuous_im)
  have ht : Continuous (fun τ : UpperHalfPlane => complexPoincareTerm 0 J s τ q) := by
    simp only [complexPoincareTerm_out]
    have hg : Continuous (fun τ : UpperHalfPlane => q.out • τ) := by
      change Continuous (fun τ : UpperHalfPlane =>
        (q.out : Matrix.GeneralLinearGroup (Fin 2) ℝ) • τ)
      exact continuous_const_smul _
    exact (continuous_complexPointSeed_spatial 0 J s).comp hg
  exact hw.mul ht

/-- The uniform row bound holds almost everywhere for the actual modular measure. -/
theorem cuspWeightedTailTerm_ae_bound (J : ℤ) (s : ℂ) {α : ℝ}
    (hα : 0 ≤ α) (hαs : α ≤ s.re) (q : CuspCoset) (hq : q ≠ identityCuspCoset) :
    ∀ᵐ τ ∂modularMeasure, ‖cuspWeightedTailTerm J s α q τ‖ ≤
      (2 : ℝ) ^ (s.re - α) * ‖cuspBottomRow q‖ ^ (-(s.re - α)) := by
  have hfd : ∀ᵐ τ ∂modularMeasure, τ ∈ ModularGroup.fd :=
    ae_restrict_mem measurableSet_fd
  filter_upwards [hfd] with τ hτ
  rw [cuspWeightedTailTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg τ.im_pos.le α)]
  exact norm_weighted_nonidentity_complexPoincareTerm_le J s q hq
    hτ hα hαs

/-- A genuine weighted L² summand on the finite modular measure. -/
theorem cuspWeightedTailTerm_memLp (J : ℤ) (s : ℂ) {α : ℝ}
    (hα : 0 ≤ α) (hαs : α ≤ s.re) (q : CuspCoset) (hq : q ≠ identityCuspCoset) :
    MemLp (cuspWeightedTailTerm J s α q) 2 modularMeasure :=
  MemLp.of_bound (cuspWeightedTailTerm_continuous J s hα q).aestronglyMeasurable _
    (cuspWeightedTailTerm_ae_bound J s hα hαs q hq)

/-- The actual weighted Hilbert class, with no totalized membership assumption. -/
def cuspWeightedTailLp (J : ℤ) (s : ℂ) {α : ℝ} (hα : 0 ≤ α)
    (hαs : α ≤ s.re) (q : {q : CuspCoset // q ≠ identityCuspCoset}) : ModularHilbert :=
  (cuspWeightedTailTerm_memLp J s hα hαs q q.property).toLp (cuspWeightedTailTerm J s α q)

theorem cuspWeightedTailLp_ae (J : ℤ) (s : ℂ) {α : ℝ} (hα : 0 ≤ α)
    (hαs : α ≤ s.re) (q : {q : CuspCoset // q ≠ identityCuspCoset}) :
    cuspWeightedTailLp J s hα hαs q =ᵐ[modularMeasure] cuspWeightedTailTerm J s α q :=
  MemLp.coeFn_toLp _

/-- The finite-measure L² estimate keeps the row majorant explicit. -/
theorem cuspWeightedTailLp_norm_le (J : ℤ) (s : ℂ) {α : ℝ} (hα : 0 ≤ α)
    (hαs : α ≤ s.re) (q : {q : CuspCoset // q ≠ identityCuspCoset}) :
    ‖cuspWeightedTailLp J s hα hαs q‖ ≤
      (measureUnivNNReal modularMeasure : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹ *
        ((2 : ℝ) ^ (s.re - α) * ‖cuspBottomRow q‖ ^ (-(s.re - α))) := by
  apply Lp.norm_le_of_ae_bound (by positivity)
  filter_upwards [cuspWeightedTailLp_ae J s hα hαs q,
    cuspWeightedTailTerm_ae_bound J s hα hαs q q.property] with τ hrep hbound
  rw [hrep]
  exact hbound

/-- The weighted nonidentity tail is absolutely summable in the actual modular L² norm. -/
theorem summable_norm_cuspWeightedTailLp (J : ℤ) (s : ℂ) {α : ℝ}
    (hα : 0 ≤ α) (hgap : 2 < s.re - α) :
    Summable (fun q : {q : CuspCoset // q ≠ identityCuspCoset} =>
      ‖cuspWeightedTailLp J s hα (by linarith) q‖) := by
  have hsum := (summable_nonidentity_cusp_height_majorant hgap).mul_left
    ((measureUnivNNReal modularMeasure : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹)
  exact hsum.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun q => cuspWeightedTailLp_norm_le J s hα (by linarith) q)

/-- The weighted series actually converges in the modular Hilbert space. -/
theorem summable_cuspWeightedTailLp (J : ℤ) (s : ℂ) {α : ℝ}
    (hα : 0 ≤ α) (hgap : 2 < s.re - α) :
    Summable (fun q : {q : CuspCoset // q ≠ identityCuspCoset} =>
      cuspWeightedTailLp J s hα (by linarith) q) :=
  (summable_norm_cuspWeightedTailLp J s hα hgap).of_norm

/-- The actual summed weighted nonidentity vector. -/
def cuspWeightedTail (J : ℤ) (s : ℂ) {α : ℝ}
    (hα : 0 ≤ α) (hgap : 2 < s.re - α) : ModularHilbert :=
  ∑' q : {q : CuspCoset // q ≠ identityCuspCoset},
    cuspWeightedTailLp J s hα (by linarith) q

theorem cuspWeightedTail_hasSum (J : ℤ) (s : ℂ) {α : ℝ}
    (hα : 0 ≤ α) (hgap : 2 < s.re - α) :
    HasSum (fun q : {q : CuspCoset // q ≠ identityCuspCoset} =>
      cuspWeightedTailLp J s hα (by linarith) q) (cuspWeightedTail J s hα hgap) :=
  (summable_cuspWeightedTailLp J s hα hgap).hasSum

/-- The ordinary literal summands sum almost everywhere to the actual Hilbert vector. -/
theorem cuspWeightedTail_hasSum_ae (J : ℤ) (s : ℂ) {α : ℝ}
    (hα : 0 ≤ α) (hgap : 2 < s.re - α) :
    ∀ᵐ τ ∂modularMeasure,
      HasSum (fun q : {q : CuspCoset // q ≠ identityCuspCoset} =>
        cuspWeightedTailTerm J s α q τ) (cuspWeightedTail J s hα hgap τ) := by
  let : Countable CuspCoset := cuspBottomRow_injective.countable
  have hn := tsum_enorm_ne_top_iff_summable_norm.mpr
    (summable_norm_cuspWeightedTailLp J s hα hgap)
  have hs := Lp.hasSum_coeFn_tsum hn
  have hr : ∀ᵐ τ ∂modularMeasure,
      ∀ q : {q : CuspCoset // q ≠ identityCuspCoset},
        cuspWeightedTailLp J s hα (by linarith) q τ = cuspWeightedTailTerm J s α q τ :=
    ae_all_iff.mpr (fun q => cuspWeightedTailLp_ae J s hα (by linarith) q)
  filter_upwards [hs, hr] with τ hs hr
  simpa only [cuspWeightedTail, hr] using hs

/-- In particular the true vector has the literal weighted Poincare-tail representative. -/
theorem cuspWeightedTail_ae (J : ℤ) (s : ℂ) {α : ℝ}
    (hα : 0 ≤ α) (hgap : 2 < s.re - α) :
    cuspWeightedTail J s hα hgap =ᵐ[modularMeasure]
      (fun τ => ∑' q : {q : CuspCoset // q ≠ identityCuspCoset},
        cuspWeightedTailTerm J s α q τ) := by
  filter_upwards [cuspWeightedTail_hasSum_ae J s hα hgap] with τ hτ
  exact hτ.tsum_eq.symm


end GapFamily.Analytic
