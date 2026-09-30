import GapFamily.Analytic.Poincare.PoincareHigherComposition
import GapFamily.Analytic.Poincare.PoincareHigherRow

noncomputable section
namespace GapFamily.Analytic.PoincareHigherComposition
open Set UpperHalfPlane PoincareTermGradient PoincareHigherRow

/-- Every real derivative order of the actual quotient terms has one summable
operator-norm majorant on a compact spatial set and a bounded spectral strip. -/
theorem exists_compact_iteratedFDeriv_majorant (n : ℕ) (J : ℤ) {a b S : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hS : 0 ≤ S)
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ u : CuspCoset → ℝ, Summable u ∧ (∀ q, 0 ≤ u q) ∧
      ∀ (q : CuspCoset) (s : ℂ) (τ : UpperHalfPlane),
        a ≤ s.re → s.re ≤ b → ‖s‖ ≤ S → τ ∈ K →
        ‖iteratedFDeriv ℝ n (term J s q) τ‖ ≤ u q := by
  obtain ⟨M, hM, u, hu, hu0, hub⟩ :=
    exists_compact_height_power_div_majorant_strip n ha hab hK
  let C := termDerivativeConstant n S J M
  have hC : 0 ≤ C := termDerivativeConstant_nonneg n hS J hM.le
  refine ⟨fun q => C * u q, hu.mul_left C,
    fun q => mul_nonneg hC (hu0 q), ?_⟩
  intro q s τ hsa hsb hsS hτ
  calc
    _ ≤ C * (q.out • τ : UpperHalfPlane).im ^ s.re / τ.im ^ n :=
      norm_iteratedFDeriv_term_le n J hsS q τ (hub q s.re τ hsa hsb hτ).1
    _ = C * ((q.out • τ : UpperHalfPlane).im ^ s.re / τ.im ^ n) := by ring
    _ ≤ C * u q :=
      mul_le_mul_of_nonneg_left (hub q s.re τ hsa hsb hτ).2 hC

/-- In the actual convergence half-plane, each fixed spectral parameter has a
summable compact majorant for every order of the genuine real multilinear derivative. -/
theorem exists_compact_iteratedFDeriv_majorant_fixed (n : ℕ) (J : ℤ)
    {s : ℂ} (hs : 1 < s.re) {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ u : CuspCoset → ℝ, Summable u ∧ (∀ q, 0 ≤ u q) ∧
      ∀ (q : CuspCoset) (τ : UpperHalfPlane), τ ∈ K →
        ‖iteratedFDeriv ℝ n (term J s q) τ‖ ≤ u q := by
  obtain ⟨u, hu, hu0, hub⟩ :=
    exists_compact_iteratedFDeriv_majorant n J hs le_rfl (norm_nonneg s) hK
  exact ⟨u, hu, hu0, fun q τ hτ => hub q s τ le_rfl le_rfl le_rfl hτ⟩

/-- The same estimate literally concerns the quotient seed composed with the
ambient upper-half-plane map; it is not a bound for an assumed representative. -/
theorem exists_compact_iteratedFDeriv_complexPoincareTerm_majorant (n : ℕ) (J : ℤ)
    {s : ℂ} (hs : 1 < s.re) {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ u : CuspCoset → ℝ, Summable u ∧ (∀ q, 0 ≤ u q) ∧
      ∀ (q : CuspCoset) (τ : UpperHalfPlane), τ ∈ K →
        ‖iteratedFDeriv ℝ n
          (fun z : ℂ => complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z) q) τ‖ ≤ u q := by
  simpa only [← term_eq_complexPoincareTerm_ofComplex] using
    exists_compact_iteratedFDeriv_majorant_fixed n J hs hK

end GapFamily.Analytic.PoincareHigherComposition
