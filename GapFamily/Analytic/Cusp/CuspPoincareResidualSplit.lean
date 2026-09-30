import GapFamily.Analytic.Poincare.PoincareAnalytic

noncomputable section
namespace GapFamily.Analytic

/-- The nonidentity part of the actual complex cusp series is convergent. -/
theorem summable_complexPoincareTerm_nonidentity (E : ℂ) (J : ℤ) {s : ℂ}
    (hs : 1 < s.re) (τ : UpperHalfPlane) :
    Summable (fun q : {q : CuspCoset // q ≠ identityCuspCoset} =>
      complexPoincareTerm E J s τ q) :=
  (summable_norm_complexPoincareTerm E J hs τ).of_norm.subtype _

/-- The identity-coset contribution is exactly the literal complex point seed. -/
theorem complexPoincareSeries_direct_term (E : ℂ) (J : ℤ) {s : ℂ}
    (hs : 1 < s.re) (τ : UpperHalfPlane) :
    complexPoincareSeries E J s τ = complexPointSeed E J s τ +
      ∑' q : {q : CuspCoset // q ≠ identityCuspCoset}, complexPoincareTerm E J s τ q := by
  classical
  have h := (summable_norm_complexPoincareTerm E J hs τ).of_norm.sum_add_tsum_compl
    (s := {identityCuspCoset})
  simp only [Finset.sum_singleton, complexPoincareTerm_identity] at h
  let e : {q : CuspCoset // q ≠ identityCuspCoset} ≃
      ↑((↑({identityCuspCoset} : Finset CuspCoset) : Set CuspCoset)ᶜ) :=
    Equiv.subtypeEquivRight (fun _ => by simp)
  calc
    _ = complexPointSeed E J s τ + ∑' q :
        ↑((↑({identityCuspCoset} : Finset CuspCoset) : Set CuspCoset)ᶜ),
          complexPoincareTerm E J s τ q := h.symm
    _ = _ := congrArg (complexPointSeed E J s τ + ·)
      (e.tsum_eq (fun q => complexPoincareTerm E J s τ q)).symm

/-- Subtracting any scalar cutoff of the direct seed leaves the actual
nonidentity series plus the complementary direct seed. -/
theorem complexPoincareSeries_residual_split (E : ℂ) (J : ℤ) {s : ℂ}
    (hs : 1 < s.re) (τ : UpperHalfPlane) (χ : ℂ) :
    complexPoincareSeries E J s τ - χ * complexPointSeed E J s τ =
      (∑' q : {q : CuspCoset // q ≠ identityCuspCoset}, complexPoincareTerm E J s τ q) +
        (1 - χ) * complexPointSeed E J s τ := by
  rw [complexPoincareSeries_direct_term E J hs τ]
  ring

/-- The shifted zero-energy residual split holds throughout its actual
convergence half-plane, including the intended neighborhood of s=1/2. -/
theorem complexPoincareSeries_shifted_zero_residual_split (J : ℤ) {s : ℂ}
    (hs : -1 < s.re) (τ : UpperHalfPlane) (χ : ℂ) :
    complexPoincareSeries 0 J (s + 2) τ - χ * complexPointSeed 0 J (s + 2) τ =
      (∑' q : {q : CuspCoset // q ≠ identityCuspCoset},
        complexPoincareTerm 0 J (s + 2) τ q) +
        (1 - χ) * complexPointSeed 0 J (s + 2) τ := by
  apply complexPoincareSeries_residual_split
  norm_num [Complex.add_re]
  linarith


end GapFamily.Analytic
