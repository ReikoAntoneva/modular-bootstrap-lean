import GapFamily.Analytic.Elliptic.WeakSobolevOrder
import Homogenization.Sobolev.H1.BasicLemmas
import Homogenization.Sobolev.Foundations.EuclideanL2CZ

/-! All finite weak-derivative orders are preserved by actual smooth compact coefficients. -/
noncomputable section
namespace GapFamily.Analytic.EllipticSobolev
open Set MeasureTheory Homogenization
open scoped ContDiff

/-- Multiplication by a genuine smooth compact coefficient preserves every
finite Sobolev order. The successor step uses the actual H1 Leibniz gradient,
not an assumed family of higher weak derivatives. -/
theorem weakSobolev_mul_smoothCompact {d n : ℕ} {U : Set (Vec d)}
    {f a : Vec d → ℝ} (hf : weakSobolev n U f)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) :
    weakSobolev n U (fun x => a x * f x) := by
  induction n generalizing f a with
  | zero =>
      change MemL2On U (fun x => a x * f x)
      have haTop : MemLp a ⊤ (volume.restrict U) :=
        (ha.continuous.memLp_of_hasCompactSupport hc).restrict U
      exact haTop.fun_mul (r := 2) hf
  | succ n ih =>
      have hdown := weakSobolev_succ_down hf
      obtain ⟨u, hu, hgrad⟩ := hf
      refine ⟨u.mulContDiffHasCompactSupport ha hc, ?_, ?_⟩
      · rw [H1Function.mulContDiffHasCompactSupport_toFun, hu]
      · intro i
        change weakSobolev n U
          (fun x => (u.mulContDiffHasCompactSupport ha hc).grad x i)
        have hfirst := ih (hgrad i) ha hc
        have hsecond := ih hdown (contDiff_euclideanCoordDeriv ha i)
          (hasCompactSupport_euclideanCoordDeriv hc i)
        have hsecond' : weakSobolev n U
            (fun x => u x * (fderiv ℝ a x) (basisVec i)) := by
          simpa only [← hu, euclideanCoordDeriv, mul_comm] using hsecond
        simpa only [H1Function.mulContDiffHasCompactSupport_grad] using
          weakSobolev_add hfirst hsecond'

/-- Smooth compact functions supply actual finite weak derivatives at every
order, with the classical coordinate derivative at each induction step. -/
theorem weakSobolev_smoothCompact {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (n : ℕ) :
    weakSobolev n U f := by
  induction n generalizing f with
  | zero =>
      exact (hf.continuous.memLp_of_hasCompactSupport hc).restrict U
  | succ n ih =>
      refine ⟨H1Function.ofContDiff hU (hf.of_le (by simp)) hc, rfl, ?_⟩
      intro i
      exact ih (contDiff_euclideanCoordDeriv hf i)
        (hasCompactSupport_euclideanCoordDeriv hc i)

/-- The actual smooth-potential source a*u+g has each finite weak order
already proved for u. This is the source closure needed for repeated elliptic gain. -/
theorem weakSobolev_smoothPotentialSource {d n : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {u a g : Vec d → ℝ} (hu : weakSobolev n U u)
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    weakSobolev n U (fun x => a x * u x + g x) :=
  weakSobolev_add (weakSobolev_mul_smoothCompact hu ha hac)
    (weakSobolev_smoothCompact hU hg hgc n)

end GapFamily.Analytic.EllipticSobolev
