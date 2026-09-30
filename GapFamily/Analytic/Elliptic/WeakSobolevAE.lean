import GapFamily.Analytic.Elliptic.WeakSobolevOrder

/-!
# Finite weak Sobolev order under AE replacement

Replacing the value of an actual H1 witness by an AE-equal function preserves
its gradient and its literal weak integral identities. The higher derivative
witnesses are retained, without converting AE equality to pointwise equality.
-/

namespace GapFamily.Analytic.EllipticSobolev

open Set MeasureTheory Homogenization

/-- Replace the value representative while retaining the actual weak gradient. -/
def replaceValueAE {d : ℕ} {U : Set (Vec d)} (u : H1Function U) (g : Vec d → ℝ)
    (hug : u.toFun =ᵐ[volume.restrict U] g) : H1Function U where
  toFun := g
  grad := u.grad
  memL2 := (memLp_congr_ae hug).mp u.memL2
  gradMemL2 := u.gradMemL2
  hasWeakGradient := by
    intro i φ hφ hc hs
    calc
      (∫ x in U, g x * fderiv ℝ φ x (basisVec i)) =
          ∫ x in U, u.toFun x * fderiv ℝ φ x (basisVec i) := by
        apply integral_congr_ae
        filter_upwards [hug] with x hx
        rw [hx]
      _ = -(∫ x in U, u.grad x i * φ x) := u.hasWeakGradient i φ hφ hc hs

@[simp] theorem replaceValueAE_toFun {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) (g : Vec d → ℝ) (hug : u.toFun =ᵐ[volume.restrict U] g) :
    (replaceValueAE u g hug).toFun = g := rfl

@[simp] theorem replaceValueAE_grad {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) (g : Vec d → ℝ) (hug : u.toFun =ᵐ[volume.restrict U] g) :
    (replaceValueAE u g hug).grad = u.grad := rfl

/-- Every finite weak Sobolev order is invariant under actual AE replacement of its value. -/
theorem weakSobolev_congr_ae {d n : ℕ} {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : weakSobolev n U f) (hfg : f =ᵐ[volume.restrict U] g) :
    weakSobolev n U g := by
  cases n with
  | zero => exact (memLp_congr_ae hfg).mp hf
  | succ n =>
    obtain ⟨u, hu, hgrad⟩ := hf
    have hug : u.toFun =ᵐ[volume.restrict U] g := by
      rw [hu]
      exact hfg
    exact ⟨replaceValueAE u g hug, rfl, hgrad⟩

theorem weakSobolev_congr_ae_iff {d n : ℕ} {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hfg : f =ᵐ[volume.restrict U] g) :
    weakSobolev n U f ↔ weakSobolev n U g :=
  ⟨fun hf => weakSobolev_congr_ae hf hfg, fun hg => weakSobolev_congr_ae hg hfg.symm⟩

end GapFamily.Analytic.EllipticSobolev
