import GapFamily.Analytic.Elliptic.WeakSobolevOrder
import GapFamily.Analytic.Elliptic.WeakHessianContinuousGradient

noncomputable section
namespace GapFamily.Analytic.EllipticSobolev

open Set MeasureTheory Homogenization ModularElliptic

/-- The order-two witnesses supply the actual Hessian: its `(i,j)` entry
is the `j`th weak derivative in the H1 witness for gradient coordinate `i`. -/
theorem weakSobolev_two_exists_h1_hessian {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → ℝ} (hf : weakSobolev 2 U f) :
    ∃ u : H1Function U, u.toFun = f ∧ Nonempty (HasWeakHessianOn U u) := by
  classical
  obtain ⟨u, hu, hgrad⟩ := hf
  have hvex (i : Fin d) : ∃ v : H1Function U, v.toFun = fun x => u.grad x i :=
    (weakSobolev_one U _).mp (hgrad i)
  choose v hv using hvex
  let H : HasWeakHessianOn U u :=
    { hess := fun i j x => (v i).grad x j
      hess_memL2 := fun i j => (v i).gradMemL2 j
      weak_second := by
        intro i j
        rw [← hv i]
        exact (v i).hasWeakPartialDerivOn j }
  exact ⟨u, hu, ⟨H⟩⟩

/-- Actual finite weak order two gives a continuous representative on an
open neighborhood of zero contained in the original open set. -/
theorem exists_local_continuous_of_weakSobolev_two {U : Set (Vec 2)}
    (hU : IsOpen U) (h0 : (0 : Vec 2) ∈ U) {f : Vec 2 → ℝ}
    (hf : weakSobolev 2 U f) :
    ∃ V : Set (Vec 2), IsOpen V ∧ (0 : Vec 2) ∈ V ∧ V ⊆ U ∧
      ∃ g : Vec 2 → ℝ, ContinuousOn g V ∧ g =ᵐ[volume.restrict V] f := by
  obtain ⟨u, hu, ⟨H⟩⟩ := weakSobolev_two_exists_h1_hessian hf
  obtain ⟨Q, hcenter, hQU, _⟩ := exists_centered_cube_closed_subset hU h0
  have hhalf : scaledOpenCubeSet Q (1 / 2) ⊆ U :=
    (scaledOpenCubeSet_subset_scaledClosedCubeSet Q (1 / 2)).trans
      ((scaledClosedCubeSet_mono Q (by norm_num : (1 : ℝ) / 2 ≤ 1)).trans hQU)
  have hopen := isOpen_scaledOpenCubeSet Q (1 / 2)
  obtain ⟨V, hVo, hV0, _hVc, hVQ, g, hgc, hgf⟩ :=
    WeakHessianContinuousGradient.exists_local_continuous_real_halfCube
      Q hcenter (u.restrict hopen hhalf) (H.restrict hopen hhalf)
  refine ⟨V, hVo, hV0, (subset_closure.trans hVQ).trans hhalf, g, hgc, ?_⟩
  change g =ᵐ[volume.restrict V] u.toFun at hgf
  simpa only [hu] using hgf

end GapFamily.Analytic.EllipticSobolev
