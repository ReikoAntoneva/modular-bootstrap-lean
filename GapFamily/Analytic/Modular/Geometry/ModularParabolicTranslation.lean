/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the pinned mathlib LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu

The matrix case analysis is adapted from ModularGroup.exists_eq_T_zpow_of_c_eq_zero
in Mathlib/NumberTheory/Modular.lean, mathlib commit
5ed2965256430c3649e86755f9576b54eca72435. The conclusion retains the two matrices
rather than passing to equality of their actions.
-/
import Mathlib.NumberTheory.Modular

namespace GapFamily.Analytic
open Matrix Matrix.SpecialLinearGroup ModularGroup
open scoped MatrixGroups

theorem parabolic_eq_T_zpow_or_neg {g : SL(2, ℤ)} (hc : g 1 0 = 0) :
    ∃ n : ℤ, g = T ^ n ∨ g = -(T ^ n) := by
  have had := g.det_coe
  replace had : g 0 0 * g 1 1 = 1 := by rw [det_fin_two, hc] at had; omega
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with (⟨ha, hd⟩ | ⟨ha, hd⟩)
  · refine ⟨g 0 1, Or.inl ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ha, hc, hd, coe_T_zpow, show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]
  · refine ⟨-(g 0 1), Or.inr ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ha, hc, hd, coe_T_zpow, show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]

end GapFamily.Analytic
