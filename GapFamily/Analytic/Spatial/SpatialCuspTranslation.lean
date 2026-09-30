import GapFamily.Analytic.Poincare.Poincare

noncomputable section
namespace GapFamily.Analytic

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- Signed translations are the literal matrices in the cusp stabilizer. -/
def signedCuspTranslation (p : ℤ × Bool) : cuspInfinity :=
  ⟨if p.2 then -(ModularGroup.T ^ p.1) else ModularGroup.T ^ p.1, by
    change (if p.2 then -(ModularGroup.T ^ p.1) else ModularGroup.T ^ p.1) 1 0 = 0
    cases p.2 <;> simp [ModularGroup.coe_T_zpow]⟩

theorem signedCuspTranslation_injective : Function.Injective signedCuspTranslation := by
  rintro ⟨n, b⟩ ⟨m, c⟩ he
  have h00 := congrArg (fun g : cuspInfinity => (g : SL(2, ℤ)) 0 0) he
  have h01 := congrArg (fun g : cuspInfinity => (g : SL(2, ℤ)) 0 1) he
  cases b <;> cases c <;>
    simp [signedCuspTranslation, ModularGroup.coe_T_zpow] at h00 h01 ⊢
  all_goals assumption

theorem signedCuspTranslation_surjective : Function.Surjective signedCuspTranslation := by
  intro g
  have hc : (g : SL(2, ℤ)) 1 0 = 0 := g.property
  have had := (g : SL(2, ℤ)).det_coe
  replace had : (g : SL(2, ℤ)) 0 0 * (g : SL(2, ℤ)) 1 1 = 1 := by
    rw [det_fin_two, hc] at had
    lia
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with (⟨ha, hd⟩ | ⟨ha, hd⟩)
  · refine ⟨⟨(g : SL(2, ℤ)) 0 1, false⟩, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [signedCuspTranslation, ModularGroup.coe_T_zpow, ha, hc, hd,
        show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]
  · refine ⟨⟨-(g : SL(2, ℤ)) 0 1, true⟩, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [signedCuspTranslation, ModularGroup.coe_T_zpow, ha, hc, hd,
        show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]

/-- Every integer translation has exactly its two central matrix signs. -/
def cuspTranslationEquiv : (ℤ × Bool) ≃ cuspInfinity :=
  Equiv.ofBijective signedCuspTranslation
    ⟨signedCuspTranslation_injective, signedCuspTranslation_surjective⟩

@[simp] theorem cuspTranslationEquiv_smul (n : ℤ) (b : Bool) (z : UpperHalfPlane) :
    (cuspTranslationEquiv (n, b) : SL(2, ℤ)) • z = ModularGroup.T ^ n • z := by
  change (if b then -(ModularGroup.T ^ n) else ModularGroup.T ^ n) • z = _
  cases b
  · rfl
  · exact ModularGroup.SL_neg_smul _ _

end GapFamily.Analytic
