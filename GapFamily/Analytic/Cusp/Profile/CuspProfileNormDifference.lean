import GapFamily.Analytic.Cusp.Profile.CuspProfileNorm
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactCore

/-!
# Actual graph-norm differences of compact scalar cusp profiles

The periodized value, gradient, and completed form vectors respect profile
subtraction. Their exact difference norms are ordinary scalar integrals,
providing the direct Cauchy criterion for the subsequent graph-closure lift.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory ModularGradient
open scoped ContDiff

theorem cuspProfile_tsupport_sub {b c : ℝ → ℂ}
    (hb : tsupport b ⊆ Ioi (1 : ℝ)) (hc : tsupport c ⊆ Ioi (1 : ℝ)) :
    tsupport (b - c) ⊆ Ioi (1 : ℝ) :=
  (tsupport_sub b c).trans (union_subset hb hc)

variable (b c : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : ContDiff ℝ ∞ c)
  (hbc : HasCompactSupport b) (hcc : HasCompactSupport c)
  (hbs : tsupport b ⊆ Ioi (1 : ℝ)) (hcs : tsupport c ⊆ Ioi (1 : ℝ))

theorem cuspProfileCore_value_sub :
    value (cuspProfileCore (b - c) (hb.sub hc) (hbc.sub hcc) (cuspProfile_tsupport_sub hbs hcs)) =
      value (cuspProfileCore b hb hbc hbs) - value (cuspProfileCore c hc hcc hcs) := by
  apply Lp.ext
  filter_upwards [cuspProfileCore_value_ae (b - c) (hb.sub hc) (hbc.sub hcc)
      (cuspProfile_tsupport_sub hbs hcs),
    cuspProfileCore_value_ae b hb hbc hbs, cuspProfileCore_value_ae c hc hcc hcs,
    Lp.coeFn_sub (value (cuspProfileCore b hb hbc hbs)) (value (cuspProfileCore c hc hcc hcs))]
      with τ hsub hbτ hcτ hd
  simp only [hsub, hd, Pi.sub_apply, hbτ, hcτ]

theorem cuspProfileCore_gradient_sub :
    coreGradient
      (cuspProfileCore (b - c) (hb.sub hc) (hbc.sub hcc) (cuspProfile_tsupport_sub hbs hcs)) =
      coreGradient (cuspProfileCore b hb hbc hbs) - coreGradient (cuspProfileCore c hc hcc hcs) := by
  have hv : value (cuspProfileCore b hb hbc hbs - cuspProfileCore c hc hcc hcs) =
      value (cuspProfileCore (b - c) (hb.sub hc) (hbc.sub hcc) (cuspProfile_tsupport_sub hbs hcs)) := by
    rw [map_sub]
    exact (cuspProfileCore_value_sub b c hb hc hbc hcc hbs hcs).symm
  simpa only [map_sub] using (coreGradient_eq_of_value_eq hv).symm

theorem cuspProfileCore_form_sub :
    coreForm (cuspProfileCore (b - c) (hb.sub hc) (hbc.sub hcc) (cuspProfile_tsupport_sub hbs hcs)) =
      coreForm (cuspProfileCore b hb hbc hbs) - coreForm (cuspProfileCore c hc hcc hcs) := by
  apply formEmbedding_injective
  simp only [map_sub, formEmbedding_coreForm]
  exact cuspProfileCore_value_sub b c hb hc hbc hcc hbs hcs

theorem cuspProfileCore_value_sub_norm_sq :
    ‖value (cuspProfileCore b hb hbc hbs) - value (cuspProfileCore c hc hcc hcs)‖ ^ 2 =
      ∫ y : ℝ in Ioi 1, ‖b y - c y‖ ^ 2 / y ^ 2 := by
  rw [← cuspProfileCore_value_sub b c hb hc hbc hcc hbs hcs]
  exact (cuspProfileCore_value_norm_sq (b - c) (hb.sub hc) (hbc.sub hcc)
    (cuspProfile_tsupport_sub hbs hcs)).2

theorem cuspProfileCore_gradient_sub_norm_sq :
    ‖coreGradient (cuspProfileCore b hb hbc hbs) - coreGradient (cuspProfileCore c hc hcc hcs)‖ ^ 2 =
      ∫ y : ℝ in Ioi 1, ‖deriv b y - deriv c y‖ ^ 2 := by
  rw [← cuspProfileCore_gradient_sub b c hb hc hbc hcc hbs hcs,
    (cuspProfileCore_gradient_norm_sq (b - c) (hb.sub hc) (hbc.sub hcc)
      (cuspProfile_tsupport_sub hbs hcs)).2]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    rw [deriv_sub ((hb.differentiable (by simp)) y) ((hc.differentiable (by simp)) y)])

/-- The actual completed form difference is exactly the weighted scalar H¹ difference. -/
theorem cuspProfileCore_form_sub_norm_sq :
    ‖coreForm (cuspProfileCore b hb hbc hbs) - coreForm (cuspProfileCore c hc hcc hcs)‖ ^ 2 =
      (∫ y : ℝ in Ioi 1, ‖b y - c y‖ ^ 2 / y ^ 2) +
        ∫ y : ℝ in Ioi 1, ‖deriv b y - deriv c y‖ ^ 2 := by
  rw [formDomain_norm_sq]
  simp only [map_sub, formEmbedding_coreForm, formGradient_coreForm]
  rw [cuspProfileCore_value_sub_norm_sq, cuspProfileCore_gradient_sub_norm_sq]

end GapFamily.Analytic
