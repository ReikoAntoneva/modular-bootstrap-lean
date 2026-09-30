import BTZEntropy.Contract
import GapFamily.GapFamilyLimit

/-! Uniform remainder estimates on the real central charge. -/

noncomputable section

open Set Filter

namespace BTZEntropy

universe u

theorem UniformRemainder.add {ι : Type u} {B : ℝ} {selectors : Set ι} {q : ℕ}
    {f g : ι → ℝ → ℝ → ℝ → ℝ}
    (hf : UniformRemainder B selectors q f) (hg : UniformRemainder B selectors q g) :
    UniformRemainder B selectors q (fun σ a δ x => f σ a δ x + g σ a δ x) := by
  intro L U hL hLU
  obtain ⟨Cf, hCf, Nf, hNf, hf⟩ := hf L U hL hLU
  obtain ⟨Cg, hCg, Ng, hNg, hg⟩ := hg L U hL hLU
  refine ⟨Cf + Cg, add_pos hCf hCg, max Nf Ng,
    hNf.trans (le_max_left _ _), ?_⟩
  intro σ hσ a hK δ hδ x hx
  calc
    |f σ a δ x + g σ a δ x| ≤ |f σ a δ x| + |g σ a δ x| := abs_add_le _ _
    _ ≤ Cf / GapFamily.gapFamilyCharge a ^ q +
        Cg / GapFamily.gapFamilyCharge a ^ q :=
      add_le_add (hf σ hσ a ((le_max_left _ _).trans hK) δ hδ x hx)
        (hg σ hσ a ((le_max_right _ _).trans hK) δ hδ x hx)
    _ = (Cf + Cg) / GapFamily.gapFamilyCharge a ^ q := (add_div _ _ _).symm

/-- Positive inverse powers become uniformly small at a real threshold;
no parameter of the spectral family occurs in this threshold. -/
theorem eventually_const_div_charge_pow_le_half (C : ℝ) {q : ℕ} (hq : 1 ≤ q) :
    ∀ᶠ a : ℝ in atTop, C / GapFamily.gapFamilyCharge a ^ q ≤ 1 / 2 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    GapFamily.tendsto_gapFamilyCharge_atTop.eventually_ge_atTop (2 * C)] with a hK hC
  have hc : 1 < GapFamily.gapFamilyCharge a := GapFamily.gapFamilyCharge_gt_one (by linarith)
  have hp : GapFamily.gapFamilyCharge a ≤ GapFamily.gapFamilyCharge a ^ q :=
    le_self_pow₀ hc.le (by omega)
  apply (div_le_iff₀ (pow_pos (by linarith : 0 < GapFamily.gapFamilyCharge a) q)).2
  nlinarith

end BTZEntropy
