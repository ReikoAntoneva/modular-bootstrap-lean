import BTZEntropy.Analytic.PartitionBound
import BTZEntropy.Analytic.DescendantThermal

/-!
# The actual eta function on the thermal axis

The Euler product is identified with mathlib's Dedekind eta function, retaining
the exact `1/24` chiral shift. No abstract character is substituted for eta.
-/

noncomputable section

open Function

namespace BTZEntropy

/-- Zero angular potential at inverse temperature `β`. -/
def thermalPoint (β : ℝ) (hβ : 0 < β) : UpperHalfPlane :=
  ⟨((β / (2 * Real.pi) : ℝ) : ℂ) * Complex.I,
    by
      rw [Complex.mul_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_im,
        Complex.I_re, mul_one, mul_zero, add_zero]
      exact div_pos hβ (by positivity)⟩

/-- The real nome on the positive thermal axis. -/
def thermalNome (β : ℝ) : ℝ := Real.exp (-β)

theorem thermalNome_pos (β : ℝ) : 0 < thermalNome β := Real.exp_pos _

theorem thermalNome_lt_one {β : ℝ} (hβ : 0 < β) : thermalNome β < 1 := by
  exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hβ)

theorem qParam_thermalPoint (β : ℝ) (hβ : 0 < β) (h : ℝ) :
    Periodic.qParam h (thermalPoint β hβ : ℂ) =
      (Real.exp (-β / h) : ℂ) := by
  rw [Complex.ofReal_exp]
  unfold Periodic.qParam thermalPoint
  congr 1
  push_cast
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  simp [Complex.I_sq]
  ring

theorem qPower_thermalPoint (β : ℝ) (hβ : 0 < β) (r : ℝ) :
    GapFamily.qPower r (thermalPoint β hβ) = (Real.exp (-β * r) : ℂ) := by
  rw [Complex.ofReal_exp]
  unfold GapFamily.qPower thermalPoint
  congr 1
  push_cast
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  simp [Complex.I_sq]

theorem eta_q_thermalPoint (β : ℝ) (hβ : 0 < β) (n : ℕ) :
    ModularForm.eta_q n (thermalPoint β hβ : ℂ) =
      ((thermalNome β ^ (n + 1) : ℝ) : ℂ) := by
  unfold ModularForm.eta_q
  rw [qParam_thermalPoint]
  simp [thermalNome]

/-- The convergent positive reciprocal Euler product used by the thermal modules. -/
def descendantEuler (β : ℝ) : ℝ := ∏' n, partitionEulerFactor (thermalNome β) n

theorem descendantEuler_pos {β : ℝ} (hβ : 0 < β) : 0 < descendantEuler β :=
  lt_of_lt_of_le zero_lt_one
    (one_le_partitionEulerProduct (thermalNome_pos β).le (thermalNome_lt_one hβ))

/-- The un-inverted real Euler product has the inverse descendant product as limit. -/
theorem hasProd_thermalEuler {β : ℝ} (hβ : 0 < β) :
    HasProd (fun n : ℕ => 1 - thermalNome β ^ (n + 1)) (descendantEuler β)⁻¹ := by
  have h := (multipliable_partitionEulerFactor (thermalNome_pos β).le
    (thermalNome_lt_one hβ)).hasProd.inv₀ (ne_of_gt (descendantEuler_pos hβ))
  simpa only [partitionEulerFactor, inv_inv, descendantEuler] using h

/-- The exact eta value on the imaginary axis, with no discarded finite-charge shift. -/
theorem eta_thermalPoint (β : ℝ) (hβ : 0 < β) :
    ModularForm.eta (thermalPoint β hβ : ℂ) =
      ((Real.exp (-β / 24) * (descendantEuler β)⁻¹ : ℝ) : ℂ) := by
  have hprod := (hasProd_thermalEuler hβ).map Complex.ofRealHom Complex.continuous_ofReal
  unfold ModularForm.eta
  rw [qParam_thermalPoint]
  push_cast
  congr 1
  calc
    _ = ∏' n, Complex.ofRealHom (1 - thermalNome β ^ (n + 1)) := by
      apply tprod_congr
      intro n
      simp [eta_q_thermalPoint]
    _ = _ := by simpa using hprod.tprod_eq

/-- The physical chiral primary character includes its exact cylinder ground energy. -/
theorem primaryCharacter_thermalPoint (β : ℝ) (hβ : 0 < β) (c h : ℝ) :
    GapFamily.primaryCharacter c h (thermalPoint β hβ) =
      ((Real.exp (-β * (h - c / 24)) * descendantEuler β : ℝ) : ℂ) := by
  unfold GapFamily.primaryCharacter
  rw [qPower_thermalPoint, eta_thermalPoint, ← Complex.ofReal_div]
  apply congrArg Complex.ofReal
  have hexp : Real.exp (-β * (h - GapFamily.shift c / 2)) /
      Real.exp (-β / 24) = Real.exp (-β * (h - c / 24)) := by
    rw [← Real.exp_sub]
    congr 1
    unfold GapFamily.shift
    ring
  rw [div_mul_eq_div_div, div_inv_eq_mul, hexp]

/-- The vacuum character removes the level-one null module and keeps the full
finite-charge vacuum energy. -/
theorem vacuumCharacter_thermalPoint (β : ℝ) (hβ : 0 < β) (c : ℝ) :
    GapFamily.vacuumCharacter c (thermalPoint β hβ) =
      ((Real.exp (β * c / 24) * (1 - Real.exp (-β)) * descendantEuler β : ℝ) : ℂ) := by
  unfold GapFamily.vacuumCharacter
  rw [qPower_thermalPoint, qPower_thermalPoint, eta_thermalPoint]
  simp only [mul_one]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
    ← Complex.ofReal_div]
  apply congrArg Complex.ofReal
  have hexp : Real.exp (-β * (-GapFamily.shift c / 2)) /
      Real.exp (-β / 24) = Real.exp (β * c / 24) := by
    rw [← Real.exp_sub]
    congr 1
    unfold GapFamily.shift
    ring
  rw [div_mul_eq_div_div, div_inv_eq_mul, mul_div_right_comm, hexp]

theorem primaryCharacter_product_thermalPoint (β : ℝ) (hβ : 0 < β)
    (c : ℝ) (p : ℝ × ℝ) :
    GapFamily.primaryCharacter c p.1 (thermalPoint β hβ) *
      star (GapFamily.primaryCharacter c p.2 (thermalPoint β hβ)) =
      ((Real.exp (β * c / 12) * Real.exp (-β * GapFamily.dimension p) *
        descendantEuler β ^ 2 : ℝ) : ℂ) := by
  rw [primaryCharacter_thermalPoint, primaryCharacter_thermalPoint]
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [← Real.exp_add]
  have he : β * c / 12 + -β * GapFamily.dimension p =
      -β * (p.1 - c / 24) + -β * (p.2 - c / 24) := by
    unfold GapFamily.dimension
    ring
  rw [he, Real.exp_add]
  ring

theorem vacuumCharacter_product_thermalPoint (β : ℝ) (hβ : 0 < β) (c : ℝ) :
    GapFamily.vacuumCharacter c (thermalPoint β hβ) *
      star (GapFamily.vacuumCharacter c (thermalPoint β hβ)) =
      ((Real.exp (β * c / 12) *
        ((1 - Real.exp (-β)) * descendantEuler β) ^ 2 : ℝ) : ℂ) := by
  rw [vacuumCharacter_thermalPoint]
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [show β * c / 12 = β * c / 24 + β * c / 24 by ring, Real.exp_add]
  ring

/-- The literal character partition function on the thermal axis. Both the
vacuum and every primary use the same actual eta product. -/
theorem partitionFunction_thermalPoint (β : ℝ) (hβ : 0 < β)
    (c : ℝ) (s : GapFamily.Spectrum) :
    GapFamily.partitionFunction c s (thermalPoint β hβ) =
      ((Real.exp (β * c / 12) *
        (((1 - Real.exp (-β)) * descendantEuler β) ^ 2 +
          primaryThermal β s * descendantEuler β ^ 2) : ℝ) : ℂ) := by
  unfold GapFamily.partitionFunction
  rw [vacuumCharacter_product_thermalPoint]
  have hterm (p : s.support) :
      (s.multiplicity p : ℂ) *
        GapFamily.primaryCharacter c p.val.1 (thermalPoint β hβ) *
        star (GapFamily.primaryCharacter c p.val.2 (thermalPoint β hβ)) =
      ((Real.exp (β * c / 12) * primaryThermalTerm β s p *
        descendantEuler β ^ 2 : ℝ) : ℂ) := by
    rw [mul_assoc, primaryCharacter_product_thermalPoint]
    change (((s.multiplicity p : ℝ) : ℂ) * _) = _
    rw [← Complex.ofReal_mul]
    apply congrArg Complex.ofReal
    unfold primaryThermalTerm
    ring
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_add]
  apply congrArg Complex.ofReal
  rw [tsum_mul_right, tsum_mul_left]
  unfold primaryThermal
  ring

end BTZEntropy
