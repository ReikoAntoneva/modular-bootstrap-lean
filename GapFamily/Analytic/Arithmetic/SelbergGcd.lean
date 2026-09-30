import GapFamily.Analytic.Arithmetic.Kloosterman
import Mathlib.NumberTheory.Divisors

/-!
# Residue decomposition by its greatest common divisor

Every residue modulo a positive natural number `c` is uniquely a positive divisor
`d` of `c` times a unit modulo `c / d`. The divisor `d = c` is retained: its unit
modulo one represents the zero residue.
-/

noncomputable section

namespace GapFamily.Analytic

/-- A divisor and a primitive residue modulo the complementary divisor. -/
abbrev DivisorUnit (c : ℕ) := Σ d : {d : ℕ // d ∣ c}, (ZMod (c / d.1))ˣ

/-- The actual residue attached to a divisor and a primitive residue. -/
def divisorUnitResidue (c : ℕ) (p : DivisorUnit c) : ZMod c :=
  (p.1.1 * (p.2 : ZMod (c / p.1.1)).val : ℕ)

lemma divisorUnit_divisor_pos {c : ℕ} [NeZero c] (d : {d : ℕ // d ∣ c}) :
    0 < d.1 := Nat.pos_of_ne_zero (fun h => NeZero.ne c (by simpa [h] using d.2))

lemma divisorUnit_quotient_pos {c : ℕ} [NeZero c] (d : {d : ℕ // d ∣ c}) :
    0 < c / d.1 :=
  Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne c)) d.2)
    (divisorUnit_divisor_pos d)

/-- The product representing a residue stays in the standard representative interval. -/
theorem divisorUnitResidue_val {c : ℕ} [NeZero c] (p : DivisorUnit c) :
    (divisorUnitResidue c p).val = p.1.1 * (p.2 : ZMod (c / p.1.1)).val := by
  let : NeZero (c / p.1.1) := ⟨(divisorUnit_quotient_pos p.1).ne'⟩
  have hlt : p.1.1 * (p.2 : ZMod (c / p.1.1)).val < c := by
    calc
      _ < p.1.1 * (c / p.1.1) :=
        Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) (divisorUnit_divisor_pos p.1)
      _ = c := Nat.mul_div_cancel' p.1.2
  exact (ZMod.val_natCast _ _).trans (Nat.mod_eq_of_lt hlt)

/-- The divisor coordinate is exactly the greatest common divisor with the modulus. -/
theorem divisorUnitResidue_gcd {c : ℕ} [NeZero c] (p : DivisorUnit c) :
    (divisorUnitResidue c p).val.gcd c = p.1.1 := by
  rw [divisorUnitResidue_val]
  conv_lhs => arg 2; rw [← Nat.mul_div_cancel' p.1.2]
  rw [Nat.gcd_mul_left, ZMod.val_coe_unit_coprime p.2, Nat.mul_one]

/-- Different divisor–unit coordinates produce different actual residues. -/
theorem divisorUnitResidue_injective {c : ℕ} [NeZero c] :
    Function.Injective (divisorUnitResidue c) := by
  rintro ⟨⟨d, hd⟩, u⟩ ⟨⟨e, he⟩, v⟩ huv
  have hde : d = e := by
    simpa only [divisorUnitResidue_gcd] using
      congrArg (fun x : ZMod c => x.val.gcd c) huv
  subst e
  have hval := congrArg ZMod.val huv
  rw [divisorUnitResidue_val, divisorUnitResidue_val] at hval
  have huv' : (u : ZMod (c / d)).val = (v : ZMod (c / d)).val :=
    Nat.eq_of_mul_eq_mul_left (divisorUnit_divisor_pos ⟨d, hd⟩) hval
  let : NeZero (c / d) := ⟨(divisorUnit_quotient_pos ⟨d, hd⟩).ne'⟩
  have huve : u = v := Units.ext (ZMod.val_injective _ huv')
  subst v
  rfl

/-- Every actual residue has divisor–unit coordinates, including the zero residue. -/
theorem divisorUnitResidue_surjective {c : ℕ} [NeZero c] :
    Function.Surjective (divisorUnitResidue c) := by
  intro x
  let d := x.val.gcd c
  have hd : d ∣ c := Nat.gcd_dvd_right _ _
  have hdx : d ∣ x.val := Nat.gcd_dvd_left _ _
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne c))
  have hcop : Nat.Coprime (x.val / d) (c / d) := Nat.coprime_div_gcd_div_gcd hdpos
  let u : (ZMod (c / d))ˣ := ZMod.unitOfCoprime (x.val / d) hcop
  have hlt : x.val / d < c / d := by
    apply Nat.lt_of_mul_lt_mul_left (a := d)
    simpa only [Nat.mul_div_cancel' hdx, Nat.mul_div_cancel' hd] using ZMod.val_lt x
  refine ⟨⟨⟨d, hd⟩, u⟩, ?_⟩
  change ((d * (u : ZMod (c / d)).val : ℕ) : ZMod c) = x
  have huval : (u : ZMod (c / d)).val = x.val / d := by
    change ((x.val / d : ℕ) : ZMod (c / d)).val = _
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  rw [huval, Nat.mul_div_cancel' hdx, ZMod.natCast_zmod_val]

/-- Canonical classification of every residue by its gcd and a primitive residue. -/
def divisorUnitEquiv (c : ℕ) [NeZero c] : DivisorUnit c ≃ ZMod c :=
  Equiv.ofBijective (divisorUnitResidue c)
    ⟨divisorUnitResidue_injective, divisorUnitResidue_surjective⟩

@[simp] theorem divisorUnitEquiv_apply (c : ℕ) [NeZero c] (p : DivisorUnit c) :
    divisorUnitEquiv c p = (p.1.1 * (p.2 : ZMod (c / p.1.1)).val : ℕ) := rfl

/-- The inverse classification really returns the gcd coordinate. -/
@[simp] theorem divisorUnitEquiv_symm_divisor {c : ℕ} [NeZero c] (x : ZMod c) :
    ((divisorUnitEquiv c).symm x).1.1 = x.val.gcd c := by
  have h := divisorUnitResidue_gcd ((divisorUnitEquiv c).symm x)
  change ((divisorUnitEquiv c) ((divisorUnitEquiv c).symm x)).val.gcd c = _ at h
  simpa only [Equiv.apply_symm_apply] using h.symm

/-- The divisor subtype is finite for a positive modulus. -/
instance divisorFintype (c : ℕ) [NeZero c] : Fintype {d : ℕ // d ∣ c} :=
  Fintype.ofEquiv {d : ℕ // d ∈ c.divisors}
    (Equiv.subtypeEquivRight fun d => by simp [Nat.mem_divisors, NeZero.ne c])

instance divisorNeZero {c : ℕ} [NeZero c] (d : {d : ℕ // d ∣ c}) :
    NeZero d.1 := ⟨(divisorUnit_divisor_pos d).ne'⟩

instance divisorQuotientNeZero {c : ℕ} [NeZero c] (d : {d : ℕ // d ∣ c}) :
    NeZero (c / d.1) := ⟨(divisorUnit_quotient_pos d).ne'⟩

/-- Reindex a finite residue sum by its actual gcd and primitive residue. -/
theorem sum_zmod_eq_sum_divisorUnit {c : ℕ} [NeZero c]
    {A : Type*} [AddCommMonoid A] (f : ZMod c → A) :
    ∑ x : ZMod c, f x =
      ∑ d : {d : ℕ // d ∣ c}, ∑ u : (ZMod (c / d.1))ˣ,
        f (d.1 * (u : ZMod (c / d.1)).val : ℕ) := by
  rw [← (divisorUnitEquiv c).sum_comp f, Fintype.sum_sigma]
  rfl

end GapFamily.Analytic
