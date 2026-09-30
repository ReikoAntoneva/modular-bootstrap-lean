import Homogenization.Sobolev.H1.Algebra.H1Function

/-!
# Finite weak Sobolev order from actual H1 witnesses

Order zero is literal local L2 membership. Each successor order consists of
an actual H1Function with the given value and finite-order weak regularity
of each actual gradient coordinate. Restriction, addition, and loss of order
are derived from those witnesses.
-/

namespace GapFamily.Analytic.EllipticSobolev

open Set Homogenization

def weakSobolev {d : ℕ} : ℕ → Set (Vec d) → (Vec d → ℝ) → Prop :=
  Nat.rec (fun U f => MemL2On U f)
    (fun _ previous U f =>
      ∃ u : H1Function U, u.toFun = f ∧
        ∀ i : Fin d, previous U (fun x => u.grad x i))

@[simp] theorem weakSobolev_zero {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) :
    weakSobolev 0 U f ↔ MemL2On U f := Iff.rfl

theorem weakSobolev_succ {d : ℕ} (n : ℕ) (U : Set (Vec d)) (f : Vec d → ℝ) :
    weakSobolev (n + 1) U f ↔
      ∃ u : H1Function U, u.toFun = f ∧
        ∀ i : Fin d, weakSobolev n U (fun x => u.grad x i) := Iff.rfl

/-- Order one is exactly the existence of an actual H1 witness for the literal value. -/
theorem weakSobolev_one {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) :
    weakSobolev 1 U f ↔ ∃ u : H1Function U, u.toFun = f := by
  constructor
  · rintro ⟨u, hu, _⟩
    exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, hu, fun i => u.gradMemL2 i⟩

/-- Every finite-order witness restricts using the actual H1 restriction. -/
theorem weakSobolev_restrict {d n : ℕ} {U V : Set (Vec d)} {f : Vec d → ℝ}
    (h : weakSobolev n U f) (hV : IsOpen V) (hVU : V ⊆ U) :
    weakSobolev n V f := by
  induction n generalizing U V f with
  | zero => exact memL2On_mono hVU h
  | succ n ih =>
    obtain ⟨u, hu, hgrad⟩ := h
    refine ⟨u.restrict hV hVU, hu, ?_⟩
    intro i
    exact ih (hgrad i) hV hVU

/-- Finite-order weak regularity is closed under literal pointwise addition. -/
theorem weakSobolev_add {d n : ℕ} {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : weakSobolev n U f) (hg : weakSobolev n U g) :
    weakSobolev n U (fun x => f x + g x) := by
  induction n generalizing f g with
  | zero => exact hf.add hg
  | succ n ih =>
    obtain ⟨u, hu, hDu⟩ := hf
    obtain ⟨v, hv, hDv⟩ := hg
    refine ⟨u + v, ?_, ?_⟩
    · change (fun x => u.toFun x + v.toFun x) = (fun x => f x + g x)
      rw [hu, hv]
    · intro i
      exact ih (hDu i) (hDv i)

/-- Drop one derivative order using the same actual H1 witness. -/
theorem weakSobolev_succ_down {d n : ℕ} {U : Set (Vec d)} {f : Vec d → ℝ}
    (h : weakSobolev (n + 1) U f) : weakSobolev n U f := by
  induction n generalizing f with
  | zero =>
    obtain ⟨u, hu, _⟩ := h
    exact hu ▸ u.memL2
  | succ n ih =>
    obtain ⟨u, hu, hgrad⟩ := h
    exact ⟨u, hu, fun i => ih (hgrad i)⟩

/-- A witness of higher finite order supplies every smaller finite order. -/
theorem weakSobolev_mono_order {d m n : ℕ} {U : Set (Vec d)} {f : Vec d → ℝ}
    (hmn : m ≤ n) : weakSobolev n U f → weakSobolev m U f := by
  induction hmn with
  | refl => exact id
  | step hmn ih => exact fun h => ih (weakSobolev_succ_down h)

end GapFamily.Analytic.EllipticSobolev
