import GapFamily.Analytic.Elliptic.LocalPoissonJet
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
A bounded retraction onto the actual closed local Poisson jet space.
The ambient Jet retains its ordinary product norm. Orthogonal projection is
used only after an explicit continuous linear equivalence with a Hilbert product.
-/

noncomputable section
namespace GapFamily.Analytic.LocalPoisson

open Set

abbrev HilbertJetPair := WithLp 2 (Field × Field)
abbrev HilbertJetTriple := WithLp 2 (Field × HilbertJetPair)
abbrev HilbertJet := WithLp 2 (Field × HilbertJetTriple)

/-- The four-field Hilbert product has the same linear topology as the actual jet. -/
def hilbertJetEquiv : HilbertJet ≃L[ℂ] Jet :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ Field HilbertJetTriple).trans
    ((ContinuousLinearEquiv.refl ℂ Field).prodCongr
      ((WithLp.prodContinuousLinearEquiv 2 ℂ Field HilbertJetPair).trans
        ((ContinuousLinearEquiv.refl ℂ Field).prodCongr
          (WithLp.prodContinuousLinearEquiv 2 ℂ Field Field))))

/-- The actual weak PDE constraints pulled back to the Hilbert product. -/
def hilbertJetSubmodule (U : Set ℂ) : Submodule ℂ HilbertJet :=
  (jetSubmodule U).comap hilbertJetEquiv.toLinearMap

theorem isClosed_hilbertJetSubmodule (U : Set ℂ) :
    IsClosed (hilbertJetSubmodule U : Set HilbertJet) :=
  (isClosed_jetSubmodule U).preimage hilbertJetEquiv.continuous

instance (U : Set ℂ) : CompleteSpace (hilbertJetSubmodule U) :=
  (isClosed_hilbertJetSubmodule U).isComplete.completeSpace_coe

/-- Transport of a constrained Hilbert jet back to the original normed subtype. -/
def hilbertJetToJetSpace (U : Set ℂ) : hilbertJetSubmodule U →L[ℂ] JetSpace U :=
  (hilbertJetEquiv.toContinuousLinearMap.comp (hilbertJetSubmodule U).subtypeL).codRestrict
    (jetSubmodule U) (fun j => j.property)

/-- A bounded projection onto the complete space of actual local Poisson jets. -/
def jetProjection (U : Set ℂ) : Jet →L[ℂ] JetSpace U :=
  (hilbertJetToJetSpace U).comp
    ((hilbertJetSubmodule U).orthogonalProjectionOnto.comp
      hilbertJetEquiv.symm.toContinuousLinearMap)

@[simp] theorem jetProjection_subtype (U : Set ℂ) (j : JetSpace U) :
    jetProjection U j = j := by
  let v : hilbertJetSubmodule U := ⟨hilbertJetEquiv.symm j, by
    change hilbertJetEquiv (hilbertJetEquiv.symm j.val) ∈ jetSubmodule U
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using j.property⟩
  change hilbertJetToJetSpace U ((hilbertJetSubmodule U).orthogonalProjectionOnto v) = j
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  apply Subtype.ext
  exact hilbertJetEquiv.apply_symm_apply j.val

theorem jetProjection_eq_of_mem (U : Set ℂ) {j : Jet} (hj : j ∈ jetSubmodule U) :
    jetProjection U j = ⟨j, hj⟩ :=
  jetProjection_subtype U ⟨j, hj⟩

@[simp] theorem jetProjection_comp_subtype (U : Set ℂ) :
    (jetProjection U).comp (jetSubmodule U).subtypeL =
      ContinuousLinearMap.id ℂ (JetSpace U) := by
  apply ContinuousLinearMap.ext
  intro j
  exact jetProjection_subtype U j

theorem jetProjection_analyticAt (U : Set ℂ) {f : ℂ → Jet} {z : ℂ}
    (hf : AnalyticAt ℂ f z) : AnalyticAt ℂ (fun w => jetProjection U (f w)) z :=
  ((jetProjection U).analyticAt _).comp hf

section Operator
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Bounded postcomposition packages whole source operators, in operator norm. -/
def jetOperator (U : Set ℂ) : (E →L[ℂ] Jet) →L[ℂ] (E →L[ℂ] JetSpace U) :=
  ContinuousLinearMap.compL ℂ E Jet (JetSpace U) (jetProjection U)

@[simp] theorem jetOperator_apply (U : Set ℂ) (A : E →L[ℂ] Jet) (x : E) :
    jetOperator E U A x = jetProjection U (A x) := rfl

theorem jetOperator_subtype_of_mem (U : Set ℂ) (A : E →L[ℂ] Jet)
    (hA : ∀ x, A x ∈ jetSubmodule U) :
    (jetSubmodule U).subtypeL.comp (jetOperator E U A) = A := by
  apply ContinuousLinearMap.ext
  intro x
  change (jetProjection U (A x)).val = A x
  rw [jetProjection_eq_of_mem U (hA x)]

theorem jetOperator_analyticAt (U : Set ℂ) {A : ℂ → E →L[ℂ] Jet} {z : ℂ}
    (hA : AnalyticAt ℂ A z) :
    AnalyticAt ℂ (fun w => jetOperator E U (A w)) z := by
  have hP := ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := E →L[ℂ] Jet) (F := E →L[ℂ] JetSpace U) (jetOperator E U) (A z)
  exact hP.comp_of_eq hA rfl

theorem jetOperator_analyticOnNhd (U V : Set ℂ) {A : ℂ → E →L[ℂ] Jet}
    (hA : AnalyticOnNhd ℂ A V) :
    AnalyticOnNhd ℂ (fun w => jetOperator E U (A w)) V :=
  fun z hz => jetOperator_analyticAt E U (hA z hz)

end Operator
end GapFamily.Analytic.LocalPoisson
