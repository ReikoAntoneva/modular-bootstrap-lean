import GapFamily.Construction.ProportionalSpectrum
import GapFamily.Construction.FixedGapSpectrum
import GapFamily.SpectralClass
import GapFamily.GapSpectrumConvention

/-!
# Theorem 2.2: the two exact gap families

`GapFamilyContract` gives the full definitions and quantifiers. The actual
cell construction, reference output, recursion and thermal limits are all
discharged by the imported proofs; this theorem has no analytic premises.
-/

namespace GapFamily

/-- The two parts of Theorem 2.2, for every sufficiently large real shift `a`.
Both conclusions include the unique scalar first primary with multiplicity
one, full admissibility of its character expansion, and the stated limits. -/
theorem gap_families : ProportionalGapFamilyExists ∧ FixedGapFamilyExists :=
  ⟨proportionalGapFamilyExists, fixedGapFamilyExists⟩

end GapFamily
