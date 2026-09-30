import GapFamily.GapFamily

/-! Readable statement and axiom audit for the complete two-family theorem.
The definitions display the full quantifiers; the checks identify the closed
proofs, and the axiom audit includes the actual construction. -/

#print GapFamily.ProportionalGapFamilyExists
#print GapFamily.FixedGapFamilyExists
#print GapFamily.HasUnitScalarGap
#print GapFamily.RealizesGap
#print GapFamily.firstShiftedEnergy
#check GapFamily.proportionalGapFamilyExists
#check GapFamily.fixedGapFamilyExists
#print axioms GapFamily.gap_families
#print axioms GapFamily.nodeSpectrum_hasUnitScalarGap
#print axioms GapFamily.proportionalGapFamilyExists_of_eventually_realizesGap
#print axioms GapFamily.fixedGapFamilyExists_of_eventually_realizesGap
#print axioms GapFamily.finite_primaryBelow_iff
#print axioms GapFamily.thermal_summable_iff
#print axioms GapFamily.summable_primary_copy_iff
