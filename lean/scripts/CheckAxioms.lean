import KOS

/-! Prints the axioms used by the main theorems. Run from `lean/`:
`lake env lean scripts/CheckAxioms.lean`
Every line should read `[propext, Classical.choice, Quot.sound]`. -/

#print axioms KOS.AncestralConfigurations.disanto_rosenberg
#print axioms KOS.AncestralConfigurations.disanto_rosenberg_unique
#print axioms KOS.AncestralConfigurations.disanto_rosenberg_minimum
#print axioms KOS.AncestralConfigurationsIndependent.disanto_rosenberg
#print axioms KOS.AncestralConfigurationsIndependent.disanto_rosenberg_unique
#print axioms KOS.AncestralConfigurationsIndependent.disanto_rosenberg_unique_shape
#print axioms KOS.AncestralConfigurationsIndependent.disanto_rosenberg_min
#print axioms OeisA100475.not_conjecture
