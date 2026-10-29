import KOS

/-! Prints the axioms used by the main theorems. Run from `lean/`:
`lake env lean scripts/CheckAxioms.lean`
Every line should read `[propext, Classical.choice, Quot.sound]`. -/

#print axioms KOS.AncestralConfigurations.disanto_rosenberg
#print axioms KOS.AncestralConfigurations.disanto_rosenberg_unique
#print axioms KOS.AncestralConfigurations.disanto_rosenberg_minimum
#print axioms KOS.AncestralConfigurations.disanto_rosenberg_paper
#print axioms KOS.AncestralConfigurations.paperRootConfigsNonequiv_eq_rootConfigs
#print axioms KOS.AncestralConfigurations.disanto_rosenberg_realizations
#print axioms KOS.AncestralConfigurations.realizationConfigs_eq_configsAt
#print axioms KOS.AncestralConfigurationsIndependent.disanto_rosenberg
#print axioms KOS.AncestralConfigurationsIndependent.disanto_rosenberg_unique
#print axioms KOS.AncestralConfigurationsIndependent.disanto_rosenberg_unique_shape
#print axioms KOS.AncestralConfigurationsIndependent.disanto_rosenberg_min
#print axioms OeisA100475.not_conjecture
#print axioms DickeyRosenberg.conjecture14i
#print axioms DickeyRosenberg.conjecture14ii
#print axioms DickeyRosenberg.ustar_iso_canonical
#print axioms DickeyRosenberg.conjecture14i_paper
#print axioms DickeyRosenberg.conjecture14ii_paper
#print axioms Forcing.problem55
#print axioms CosetB.conjecture25_false
#print axioms CosetB.counterexample_q4_m12
#print axioms DedePopat.not_conjecture1
#print axioms DedePopat.not_conjecture1NonEquienergetic
#print axioms DedePopat.rook_clebschCompl_counterexample
#print axioms DedePopat.order10_counterexample
#print axioms DedePopat.not_conjecture1_order10
#print axioms DedePopat.not_corollary2
#print axioms DepthVariance.explicit_counterexample
#print axioms DepthVariance.minimum_variance_depth_unique_false
#print axioms CosetA.conjecturesA
