Predefs.vo Predefs.glob Predefs.v.beautified Predefs.required_vo: Predefs.v ../lambda2Gmu/Definitions.vo ../lambda2Gmu_annotated/Definitions.vo ../dependencies/extended-pdot-calculus/src/Definitions.vo ../dependencies/extended-pdot-calculus/src/Reduction.vo ../dependencies/extended-pdot-calculus/src/Sequences.vo
Predefs.vio: Predefs.v ../lambda2Gmu/Definitions.vio ../lambda2Gmu_annotated/Definitions.vio ../dependencies/extended-pdot-calculus/src/Definitions.vio ../dependencies/extended-pdot-calculus/src/Reduction.vio ../dependencies/extended-pdot-calculus/src/Sequences.vio
Predefs.vos Predefs.vok Predefs.required_vos: Predefs.v ../lambda2Gmu/Definitions.vos ../lambda2Gmu_annotated/Definitions.vos ../dependencies/extended-pdot-calculus/src/Definitions.vos ../dependencies/extended-pdot-calculus/src/Reduction.vos ../dependencies/extended-pdot-calculus/src/Sequences.vos
Helpers.vo Helpers.glob Helpers.v.beautified Helpers.required_vo: Helpers.v Predefs.vo ../lambda2Gmu/Prelude.vo ../dependencies/extended-pdot-calculus/src/Definitions.vo ../dependencies/extended-pdot-calculus/src/ExampleTactics.vo
Helpers.vio: Helpers.v Predefs.vio ../lambda2Gmu/Prelude.vio ../dependencies/extended-pdot-calculus/src/Definitions.vio ../dependencies/extended-pdot-calculus/src/ExampleTactics.vio
Helpers.vos Helpers.vok Helpers.required_vos: Helpers.v Predefs.vos ../lambda2Gmu/Prelude.vos ../dependencies/extended-pdot-calculus/src/Definitions.vos ../dependencies/extended-pdot-calculus/src/ExampleTactics.vos
Library.vo Library.glob Library.v.beautified Library.required_vo: Library.v Helpers.vo
Library.vio: Library.v Helpers.vio
Library.vos Library.vok Library.required_vos: Library.v Helpers.vos
TestHelpers.vo TestHelpers.glob TestHelpers.v.beautified TestHelpers.required_vo: TestHelpers.v Helpers.vo Library.vo
TestHelpers.vio: TestHelpers.v Helpers.vio Library.vio
TestHelpers.vos TestHelpers.vok TestHelpers.required_vos: TestHelpers.v Helpers.vos Library.vos
Translation.vo Translation.glob Translation.v.beautified Translation.required_vo: Translation.v Helpers.vo Library.vo
Translation.vio: Translation.v Helpers.vio Library.vio
Translation.vos Translation.vok Translation.required_vos: Translation.v Helpers.vos Library.vos
TestEqualityEnv.vo TestEqualityEnv.glob TestEqualityEnv.v.beautified TestEqualityEnv.required_vo: TestEqualityEnv.v Helpers.vo Library.vo TestHelpers.vo ../lambda2Gmu/TestEquality.vo Translation.vo
TestEqualityEnv.vio: TestEqualityEnv.v Helpers.vio Library.vio TestHelpers.vio ../lambda2Gmu/TestEquality.vio Translation.vio
TestEqualityEnv.vos TestEqualityEnv.vok TestEqualityEnv.required_vos: TestEqualityEnv.v Helpers.vos Library.vos TestHelpers.vos ../lambda2Gmu/TestEquality.vos Translation.vos
TestEquality.vo TestEquality.glob TestEquality.v.beautified TestEquality.required_vo: TestEquality.v Helpers.vo Library.vo TestHelpers.vo ../lambda2Gmu/TestEquality.vo Translation.vo TestEqualityEnv.vo
TestEquality.vio: TestEquality.v Helpers.vio Library.vio TestHelpers.vio ../lambda2Gmu/TestEquality.vio Translation.vio TestEqualityEnv.vio
TestEquality.vos TestEquality.vok TestEquality.required_vos: TestEquality.v Helpers.vos Library.vos TestHelpers.vos ../lambda2Gmu/TestEquality.vos Translation.vos TestEqualityEnv.vos
TestEquality2.vo TestEquality2.glob TestEquality2.v.beautified TestEquality2.required_vo: TestEquality2.v Helpers.vo Library.vo TestHelpers.vo ../lambda2Gmu/TestEquality.vo Translation.vo TestEqualityEnv.vo
TestEquality2.vio: TestEquality2.v Helpers.vio Library.vio TestHelpers.vio ../lambda2Gmu/TestEquality.vio Translation.vio TestEqualityEnv.vio
TestEquality2.vos TestEquality2.vok TestEquality2.required_vos: TestEquality2.v Helpers.vos Library.vos TestHelpers.vos ../lambda2Gmu/TestEquality.vos Translation.vos TestEqualityEnv.vos
TestEquality3.vo TestEquality3.glob TestEquality3.v.beautified TestEquality3.required_vo: TestEquality3.v Helpers.vo Library.vo TestHelpers.vo ../lambda2Gmu/TestEquality.vo Translation.vo TestEqualityEnv.vo
TestEquality3.vio: TestEquality3.v Helpers.vio Library.vio TestHelpers.vio ../lambda2Gmu/TestEquality.vio Translation.vio TestEqualityEnv.vio
TestEquality3.vos TestEquality3.vok TestEquality3.required_vos: TestEquality3.v Helpers.vos Library.vos TestHelpers.vos ../lambda2Gmu/TestEquality.vos Translation.vos TestEqualityEnv.vos
