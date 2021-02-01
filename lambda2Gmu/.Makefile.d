CanonicalForms.vo CanonicalForms.glob CanonicalForms.v.beautified CanonicalForms.required_vo: CanonicalForms.v Definitions.vo Infrastructure.vo Equations.vo
CanonicalForms.vio: CanonicalForms.v Definitions.vio Infrastructure.vio Equations.vio
CanonicalForms.vos CanonicalForms.vok CanonicalForms.required_vos: CanonicalForms.v Definitions.vos Infrastructure.vos Equations.vos
DefinitionsTests.vo DefinitionsTests.glob DefinitionsTests.v.beautified DefinitionsTests.required_vo: DefinitionsTests.v Definitions.vo
DefinitionsTests.vio: DefinitionsTests.v Definitions.vio
DefinitionsTests.vos DefinitionsTests.vok DefinitionsTests.required_vos: DefinitionsTests.v Definitions.vos
Definitions.vo Definitions.glob Definitions.v.beautified Definitions.required_vo: Definitions.v Zip.vo
Definitions.vio: Definitions.v Zip.vio
Definitions.vos Definitions.vok Definitions.required_vos: Definitions.v Zip.vos
Equations.vo Equations.glob Equations.v.beautified Equations.required_vo: Equations.v Prelude.vo Infrastructure.vo
Equations.vio: Equations.v Prelude.vio Infrastructure.vio
Equations.vos Equations.vok Equations.required_vos: Equations.v Prelude.vos Infrastructure.vos
InfrastructureFV.vo InfrastructureFV.glob InfrastructureFV.v.beautified InfrastructureFV.required_vo: InfrastructureFV.v Prelude.vo
InfrastructureFV.vio: InfrastructureFV.v Prelude.vio
InfrastructureFV.vos InfrastructureFV.vok InfrastructureFV.required_vos: InfrastructureFV.v Prelude.vos
InfrastructureOpen.vo InfrastructureOpen.glob InfrastructureOpen.v.beautified InfrastructureOpen.required_vo: InfrastructureOpen.v Prelude.vo InfrastructureFV.vo
InfrastructureOpen.vio: InfrastructureOpen.v Prelude.vio InfrastructureFV.vio
InfrastructureOpen.vos InfrastructureOpen.vok InfrastructureOpen.required_vos: InfrastructureOpen.v Prelude.vos InfrastructureFV.vos
InfrastructureSubst.vo InfrastructureSubst.glob InfrastructureSubst.v.beautified InfrastructureSubst.required_vo: InfrastructureSubst.v Prelude.vo InfrastructureFV.vo InfrastructureOpen.vo
InfrastructureSubst.vio: InfrastructureSubst.v Prelude.vio InfrastructureFV.vio InfrastructureOpen.vio
InfrastructureSubst.vos InfrastructureSubst.vok InfrastructureSubst.required_vos: InfrastructureSubst.v Prelude.vos InfrastructureFV.vos InfrastructureOpen.vos
Infrastructure.vo Infrastructure.glob Infrastructure.v.beautified Infrastructure.required_vo: Infrastructure.v InfrastructureFV.vo InfrastructureOpen.vo InfrastructureSubst.vo
Infrastructure.vio: Infrastructure.v InfrastructureFV.vio InfrastructureOpen.vio InfrastructureSubst.vio
Infrastructure.vos Infrastructure.vok Infrastructure.required_vos: Infrastructure.v InfrastructureFV.vos InfrastructureOpen.vos InfrastructureSubst.vos
Prelude.vo Prelude.glob Prelude.v.beautified Prelude.required_vo: Prelude.v Zip.vo Definitions.vo
Prelude.vio: Prelude.v Zip.vio Definitions.vio
Prelude.vos Prelude.vok Prelude.required_vos: Prelude.v Zip.vos Definitions.vos
Preservation.vo Preservation.glob Preservation.v.beautified Preservation.required_vo: Preservation.v Prelude.vo Infrastructure.vo Regularity.vo
Preservation.vio: Preservation.v Prelude.vio Infrastructure.vio Regularity.vio
Preservation.vos Preservation.vok Preservation.required_vos: Preservation.v Prelude.vos Infrastructure.vos Regularity.vos
Progress.vo Progress.glob Progress.v.beautified Progress.required_vo: Progress.v Prelude.vo Infrastructure.vo Regularity.vo CanonicalForms.vo
Progress.vio: Progress.v Prelude.vio Infrastructure.vio Regularity.vio CanonicalForms.vio
Progress.vos Progress.vok Progress.required_vos: Progress.v Prelude.vos Infrastructure.vos Regularity.vos CanonicalForms.vos
Regularity.vo Regularity.glob Regularity.v.beautified Regularity.required_vo: Regularity.v Prelude.vo Infrastructure.vo
Regularity.vio: Regularity.v Prelude.vio Infrastructure.vio
Regularity.vos Regularity.vok Regularity.required_vos: Regularity.v Prelude.vos Infrastructure.vos
TestCommon.vo TestCommon.glob TestCommon.v.beautified TestCommon.required_vo: TestCommon.v Prelude.vo Infrastructure.vo
TestCommon.vio: TestCommon.v Prelude.vio Infrastructure.vio
TestCommon.vos TestCommon.vok TestCommon.required_vos: TestCommon.v Prelude.vos Infrastructure.vos
TestList.vo TestList.glob TestList.v.beautified TestList.required_vo: TestList.v Definitions.vo
TestList.vio: TestList.v Definitions.vio
TestList.vos TestList.vok TestList.required_vos: TestList.v Definitions.vos
Tests2.vo Tests2.glob Tests2.v.beautified Tests2.required_vo: Tests2.v TestCommon.vo
Tests2.vio: Tests2.v TestCommon.vio
Tests2.vos Tests2.vok Tests2.required_vos: Tests2.v TestCommon.vos
Tests.vo Tests.glob Tests.v.beautified Tests.required_vo: Tests.v TestCommon.vo Regularity.vo
Tests.vio: Tests.v TestCommon.vio Regularity.vio
Tests.vos Tests.vok Tests.required_vos: Tests.v TestCommon.vos Regularity.vos
TestVector.vo TestVector.glob TestVector.v.beautified TestVector.required_vo: TestVector.v TestCommon.vo
TestVector.vio: TestVector.v TestCommon.vio
TestVector.vos TestVector.vok TestVector.required_vos: TestVector.v TestCommon.vos
Zip.vo Zip.glob Zip.v.beautified Zip.required_vo: Zip.v 
Zip.vio: Zip.v 
Zip.vos Zip.vok Zip.required_vos: Zip.v 
