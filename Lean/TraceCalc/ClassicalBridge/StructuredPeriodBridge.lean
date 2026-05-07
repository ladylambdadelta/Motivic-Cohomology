import TraceCalc.ClassicalBridge.ClassicalBridgeAnchors
import TraceCalc.LayerF.RealizationPackage

universe u v w x y z

namespace TraceCalc
namespace ClassicalBridge

/-- Middleware contract describing how the existing structured/scalar theorem package should feed
the real ClassicalPeriods morphism-level structured comparison surface. The comparison data stays
proof-relevant; the realization and reflection claims stay propositional. -/
structure StructuredPackageRealizesClassicalComparison where
  theoremPackage : LayerF.StructuredScalarTheoremPackage.{u, v, w, x, y, z}
  comparisonContext : ClassicalComparisonContext
  packedComparison : SomeStructuredComparisonMorphism comparisonContext
  BasisFreePeriodMapTransportData : Type z
  basisFreePeriodMapTransportData : BasisFreePeriodMapTransportData
  structuredComparisonEquality : StructuredComparisonEquality comparisonContext
  scalarShadow : ScalarPeriodShadow (SomeStructuredComparisonMorphism comparisonContext)
  scalarShadowEquality :
    ScalarShadowEquality (SomeStructuredComparisonMorphism comparisonContext) scalarShadow
  ScalarExtractionTransportData : Type z
  scalarExtractionTransportData : ScalarExtractionTransportData
  structuredPackage : LayerD.StructuredRealizationPackage
  structuredReady : LayerD.MilestoneRealization LayerD.StructuredRealizationBridgeReady
  basisFreePeriodMapRealization : Prop
  scalarShadowExtractionRealization : Prop
  scalarEqualityReflectsStructuredComparison : Prop

namespace StructuredPackageRealizesClassicalComparison

def sourceComparison
    (bridge : StructuredPackageRealizesClassicalComparison.{u, v, w, x, y, z}) :
    ClassicalStructuredComparisonObject bridge.comparisonContext :=
  bridge.packedComparison.sourceObject

def targetComparison
    (bridge : StructuredPackageRealizesClassicalComparison.{u, v, w, x, y, z}) :
    ClassicalStructuredComparisonObject bridge.comparisonContext :=
  bridge.packedComparison.targetObject

def morphismComparison
    (bridge : StructuredPackageRealizesClassicalComparison.{u, v, w, x, y, z}) :
    ClassicalStructuredComparisonMorphism
      bridge.comparisonContext
      bridge.sourceComparison
      bridge.targetComparison :=
  bridge.packedComparison.morphismDatum

def packedMorphismComparison
    (bridge : StructuredPackageRealizesClassicalComparison.{u, v, w, x, y, z}) :
    SomeStructuredComparisonMorphism bridge.comparisonContext :=
  bridge.packedComparison

def basisFreePeriodMap
    (bridge : StructuredPackageRealizesClassicalComparison.{u, v, w, x, y, z}) :=
  bridge.packedComparison.basisFreePeriodMap

/-- Canonical constructor from the already-bundled structured/scalar theorem package. -/
def ofStructuredScalarTheoremPackage
    (theoremPackage : LayerF.StructuredScalarTheoremPackage.{u, v, w, x, y, z})
    (comparisonContext : ClassicalComparisonContext)
    (packedComparison : SomeStructuredComparisonMorphism comparisonContext)
    (BasisFreePeriodMapTransportData : Type z)
    (basisFreePeriodMapTransportData : BasisFreePeriodMapTransportData)
    (structuredComparisonEquality : StructuredComparisonEquality comparisonContext)
    (scalarShadow : ScalarPeriodShadow (SomeStructuredComparisonMorphism comparisonContext))
    (scalarShadowEquality :
      ScalarShadowEquality (SomeStructuredComparisonMorphism comparisonContext) scalarShadow)
    (ScalarExtractionTransportData : Type z)
    (scalarExtractionTransportData : ScalarExtractionTransportData)
    (basisFreePeriodMapRealization : Prop)
    (scalarShadowExtractionRealization : Prop)
    (scalarEqualityReflectsStructuredComparison : Prop) :
    StructuredPackageRealizesClassicalComparison :=
  let structuredPackage := (LayerF.structuredScalarTheoremPackage_to_packages theoremPackage).1
  { theoremPackage := theoremPackage
    comparisonContext := comparisonContext
    packedComparison := packedComparison
    BasisFreePeriodMapTransportData := BasisFreePeriodMapTransportData
    basisFreePeriodMapTransportData := basisFreePeriodMapTransportData
    structuredComparisonEquality := structuredComparisonEquality
    scalarShadow := scalarShadow
    scalarShadowEquality := scalarShadowEquality
    ScalarExtractionTransportData := ScalarExtractionTransportData
    scalarExtractionTransportData := scalarExtractionTransportData
    structuredPackage := structuredPackage
    structuredReady := structuredPackage.package_gives_structuredRealizationBridgeReady
    basisFreePeriodMapRealization := basisFreePeriodMapRealization
    scalarShadowExtractionRealization := scalarShadowExtractionRealization
    scalarEqualityReflectsStructuredComparison := scalarEqualityReflectsStructuredComparison }

/-- Constructor from the implementation-ticket subpackage view. This keeps the bridge neutral on
whether the upstream implementation is packaged as a single object or as the finer internal
tickets. -/
def ofStructuredScalarTheoremSubpackages
    (theoremSubpackages : LayerF.StructuredScalarTheoremSubpackages.{u, v, w, x, y})
    (comparisonContext : ClassicalComparisonContext)
  (packedComparison : SomeStructuredComparisonMorphism comparisonContext)
    (BasisFreePeriodMapTransportData : Type z)
    (basisFreePeriodMapTransportData : BasisFreePeriodMapTransportData)
    (structuredComparisonEquality : StructuredComparisonEquality comparisonContext)
    (scalarShadow : ScalarPeriodShadow (SomeStructuredComparisonMorphism comparisonContext))
    (scalarShadowEquality :
      ScalarShadowEquality (SomeStructuredComparisonMorphism comparisonContext) scalarShadow)
    (ScalarExtractionTransportData : Type z)
    (scalarExtractionTransportData : ScalarExtractionTransportData)
    (basisFreePeriodMapRealization : Prop)
    (scalarShadowExtractionRealization : Prop)
    (scalarEqualityReflectsStructuredComparison : Prop) :
    StructuredPackageRealizesClassicalComparison :=
  let theoremPackage := theoremSubpackages.toStructuredScalarTheoremPackage
  let structuredPackage := theoremSubpackages.toStructuredAndScalarPackages.1
  { theoremPackage := theoremPackage
    comparisonContext := comparisonContext
    packedComparison := packedComparison
    BasisFreePeriodMapTransportData := BasisFreePeriodMapTransportData
    basisFreePeriodMapTransportData := basisFreePeriodMapTransportData
    structuredComparisonEquality := structuredComparisonEquality
    scalarShadow := scalarShadow
    scalarShadowEquality := scalarShadowEquality
    ScalarExtractionTransportData := ScalarExtractionTransportData
    scalarExtractionTransportData := scalarExtractionTransportData
    structuredPackage := structuredPackage
    structuredReady := structuredPackage.package_gives_structuredRealizationBridgeReady
    basisFreePeriodMapRealization := basisFreePeriodMapRealization
    scalarShadowExtractionRealization := scalarShadowExtractionRealization
    scalarEqualityReflectsStructuredComparison := scalarEqualityReflectsStructuredComparison }

end StructuredPackageRealizesClassicalComparison

/-- Adapter from the internal structured/scalar theorem package and Layer D scalar package to the
real ClassicalPeriods framed-period data and scalar shadow. -/
structure StructuredScalarPackageRealizesFramedPeriods where
  comparisonBridge : StructuredPackageRealizesClassicalComparison.{u, v, w, x, y, z}
  pairingData :
    PeriodPairingData
      comparisonBridge.comparisonContext
      comparisonBridge.morphismComparison
  framedPeriodEquality : FramedPeriodEquality comparisonBridge.comparisonContext
  framedPeriodOperations : FramedPeriodOperations comparisonBridge.comparisonContext
  framedPeriodShadow : ScalarPeriodShadow (SomeFramedPeriodDatum comparisonBridge.comparisonContext)
  framedShadowEquality :
    ScalarShadowEquality (SomeFramedPeriodDatum comparisonBridge.comparisonContext)
      framedPeriodShadow
  FrameIndex : Type z
  framedPeriod :
    FrameIndex → FramedPeriodDatum comparisonBridge.comparisonContext pairingData
  FramedPeriodTransportData : Type z
  framedPeriodTransportData : FramedPeriodTransportData
  scalarPackage : LayerD.ScalarShadowExtractionPackage
  scalarShadowReady : LayerD.MilestoneRealization LayerD.ScalarShadowConsequenceReady
  framedPeriodDatumRealization : Prop
  scalarShadowExtractionRealization : Prop
  framedEqualityReflectsStructuredComparison : Prop

namespace StructuredScalarPackageRealizesFramedPeriods

def someFramedPeriodOf
    (bridge : StructuredScalarPackageRealizesFramedPeriods.{u, v, w, x, y, z})
    (frame : bridge.FrameIndex) :
    SomeFramedPeriodDatum bridge.comparisonBridge.comparisonContext :=
  ⟨bridge.comparisonBridge.sourceComparison,
    ⟨bridge.comparisonBridge.targetComparison,
      ⟨bridge.comparisonBridge.morphismComparison,
        ⟨bridge.pairingData, bridge.framedPeriod frame⟩⟩⟩⟩

def ofStructuredScalarTheoremPackage
    (theoremPackage : LayerF.StructuredScalarTheoremPackage.{u, v, w, x, y, z})
    (comparisonContext : ClassicalComparisonContext)
    (packedComparison : SomeStructuredComparisonMorphism comparisonContext)
    (BasisFreePeriodMapTransportData : Type z)
    (basisFreePeriodMapTransportData : BasisFreePeriodMapTransportData)
    (structuredComparisonEquality : StructuredComparisonEquality comparisonContext)
    (scalarShadow : ScalarPeriodShadow (SomeStructuredComparisonMorphism comparisonContext))
    (scalarShadowEquality :
      ScalarShadowEquality (SomeStructuredComparisonMorphism comparisonContext) scalarShadow)
    (ScalarExtractionTransportData : Type z)
    (scalarExtractionTransportData : ScalarExtractionTransportData)
    (basisFreePeriodMapRealization : Prop)
    (structuredScalarShadowExtractionRealization : Prop)
    (scalarEqualityReflectsStructuredComparison : Prop)
    (pairingData : PeriodPairingData comparisonContext packedComparison.morphismDatum)
    (framedPeriodEquality : FramedPeriodEquality comparisonContext)
    (framedPeriodOperations : FramedPeriodOperations comparisonContext)
    (framedPeriodShadow : ScalarPeriodShadow (SomeFramedPeriodDatum comparisonContext))
    (framedShadowEquality :
      ScalarShadowEquality (SomeFramedPeriodDatum comparisonContext) framedPeriodShadow)
    (FrameIndex : Type z)
    (framedPeriod : FrameIndex → FramedPeriodDatum comparisonContext pairingData)
    (FramedPeriodTransportData : Type z)
    (framedPeriodTransportData : FramedPeriodTransportData)
    (framedPeriodDatumRealization : Prop)
    (framedScalarShadowExtractionRealization : Prop)
    (framedEqualityReflectsStructuredComparison : Prop) :
    StructuredScalarPackageRealizesFramedPeriods :=
  let comparisonBridge :=
    StructuredPackageRealizesClassicalComparison.ofStructuredScalarTheoremPackage
      theoremPackage
      comparisonContext
      packedComparison
      BasisFreePeriodMapTransportData
      basisFreePeriodMapTransportData
      structuredComparisonEquality
      scalarShadow
      scalarShadowEquality
      ScalarExtractionTransportData
      scalarExtractionTransportData
      basisFreePeriodMapRealization
      structuredScalarShadowExtractionRealization
      scalarEqualityReflectsStructuredComparison
  let scalarPackage := (LayerF.structuredScalarTheoremPackage_to_packages theoremPackage).2
  { comparisonBridge := comparisonBridge
    pairingData := pairingData
    framedPeriodEquality := framedPeriodEquality
    framedPeriodOperations := framedPeriodOperations
    framedPeriodShadow := framedPeriodShadow
    framedShadowEquality := framedShadowEquality
    FrameIndex := FrameIndex
    framedPeriod := framedPeriod
    FramedPeriodTransportData := FramedPeriodTransportData
    framedPeriodTransportData := framedPeriodTransportData
    scalarPackage := scalarPackage
    scalarShadowReady := scalarPackage.package_gives_scalarShadowConsequenceReady
    framedPeriodDatumRealization := framedPeriodDatumRealization
    scalarShadowExtractionRealization := framedScalarShadowExtractionRealization
    framedEqualityReflectsStructuredComparison := framedEqualityReflectsStructuredComparison }

def ofStructuredScalarTheoremSubpackages
    (theoremSubpackages : LayerF.StructuredScalarTheoremSubpackages.{u, v, w, x, y})
    (comparisonContext : ClassicalComparisonContext)
  (packedComparison : SomeStructuredComparisonMorphism comparisonContext)
    (BasisFreePeriodMapTransportData : Type z)
    (basisFreePeriodMapTransportData : BasisFreePeriodMapTransportData)
    (structuredComparisonEquality : StructuredComparisonEquality comparisonContext)
    (scalarShadow : ScalarPeriodShadow (SomeStructuredComparisonMorphism comparisonContext))
    (scalarShadowEquality :
      ScalarShadowEquality (SomeStructuredComparisonMorphism comparisonContext) scalarShadow)
    (ScalarExtractionTransportData : Type z)
    (scalarExtractionTransportData : ScalarExtractionTransportData)
    (basisFreePeriodMapRealization : Prop)
    (structuredScalarShadowExtractionRealization : Prop)
    (scalarEqualityReflectsStructuredComparison : Prop)
    (pairingData : PeriodPairingData comparisonContext packedComparison.morphismDatum)
    (framedPeriodEquality : FramedPeriodEquality comparisonContext)
    (framedPeriodOperations : FramedPeriodOperations comparisonContext)
    (framedPeriodShadow : ScalarPeriodShadow (SomeFramedPeriodDatum comparisonContext))
    (framedShadowEquality :
      ScalarShadowEquality (SomeFramedPeriodDatum comparisonContext) framedPeriodShadow)
    (FrameIndex : Type z)
    (framedPeriod : FrameIndex → FramedPeriodDatum comparisonContext pairingData)
    (FramedPeriodTransportData : Type z)
    (framedPeriodTransportData : FramedPeriodTransportData)
    (framedPeriodDatumRealization : Prop)
    (framedScalarShadowExtractionRealization : Prop)
    (framedEqualityReflectsStructuredComparison : Prop) :
    StructuredScalarPackageRealizesFramedPeriods :=
  let comparisonBridge :=
    StructuredPackageRealizesClassicalComparison.ofStructuredScalarTheoremSubpackages
      theoremSubpackages
      comparisonContext
      packedComparison
      BasisFreePeriodMapTransportData
      basisFreePeriodMapTransportData
      structuredComparisonEquality
      scalarShadow
      scalarShadowEquality
      ScalarExtractionTransportData
      scalarExtractionTransportData
      basisFreePeriodMapRealization
      structuredScalarShadowExtractionRealization
      scalarEqualityReflectsStructuredComparison
  let scalarPackage := theoremSubpackages.toStructuredAndScalarPackages.2
  { comparisonBridge := comparisonBridge
    pairingData := pairingData
    framedPeriodEquality := framedPeriodEquality
    framedPeriodOperations := framedPeriodOperations
    framedPeriodShadow := framedPeriodShadow
    framedShadowEquality := framedShadowEquality
    FrameIndex := FrameIndex
    framedPeriod := framedPeriod
    FramedPeriodTransportData := FramedPeriodTransportData
    framedPeriodTransportData := framedPeriodTransportData
    scalarPackage := scalarPackage
    scalarShadowReady := scalarPackage.package_gives_scalarShadowConsequenceReady
    framedPeriodDatumRealization := framedPeriodDatumRealization
    scalarShadowExtractionRealization := framedScalarShadowExtractionRealization
    framedEqualityReflectsStructuredComparison := framedEqualityReflectsStructuredComparison }

end StructuredScalarPackageRealizesFramedPeriods

abbrev StructuredPeriodBridge := StructuredScalarPackageRealizesFramedPeriods

namespace StructuredPeriodBridge

abbrev ofStructuredScalarTheoremPackage :=
  StructuredScalarPackageRealizesFramedPeriods.ofStructuredScalarTheoremPackage
abbrev ofStructuredScalarTheoremSubpackages :=
  StructuredScalarPackageRealizesFramedPeriods.ofStructuredScalarTheoremSubpackages

end StructuredPeriodBridge

end ClassicalBridge
end TraceCalc