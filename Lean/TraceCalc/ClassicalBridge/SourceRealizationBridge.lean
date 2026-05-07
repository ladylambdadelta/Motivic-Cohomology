import TraceCalc.ClassicalBridge.ClassicalBridgeAnchors
import TraceCalc.LayerB.RealObjects.SourceHolographyToLayerD

universe u v w x y z

namespace TraceCalc
namespace ClassicalBridge

open CategoryTheory
open LayerB.RealObjects
open LayerB.RealObjects.RewriteCalculusSetup
open LayerB.RealObjects.RewriteCalculusSetup.FoundationsBoundaryBridgeAuxiliaryData

/-- The Layer D source package exported by a Layer B source export datum. -/
abbrev sourceTracePackageFromExport
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux) :
    LayerD.SourceTracePackage :=
  layerBSourceExportData_to_SourceTracePackage sourceExport

/-- The Layer D source-construction witness exported by a Layer B source export datum. -/
abbrev sourceConstructionWitnessFromExport
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux) :
    LayerD.SourceTracePackage.SourceConstructionWitness
      (sourceTracePackageFromExport sourceExport) :=
  layerBSourceExportData_to_SourceConstructionWitness sourceExport

/-- The realized `SourceConstructionReady` milestone exported by a Layer B source export datum. -/
def sourceConstructionReadyFromExport
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux) :
    LayerD.MilestoneRealization LayerD.SourceConstructionReady :=
  LayerD.sourceTracePackage_gives_sourceConstructionReady
    (sourceTracePackageFromExport sourceExport)
    (sourceConstructionWitnessFromExport sourceExport)

/-- Concrete localization-compatibility data for the source-realization bridge. -/
structure ReconstructionRespectsLocalizationData
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (classicalPresentation : ClassicalMotivicPresentation.{u, v, w, x, y})
    (localizedRealizationFunctor :
      ClassicalFunctor
        (sourceTracePackageFromExport sourceExport).Localized
        classicalPresentation.LocalizedCategory) where
  sourceLocalizationExports :
      (sourceTracePackageFromExport sourceExport).localizationInterface.C =
          (sourceTracePackageFromExport sourceExport).Envelope ∧
        (sourceTracePackageFromExport sourceExport).localizationInterface.D =
          (sourceTracePackageFromExport sourceExport).Localized
  sourceLocalizationCompatibility :
      (sourceTracePackageFromExport sourceExport).LocalizationCompatibilityType
  localizedFunctorPreservesId :
    ∀ X,
      localizedRealizationFunctor.map (𝟙 X) =
        𝟙 (localizedRealizationFunctor.obj X)
  localizedFunctorPreservesComp :
    ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z),
      localizedRealizationFunctor.map (f ≫ g) =
        localizedRealizationFunctor.map f ≫ localizedRealizationFunctor.map g

/-- Concrete presentation-feed data for the source-realization bridge. -/
structure SourceConstructionFeedsPresentationData
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (classicalPresentation : ClassicalMotivicPresentation.{u, v, w, x, y})
    (syntaxTransport :
      (sourceTracePackageFromExport sourceExport).Syntax →
        classicalPresentation.Syntax)
    (localizedRealizationFunctor :
      ClassicalFunctor
        (sourceTracePackageFromExport sourceExport).Localized
        classicalPresentation.LocalizedCategory) where
  syntaxLocalizationCompatibility :
    ∀ s,
      localizedRealizationFunctor.obj
        ((sourceTracePackageFromExport sourceExport).localizeObj
          ((sourceTracePackageFromExport sourceExport).includeSyntax s)) =
      classicalPresentation.localization.localizationFunctor.obj
        (classicalPresentation.includeSyntax (syntaxTransport s))
  sourceWitnessReadiness :
    (sourceConstructionWitnessFromExport sourceExport).readinessData
  sourceReadyStage :
    (sourceConstructionReadyFromExport sourceExport).stageName =
      LayerD.SourceConstructionReady.stageName
  classicalGeometricShapeAxioms : classicalPresentation.geometricShapeAxioms

/-- Exact bridge-local comparison datum still required to feed the source
construction package into a classical motivic presentation.

The lower `SourceTracePackage` exports only the trace-native source syntax map
`includeSyntax : Syntax -> Envelope` and the trace-native localization object map
`localizeObj : Envelope -> Localized`. It does not export any map into
`classicalPresentation.Syntax`, nor any theorem identifying the resulting
localized source object with the classical presentation's localized syntax image.
So the remaining missing datum is exactly the family of equalities comparing

`localizedRealizationFunctor.obj (localizeObj (includeSyntax s))`

against

`classicalPresentation.localization.localizationFunctor.obj
  (classicalPresentation.includeSyntax (syntaxTransport s))`.

This is irreducibly comparison data between the trace-native syntax lane and
the classical presentation's localization syntax lane, so it belongs at the
bridge boundary rather than in Layer B or Layer D. -/
abbrev SourceConstructionSyntaxLocalizationComparison
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (classicalPresentation : ClassicalMotivicPresentation.{u, v, w, x, y})
    (syntaxTransport :
      (sourceTracePackageFromExport sourceExport).Syntax →
        classicalPresentation.Syntax)
    (localizedRealizationFunctor :
      ClassicalFunctor
        (sourceTracePackageFromExport sourceExport).Localized
        classicalPresentation.LocalizedCategory) : Prop :=
  ∀ s,
    localizedRealizationFunctor.obj
      ((sourceTracePackageFromExport sourceExport).localizeObj
        ((sourceTracePackageFromExport sourceExport).includeSyntax s)) =
    classicalPresentation.localization.localizationFunctor.obj
      (classicalPresentation.includeSyntax (syntaxTransport s))

/-- The remaining bridge-local ingredients needed to build
`SourceConstructionFeedsPresentationData`. The readiness and stage fields are
exported by the lower source package. The syntax compatibility law is still
bridge-local, and the classical geometric-shape proof remains external because
`ClassicalMotivicPresentation` currently exposes only the proposition
`geometricShapeAxioms : Prop`, not a proof term. -/
structure SourceConstructionSyntaxCompatibilityData
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (classicalPresentation : ClassicalMotivicPresentation.{u, v, w, x, y})
    (syntaxTransport :
      (sourceTracePackageFromExport sourceExport).Syntax →
        classicalPresentation.Syntax)
    (localizedRealizationFunctor :
      ClassicalFunctor
        (sourceTracePackageFromExport sourceExport).Localized
        classicalPresentation.LocalizedCategory) where
  syntaxLocalizationCompatibility :
    SourceConstructionSyntaxLocalizationComparison
      sourceExport classicalPresentation syntaxTransport localizedRealizationFunctor
  classicalGeometricShapeAxioms : classicalPresentation.geometricShapeAxioms

namespace ReconstructionRespectsLocalizationData

/-- The theorem-target proposition extracted from localization-compatibility data. -/
def toTarget
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {sourceExport : LayerBSourceExportData presentation aux}
    {classicalPresentation : ClassicalMotivicPresentation.{u, v, w, x, y}}
    {localizedRealizationFunctor :
      ClassicalFunctor
        (sourceTracePackageFromExport sourceExport).Localized
        classicalPresentation.LocalizedCategory}
    (data :
      ReconstructionRespectsLocalizationData
        sourceExport classicalPresentation localizedRealizationFunctor) : Prop :=
  ((sourceTracePackageFromExport sourceExport).localizationInterface.C =
      (sourceTracePackageFromExport sourceExport).Envelope ∧
    (sourceTracePackageFromExport sourceExport).localizationInterface.D =
      (sourceTracePackageFromExport sourceExport).Localized) ∧
    HEq (sourceTracePackageFromExport sourceExport).localizationInterface.W
      (sourceTracePackageFromExport sourceExport).weakEquivalence ∧
    HEq (sourceTracePackageFromExport sourceExport).localizationInterface.QObj
      (sourceTracePackageFromExport sourceExport).localizeObj ∧
    (∀ X : (sourceTracePackageFromExport sourceExport).localizationInterface.C,
      (sourceTracePackageFromExport sourceExport).localizationInterface.QMap (𝟙 X) =
        𝟙 ((sourceTracePackageFromExport sourceExport).localizationInterface.QObj X)) ∧
    (∀ {X Y Z : (sourceTracePackageFromExport sourceExport).localizationInterface.C}
        (f : X ⟶ Y) (g : Y ⟶ Z),
      (sourceTracePackageFromExport sourceExport).localizationInterface.QMap (f ≫ g) =
        (sourceTracePackageFromExport sourceExport).localizationInterface.QMap f ≫
          (sourceTracePackageFromExport sourceExport).localizationInterface.QMap g) ∧
    (∀ X,
      localizedRealizationFunctor.map (𝟙 X) =
        𝟙 (localizedRealizationFunctor.obj X)) ∧
    (∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z),
      localizedRealizationFunctor.map (f ≫ g) =
        localizedRealizationFunctor.map f ≫ localizedRealizationFunctor.map g)

theorem toTarget_holds
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {sourceExport : LayerBSourceExportData presentation aux}
    {classicalPresentation : ClassicalMotivicPresentation.{u, v, w, x, y}}
    {localizedRealizationFunctor :
      ClassicalFunctor
        (sourceTracePackageFromExport sourceExport).Localized
        classicalPresentation.LocalizedCategory}
    (data :
      ReconstructionRespectsLocalizationData
        sourceExport classicalPresentation localizedRealizationFunctor) :
    data.toTarget :=
  ⟨data.sourceLocalizationExports,
    data.sourceLocalizationCompatibility.weakEquivalenceAlignment,
    data.sourceLocalizationCompatibility.localizeObjAlignment,
    data.sourceLocalizationCompatibility.localizationMapId,
    data.sourceLocalizationCompatibility.localizationMapComp,
    data.localizedFunctorPreservesId,
    data.localizedFunctorPreservesComp⟩

/-- Build the bridge localization-compatibility record directly from the Layer D
source package exported by the Layer B source data, together with the actual
functoriality laws of the localized realization functor. -/
def ofSourceTracePackage
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (classicalPresentation : ClassicalMotivicPresentation.{u, v, w, x, y})
    (localizedRealizationFunctor :
      ClassicalFunctor
        (sourceTracePackageFromExport sourceExport).Localized
        classicalPresentation.LocalizedCategory) :
    ReconstructionRespectsLocalizationData
      sourceExport classicalPresentation localizedRealizationFunctor where
  sourceLocalizationExports :=
    (sourceTracePackageFromExport sourceExport).localization_interface_exports
  sourceLocalizationCompatibility :=
    (sourceTracePackageFromExport sourceExport).localizationCompatibilityData
  localizedFunctorPreservesId := by
    intro X
    simpa using localizedRealizationFunctor.map_id X
  localizedFunctorPreservesComp := by
    intro X Y Z f g
    simpa using localizedRealizationFunctor.map_comp f g

end ReconstructionRespectsLocalizationData

namespace SourceConstructionFeedsPresentationData

/-- Build the full source-to-presentation feed package from the lower source
construction data and the remaining bridge-local presentation compatibility
record. -/
def ofSourceTracePackage
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (classicalPresentation : ClassicalMotivicPresentation.{u, v, w, x, y})
    (syntaxTransport :
      (sourceTracePackageFromExport sourceExport).Syntax →
        classicalPresentation.Syntax)
    (localizedRealizationFunctor :
      ClassicalFunctor
        (sourceTracePackageFromExport sourceExport).Localized
        classicalPresentation.LocalizedCategory)
    (syntaxData :
      SourceConstructionSyntaxCompatibilityData
        sourceExport classicalPresentation syntaxTransport localizedRealizationFunctor) :
    SourceConstructionFeedsPresentationData
      sourceExport classicalPresentation syntaxTransport localizedRealizationFunctor where
  syntaxLocalizationCompatibility := syntaxData.syntaxLocalizationCompatibility
  sourceWitnessReadiness :=
    LayerD.SourceTracePackage.SourceConstructionWitness.readinessData_of_fields
      (sourceConstructionWitnessFromExport sourceExport)
  sourceReadyStage :=
    LayerD.MilestoneRealization.stageName_eq
      (sourceConstructionReadyFromExport sourceExport)
  classicalGeometricShapeAxioms := syntaxData.classicalGeometricShapeAxioms

/-- The theorem-target proposition extracted from presentation-feed data. -/
def toTarget
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {sourceExport : LayerBSourceExportData presentation aux}
    {classicalPresentation : ClassicalMotivicPresentation.{u, v, w, x, y}}
    {syntaxTransport :
      (sourceTracePackageFromExport sourceExport).Syntax →
        classicalPresentation.Syntax}
    {localizedRealizationFunctor :
      ClassicalFunctor
        (sourceTracePackageFromExport sourceExport).Localized
        classicalPresentation.LocalizedCategory}
    (data :
      SourceConstructionFeedsPresentationData
        sourceExport classicalPresentation syntaxTransport localizedRealizationFunctor) : Prop :=
  SourceConstructionSyntaxLocalizationComparison
      sourceExport classicalPresentation syntaxTransport localizedRealizationFunctor ∧
    (sourceConstructionWitnessFromExport sourceExport).readinessData ∧
    (sourceConstructionReadyFromExport sourceExport).stageName =
      LayerD.SourceConstructionReady.stageName ∧
    classicalPresentation.geometricShapeAxioms

theorem toTarget_holds
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {sourceExport : LayerBSourceExportData presentation aux}
    {classicalPresentation : ClassicalMotivicPresentation.{u, v, w, x, y}}
    {syntaxTransport :
      (sourceTracePackageFromExport sourceExport).Syntax →
        classicalPresentation.Syntax}
    {localizedRealizationFunctor :
      ClassicalFunctor
        (sourceTracePackageFromExport sourceExport).Localized
        classicalPresentation.LocalizedCategory}
    (data :
      SourceConstructionFeedsPresentationData
        sourceExport classicalPresentation syntaxTransport localizedRealizationFunctor) :
    data.toTarget :=
  ⟨data.syntaxLocalizationCompatibility,
    data.sourceWitnessReadiness,
    data.sourceReadyStage,
    data.classicalGeometricShapeAxioms⟩

end SourceConstructionFeedsPresentationData

/-- Middleware contract describing how the existing Layer B source export and its already-proved
`SourceConstructionReady` milestone should feed a classical source-presentation slot. The source
presentation remains bridge-local adapter data because the ClassicalPeriods target lane begins at
structured comparison and period-faithfulness objects. -/
structure SourceRealizesClassicalMotivePresentation
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine) where
  sourceExport : LayerBSourceExportData presentation aux
  classicalPresentation : ClassicalMotivicPresentation.{u, v, w, x, y}
  ReconstructionTransport : Type z
  reconstructionTransport : ReconstructionTransport
  syntaxTransport :
    (layerBSourceExportData_to_SourceTracePackage sourceExport).Syntax →
      classicalPresentation.Syntax
  localizedRealizationFunctor :
    ClassicalFunctor
      (layerBSourceExportData_to_SourceTracePackage sourceExport).Localized
      classicalPresentation.LocalizedCategory
  sourceConstructionWitness :
    LayerD.SourceTracePackage.SourceConstructionWitness
      (layerBSourceExportData_to_SourceTracePackage sourceExport)
  sourceConstructionReady : LayerD.MilestoneRealization LayerD.SourceConstructionReady
  reconstructionRespectsLocalization :
    ReconstructionRespectsLocalizationData
      sourceExport classicalPresentation localizedRealizationFunctor
  sourceConstructionFeedsPresentation :
    SourceConstructionFeedsPresentationData
      sourceExport classicalPresentation syntaxTransport localizedRealizationFunctor

namespace SourceRealizesClassicalMotivePresentation

/-- The internal Layer D source package exposed by the Layer B export carried in the bridge. -/
def sourceTracePackage
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : SourceRealizesClassicalMotivePresentation presentation aux) :
    LayerD.SourceTracePackage :=
  layerBSourceExportData_to_SourceTracePackage bridge.sourceExport

/-- Canonical constructor from the existing Layer B export seam. This computes the already
available Layer D witness and milestone realization, leaving only the classical-facing claims as
open obligations. -/
def ofLayerBSourceExportData
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (classicalPresentation : ClassicalMotivicPresentation.{u, v, w, x, y})
    (ReconstructionTransport : Type z)
    (reconstructionTransport : ReconstructionTransport)
    (syntaxTransport :
      (layerBSourceExportData_to_SourceTracePackage sourceExport).Syntax →
        classicalPresentation.Syntax)
    (localizedRealizationFunctor :
      ClassicalFunctor
        (layerBSourceExportData_to_SourceTracePackage sourceExport).Localized
        classicalPresentation.LocalizedCategory)
    (sourceConstructionSyntaxCompatibility :
      SourceConstructionSyntaxCompatibilityData
        sourceExport classicalPresentation syntaxTransport localizedRealizationFunctor) :
    SourceRealizesClassicalMotivePresentation presentation aux where
  sourceExport := sourceExport
  classicalPresentation := classicalPresentation
  ReconstructionTransport := ReconstructionTransport
  reconstructionTransport := reconstructionTransport
  syntaxTransport := syntaxTransport
  localizedRealizationFunctor := localizedRealizationFunctor
  sourceConstructionWitness :=
    layerBSourceExportData_to_SourceConstructionWitness sourceExport
  sourceConstructionReady :=
    LayerD.sourceTracePackage_gives_sourceConstructionReady
      (layerBSourceExportData_to_SourceTracePackage sourceExport)
      (layerBSourceExportData_to_SourceConstructionWitness sourceExport)
  reconstructionRespectsLocalization :=
    ReconstructionRespectsLocalizationData.ofSourceTracePackage
      sourceExport classicalPresentation localizedRealizationFunctor
  sourceConstructionFeedsPresentation :=
    SourceConstructionFeedsPresentationData.ofSourceTracePackage
      sourceExport classicalPresentation syntaxTransport localizedRealizationFunctor
      sourceConstructionSyntaxCompatibility

end SourceRealizesClassicalMotivePresentation

end ClassicalBridge
end TraceCalc