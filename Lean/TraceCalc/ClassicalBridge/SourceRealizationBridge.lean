import TraceCalc.ClassicalBridge.ClassicalBridgeAnchors
import TraceCalc.LayerBNonCore.Bridges.SourceHolographyToLayerD

universe u1 v1 w1 x1 y1 z1

namespace TraceCalc
namespace ClassicalBridge

open CategoryTheory
open LayerB.RealObjects
open LayerB.RealObjects.RewriteCalculusSetup
open LayerB.RealObjects.RewriteCalculusSetup.FoundationsBoundaryBridgeAuxiliaryData

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
    (sourcePackage : LayerD.SourceTracePackage)
    (classicalPresentation : ClassicalMotivicPresentation.{u1, v1, w1, x1, y1})
    (syntaxTransport : sourcePackage.Syntax → classicalPresentation.Syntax)
    (localizedRealizationFunctor :
      ClassicalFunctor
        sourcePackage.Localized
        classicalPresentation.LocalizedCategory) : Prop :=
  ∀ s,
    localizedRealizationFunctor.obj
      (sourcePackage.localizeObj (sourcePackage.includeSyntax s)) =
    classicalPresentation.localization.localizationFunctor.obj
      (classicalPresentation.includeSyntax (syntaxTransport s))

/-- Real localization functor extracted from the proof-carrying source package. -/
def sourceLocalizationFunctor
    (sourcePackage : LayerD.SourceTracePackage) :
    ClassicalFunctor sourcePackage.Envelope sourcePackage.Localized := by
  let interfaceFunctor :
      ClassicalFunctor
        sourcePackage.localizationInterface.C
        sourcePackage.localizationInterface.D :=
    { obj := sourcePackage.localizationInterface.QObj
      map := fun {X Y} f => sourcePackage.localizationInterface.QMap f
      map_id := fun X => sourcePackage.localizationCompatibility.localizationMapId X
      map_comp := fun {X Y Z} f g => sourcePackage.localizationCompatibility.localizationMapComp f g }
  let sourceCategoryAlignment := sourcePackage.localizationCompatibility.sourceCategoryAlignment
  let targetCategoryAlignment := sourcePackage.localizationCompatibility.targetCategoryAlignment
  simpa [sourceCategoryAlignment, targetCategoryAlignment] using interfaceFunctor

/-- Canonical classical-localization package aligned with the source trace package itself. -/
def sourceAlignedClassicalLocalization
  (sourcePackage : LayerD.SourceTracePackage) :
    ClassicalLocalization sourcePackage.Envelope sourcePackage.Localized where
  weakEquivalence := fun X Y => ∃ f : X ⟶ Y, sourcePackage.weakEquivalence f
  localizationFunctor := sourceLocalizationFunctor sourcePackage
  LocalizationWitness := PUnit
  localizationWitness := PUnit.unit
  universalProperty := sourcePackage.localizationInfinity

/-- Canonical classical presentation obtained directly from the proof-carrying source package. -/
def sourceAlignedClassicalPresentation
  (sourcePackage : LayerD.SourceTracePackage) :
    ClassicalMotivicPresentation.{u1, u1, u1, v1, 0} where
  Syntax := sourcePackage.Syntax
  SourceCategory := sourcePackage.Envelope
  LocalizedCategory := sourcePackage.Localized
  includeSyntax := sourcePackage.includeSyntax
  localization := sourceAlignedClassicalLocalization sourcePackage
  GeometricShapeData := PUnit
  geometricShapeData := PUnit.unit
  geometricShapeAxioms :=
    sourcePackage.nisnevichDescentInfinity ∧
      sourcePackage.a1InvarianceInfinity ∧
      sourcePackage.tateStabilizationInfinity
  geometricShapeAxioms_holds := by
    exact ⟨sourcePackage.nisnevichDescentInfinity_holds,
      sourcePackage.a1InvarianceInfinity_holds,
      sourcePackage.tateStabilizationInfinity_holds⟩

/-- For the source-aligned classical presentation, the only remaining comparison theorem is now a
direct consequence of the constructive localization alignment exported by the source package. -/
theorem sourceAlignedSyntaxLocalizationComparison
    (sourcePackage : LayerD.SourceTracePackage) :
    SourceConstructionSyntaxLocalizationComparison
      sourcePackage
      (sourceAlignedClassicalPresentation sourcePackage)
      (fun s => s)
      (𝟭 sourcePackage.Localized) := by
  intro s
  let sourceCategoryAlignment := sourcePackage.localizationCompatibility.sourceCategoryAlignment
  let targetCategoryAlignment := sourcePackage.localizationCompatibility.targetCategoryAlignment
  let localizeObjAlignmentEq := sourcePackage.localizationCompatibility.localizeObjAlignment
  simpa [sourceCategoryAlignment, targetCategoryAlignment] using
    congrArg (fun localizeObj => localizeObj (sourcePackage.includeSyntax s))
      localizeObjAlignmentEq.symm

/-– The lower source package already carries its source-construction mathematics, and the
classical presentation now carries its geometric-shape proof. The remaining bridge-local datum is
the exact syntax/localization comparison theorem between those two concrete lanes. -/

/-- Middleware contract describing how the existing Layer B source export and its already-proved
source-construction theorem should feed a classical source-presentation slot. The source
presentation remains bridge-local adapter data because the ClassicalPeriods target lane begins at
structured comparison and period-faithfulness objects. -/
structure SourceRealizesClassicalMotivePresentation
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine) where
  sourceExport : LayerBSourceExportData presentation aux
  sourcePackage : LayerD.SourceTracePackage
  classicalPresentation : ClassicalMotivicPresentation.{u1, v1, w1, x1, y1}
  ReconstructionTransport : Type z1
  reconstructionTransport : ReconstructionTransport
  syntaxTransport : sourcePackage.Syntax → classicalPresentation.Syntax
  localizedRealizationFunctor :
    ClassicalFunctor
      sourcePackage.Localized
      classicalPresentation.LocalizedCategory
  sourceConstructionSyntaxLocalizationComparison :
    SourceConstructionSyntaxLocalizationComparison
      sourcePackage classicalPresentation syntaxTransport localizedRealizationFunctor

namespace SourceRealizesClassicalMotivePresentation

/-- The internal Layer D source package exposed by the Layer B export carried in the bridge. -/
def sourceTracePackage
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : SourceRealizesClassicalMotivePresentation presentation aux) :=
  bridge.sourcePackage

/-- Canonical constructor from the existing Layer B export seam. This computes the already
available Layer D witness and milestone realization, leaving only the classical-facing claims as
open obligations. -/
def ofLayerBSourceExportData
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (sourcePackage : LayerD.SourceTracePackage)
    (classicalPresentation : ClassicalMotivicPresentation.{u1, v1, w1, x1, y1})
    (ReconstructionTransport : Type z1)
    (reconstructionTransport : ReconstructionTransport)
    (syntaxTransport : sourcePackage.Syntax → classicalPresentation.Syntax)
    (localizedRealizationFunctor :
      ClassicalFunctor
        sourcePackage.Localized
        classicalPresentation.LocalizedCategory)
    (sourceConstructionSyntaxLocalizationComparison :
      SourceConstructionSyntaxLocalizationComparison
        sourcePackage classicalPresentation syntaxTransport localizedRealizationFunctor) :
    SourceRealizesClassicalMotivePresentation presentation aux where
  sourceExport := sourceExport
  sourcePackage := sourcePackage
  classicalPresentation := classicalPresentation
  ReconstructionTransport := ReconstructionTransport
  reconstructionTransport := reconstructionTransport
  syntaxTransport := syntaxTransport
  localizedRealizationFunctor := localizedRealizationFunctor
  sourceConstructionSyntaxLocalizationComparison :=
    sourceConstructionSyntaxLocalizationComparison

/-- Canonical bridge constructor using the source-aligned classical presentation and the exact
localization comparison theorem derived from the source package itself. -/
def ofSourceAlignedLayerBSourceExportData
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (sourcePackage : LayerD.SourceTracePackage)
    (ReconstructionTransport : Type z1)
    (reconstructionTransport : ReconstructionTransport) :
    SourceRealizesClassicalMotivePresentation presentation aux := by
  exact
    ofLayerBSourceExportData
      sourceExport
      sourcePackage
      (sourceAlignedClassicalPresentation sourcePackage)
      ReconstructionTransport
      reconstructionTransport
      (fun s => s)
      (𝟭 sourcePackage.Localized)
      (sourceAlignedSyntaxLocalizationComparison sourcePackage)

end SourceRealizesClassicalMotivePresentation

end ClassicalBridge
end TraceCalc
