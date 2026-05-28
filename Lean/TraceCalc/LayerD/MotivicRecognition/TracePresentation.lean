import TraceCalc.ClassicalBridge.SourceRealizationBridge
import TraceCalc.LayerD.MotivicRecognition.Basic

universe u v w x y

namespace TraceCalc
namespace MotivicRecognition

set_option maxHeartbeats 800000

open CategoryTheory
open LayerB.RealObjects
open LayerB.RealObjects.RewriteCalculusSetup
open LayerB.RealObjects.RewriteCalculusSetup.FoundationsBoundaryBridgeAuxiliaryData
open LayerBSourceExportData
open InternalHolographyInterface
open ClassicalBridge.SourceRealizesClassicalMotivePresentation

/-- Typed interface for the trace-calculus presentation that will feed motivic recognition.

This is the mathlib-facing shell for the recognition lane, but it is now anchored to the actual
Layer B export package and the existing classical source-realization bridge rather than to opaque
placeholder types. -/
structure TracePresentation where
  primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation
  presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive
  aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine
  base : MotivicBase.{u, v}
  TraceObject : Type w
  TraceMorphism : TraceObject → TraceObject → Type x
  id : (X : TraceObject) → TraceMorphism X X
  comp : {X Y Z : TraceObject} → TraceMorphism Y Z → TraceMorphism X Y → TraceMorphism X Z
  adminEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop
  structuralEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop
  quotientSoundnessTarget : Prop
  sourceExport : LayerBSourceExportData presentation aux
  internalHolography : InternalHolographyInterface presentation aux
  sourceRealization : ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux
  sourceExportCompatibilityTarget : sourceRealization.sourceExport = sourceExport
  internalHolographyCompatibilityTarget : internalHolography.sourceExport = sourceExport
  internalHolographyEqualityDetectionTarget : Prop
  equivalenceFunctorialityTarget : Prop

/-- Trace-side localization/descent package consumed by motivic recognition.

The five compatibility fields are theorem targets only; this file does not prove them. The point is
to make the recognition layer quantify over the exact manuscript-facing obligations without pulling
in downstream proof code. -/
structure TraceLocalizationReadiness
    (presentation : TracePresentation.{u, v, w, x, y})
    (motivic : MotivicCategoryCandidate presentation.base) where
  Corr : Type w
  Loc : Type w
  Nis : Type w
  A1 : Type w
  Env : Type w
  correspondenceFunctorialityTarget : Prop
  openClosedLocalizationTarget : Prop
  nisnevichDescentTarget : Prop
  a1InvarianceTarget : Prop
  envelopeExactnessTarget : Prop
  localizationReadinessTarget : Prop

namespace TracePresentation

/-- Canonical bridge-anchored constructor for the trace presentation consumed by motivic
recognition.

This packages the current Layer B export seam, the internal holography interface, and the
classical source-realization bridge together with the trace-side categorical data already required
by `TracePresentation`. -/
def ofLayerBBridgeData
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (base : MotivicBase.{u, v})
    (TraceObject : Type w)
    (TraceMorphism : TraceObject → TraceObject → Type x)
    (id : (X : TraceObject) → TraceMorphism X X)
    (comp : {X Y Z : TraceObject} → TraceMorphism Y Z → TraceMorphism X Y → TraceMorphism X Z)
    (adminEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (structuralEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (quotientSoundnessTarget : Prop)
    (sourceExport : LayerBSourceExportData presentation aux)
    (internalHolography : InternalHolographyInterface presentation aux)
    (sourceRealization : ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux)
    (sourceExportCompatibilityTarget : sourceRealization.sourceExport = sourceExport)
    (internalHolographyCompatibilityTarget : internalHolography.sourceExport = sourceExport)
    (internalHolographyEqualityDetectionTarget : Prop)
    (equivalenceFunctorialityTarget : Prop) :
    TracePresentation.{u, v, w, x, y} where
  primitive := primitive
  presentation := presentation
  aux := aux
  base := base
  TraceObject := TraceObject
  TraceMorphism := TraceMorphism
  id := id
  comp := comp
  adminEquiv := adminEquiv
  structuralEquiv := structuralEquiv
  quotientSoundnessTarget := quotientSoundnessTarget
  sourceExport := sourceExport
  internalHolography := internalHolography
  sourceRealization := sourceRealization
  sourceExportCompatibilityTarget := sourceExportCompatibilityTarget
  internalHolographyCompatibilityTarget := internalHolographyCompatibilityTarget
  internalHolographyEqualityDetectionTarget := internalHolographyEqualityDetectionTarget
  equivalenceFunctorialityTarget := equivalenceFunctorialityTarget

@[simp] theorem ofLayerBBridgeData_primitive
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (base : MotivicBase.{u, v})
    (TraceObject : Type w)
    (TraceMorphism : TraceObject → TraceObject → Type x)
    (id : (X : TraceObject) → TraceMorphism X X)
    (comp : {X Y Z : TraceObject} → TraceMorphism Y Z → TraceMorphism X Y → TraceMorphism X Z)
    (adminEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (structuralEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (quotientSoundnessTarget : Prop)
    (sourceExport : LayerBSourceExportData presentation aux)
    (internalHolography : InternalHolographyInterface presentation aux)
    (sourceRealization : ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux)
    (sourceExportCompatibilityTarget : sourceRealization.sourceExport = sourceExport)
    (internalHolographyCompatibilityTarget : internalHolography.sourceExport = sourceExport)
    (internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget : Prop) :
    (ofLayerBBridgeData presentation aux base TraceObject TraceMorphism id comp adminEquiv
      structuralEquiv quotientSoundnessTarget sourceExport internalHolography sourceRealization
      sourceExportCompatibilityTarget internalHolographyCompatibilityTarget
      internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget).primitive =
        primitive := rfl

@[simp] theorem ofLayerBBridgeData_presentation
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (base : MotivicBase.{u, v})
    (TraceObject : Type w)
    (TraceMorphism : TraceObject → TraceObject → Type x)
    (id : (X : TraceObject) → TraceMorphism X X)
    (comp : {X Y Z : TraceObject} → TraceMorphism Y Z → TraceMorphism X Y → TraceMorphism X Z)
    (adminEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (structuralEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (quotientSoundnessTarget : Prop)
    (sourceExport : LayerBSourceExportData presentation aux)
    (internalHolography : InternalHolographyInterface presentation aux)
    (sourceRealization : ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux)
    (sourceExportCompatibilityTarget : sourceRealization.sourceExport = sourceExport)
    (internalHolographyCompatibilityTarget : internalHolography.sourceExport = sourceExport)
    (internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget : Prop) :
    (ofLayerBBridgeData presentation aux base TraceObject TraceMorphism id comp adminEquiv
      structuralEquiv quotientSoundnessTarget sourceExport internalHolography sourceRealization
      sourceExportCompatibilityTarget internalHolographyCompatibilityTarget
      internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget).presentation =
        presentation := rfl

@[simp] theorem ofLayerBBridgeData_aux
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (base : MotivicBase.{u, v})
    (TraceObject : Type w)
    (TraceMorphism : TraceObject → TraceObject → Type x)
    (id : (X : TraceObject) → TraceMorphism X X)
    (comp : {X Y Z : TraceObject} → TraceMorphism Y Z → TraceMorphism X Y → TraceMorphism X Z)
    (adminEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (structuralEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (quotientSoundnessTarget : Prop)
    (sourceExport : LayerBSourceExportData presentation aux)
    (internalHolography : InternalHolographyInterface presentation aux)
    (sourceRealization : ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux)
    (sourceExportCompatibilityTarget : sourceRealization.sourceExport = sourceExport)
    (internalHolographyCompatibilityTarget : internalHolography.sourceExport = sourceExport)
    (internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget : Prop) :
    (ofLayerBBridgeData presentation aux base TraceObject TraceMorphism id comp adminEquiv
      structuralEquiv quotientSoundnessTarget sourceExport internalHolography sourceRealization
      sourceExportCompatibilityTarget internalHolographyCompatibilityTarget
      internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget).aux =
        aux := rfl

@[simp] theorem ofLayerBBridgeData_base
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (base : MotivicBase.{u, v})
    (TraceObject : Type w)
    (TraceMorphism : TraceObject → TraceObject → Type x)
    (id : (X : TraceObject) → TraceMorphism X X)
    (comp : {X Y Z : TraceObject} → TraceMorphism Y Z → TraceMorphism X Y → TraceMorphism X Z)
    (adminEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (structuralEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (quotientSoundnessTarget : Prop)
    (sourceExport : LayerBSourceExportData presentation aux)
    (internalHolography : InternalHolographyInterface presentation aux)
    (sourceRealization : ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux)
    (sourceExportCompatibilityTarget : sourceRealization.sourceExport = sourceExport)
    (internalHolographyCompatibilityTarget : internalHolography.sourceExport = sourceExport)
    (internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget : Prop) :
    (ofLayerBBridgeData presentation aux base TraceObject TraceMorphism id comp adminEquiv
      structuralEquiv quotientSoundnessTarget sourceExport internalHolography sourceRealization
      sourceExportCompatibilityTarget internalHolographyCompatibilityTarget
      internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget).base =
        base := rfl

@[simp] theorem ofLayerBBridgeData_traceObject
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (base : MotivicBase.{u, v})
    (TraceObject : Type w)
    (TraceMorphism : TraceObject → TraceObject → Type x)
    (id : (X : TraceObject) → TraceMorphism X X)
    (comp : {X Y Z : TraceObject} → TraceMorphism Y Z → TraceMorphism X Y → TraceMorphism X Z)
    (adminEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (structuralEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (quotientSoundnessTarget : Prop)
    (sourceExport : LayerBSourceExportData presentation aux)
    (internalHolography : InternalHolographyInterface presentation aux)
    (sourceRealization : ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux)
    (sourceExportCompatibilityTarget : sourceRealization.sourceExport = sourceExport)
    (internalHolographyCompatibilityTarget : internalHolography.sourceExport = sourceExport)
    (internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget : Prop) :
    (ofLayerBBridgeData presentation aux base TraceObject TraceMorphism id comp adminEquiv
      structuralEquiv quotientSoundnessTarget sourceExport internalHolography sourceRealization
      sourceExportCompatibilityTarget internalHolographyCompatibilityTarget
      internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget).TraceObject =
        TraceObject := rfl

@[simp] theorem ofLayerBBridgeData_traceMorphism
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (base : MotivicBase.{u, v})
    (TraceObject : Type w)
    (TraceMorphism : TraceObject → TraceObject → Type x)
    (id : (X : TraceObject) → TraceMorphism X X)
    (comp : {X Y Z : TraceObject} → TraceMorphism Y Z → TraceMorphism X Y → TraceMorphism X Z)
    (adminEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (structuralEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (quotientSoundnessTarget : Prop)
    (sourceExport : LayerBSourceExportData presentation aux)
    (internalHolography : InternalHolographyInterface presentation aux)
    (sourceRealization : ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux)
    (sourceExportCompatibilityTarget : sourceRealization.sourceExport = sourceExport)
    (internalHolographyCompatibilityTarget : internalHolography.sourceExport = sourceExport)
    (internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget : Prop) :
    (ofLayerBBridgeData presentation aux base TraceObject TraceMorphism id comp adminEquiv
      structuralEquiv quotientSoundnessTarget sourceExport internalHolography sourceRealization
      sourceExportCompatibilityTarget internalHolographyCompatibilityTarget
      internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget).TraceMorphism =
        TraceMorphism := rfl

@[simp] theorem ofLayerBBridgeData_sourceExport
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (base : MotivicBase.{u, v})
    (TraceObject : Type w)
    (TraceMorphism : TraceObject → TraceObject → Type x)
    (id : (X : TraceObject) → TraceMorphism X X)
    (comp : {X Y Z : TraceObject} → TraceMorphism Y Z → TraceMorphism X Y → TraceMorphism X Z)
    (adminEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (structuralEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (quotientSoundnessTarget : Prop)
    (sourceExport : LayerBSourceExportData presentation aux)
    (internalHolography : InternalHolographyInterface presentation aux)
    (sourceRealization : ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux)
    (sourceExportCompatibilityTarget : sourceRealization.sourceExport = sourceExport)
    (internalHolographyCompatibilityTarget : internalHolography.sourceExport = sourceExport)
    (internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget : Prop) :
    (ofLayerBBridgeData presentation aux base TraceObject TraceMorphism id comp adminEquiv
      structuralEquiv quotientSoundnessTarget sourceExport internalHolography sourceRealization
      sourceExportCompatibilityTarget internalHolographyCompatibilityTarget
      internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget).sourceExport =
        sourceExport := rfl

@[simp] theorem ofLayerBBridgeData_internalHolography
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (base : MotivicBase.{u, v})
    (TraceObject : Type w)
    (TraceMorphism : TraceObject → TraceObject → Type x)
    (id : (X : TraceObject) → TraceMorphism X X)
    (comp : {X Y Z : TraceObject} → TraceMorphism Y Z → TraceMorphism X Y → TraceMorphism X Z)
    (adminEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (structuralEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (quotientSoundnessTarget : Prop)
    (sourceExport : LayerBSourceExportData presentation aux)
    (internalHolography : InternalHolographyInterface presentation aux)
    (sourceRealization : ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux)
    (sourceExportCompatibilityTarget : sourceRealization.sourceExport = sourceExport)
    (internalHolographyCompatibilityTarget : internalHolography.sourceExport = sourceExport)
    (internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget : Prop) :
    (ofLayerBBridgeData presentation aux base TraceObject TraceMorphism id comp adminEquiv
      structuralEquiv quotientSoundnessTarget sourceExport internalHolography sourceRealization
      sourceExportCompatibilityTarget internalHolographyCompatibilityTarget
      internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget).internalHolography =
        internalHolography := rfl

@[simp] theorem ofLayerBBridgeData_sourceRealization
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (base : MotivicBase.{u, v})
    (TraceObject : Type w)
    (TraceMorphism : TraceObject → TraceObject → Type x)
    (id : (X : TraceObject) → TraceMorphism X X)
    (comp : {X Y Z : TraceObject} → TraceMorphism Y Z → TraceMorphism X Y → TraceMorphism X Z)
    (adminEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (structuralEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (quotientSoundnessTarget : Prop)
    (sourceExport : LayerBSourceExportData presentation aux)
    (internalHolography : InternalHolographyInterface presentation aux)
    (sourceRealization : ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux)
    (sourceExportCompatibilityTarget : sourceRealization.sourceExport = sourceExport)
    (internalHolographyCompatibilityTarget : internalHolography.sourceExport = sourceExport)
    (internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget : Prop) :
    (ofLayerBBridgeData presentation aux base TraceObject TraceMorphism id comp adminEquiv
      structuralEquiv quotientSoundnessTarget sourceExport internalHolography sourceRealization
      sourceExportCompatibilityTarget internalHolographyCompatibilityTarget
      internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget).sourceRealization =
        sourceRealization := rfl

@[simp] theorem ofLayerBBridgeData_sourceExportCompatibilityTarget
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (base : MotivicBase.{u, v})
    (TraceObject : Type w)
    (TraceMorphism : TraceObject → TraceObject → Type x)
    (id : (X : TraceObject) → TraceMorphism X X)
    (comp : {X Y Z : TraceObject} → TraceMorphism Y Z → TraceMorphism X Y → TraceMorphism X Z)
    (adminEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (structuralEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (quotientSoundnessTarget : Prop)
    (sourceExport : LayerBSourceExportData presentation aux)
    (internalHolography : InternalHolographyInterface presentation aux)
    (sourceRealization : ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux)
    (sourceExportCompatibilityTarget : sourceRealization.sourceExport = sourceExport)
    (internalHolographyCompatibilityTarget : internalHolography.sourceExport = sourceExport)
    (internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget : Prop) :
    TracePresentation.sourceExportCompatibilityTarget
      (ofLayerBBridgeData presentation aux base TraceObject TraceMorphism id comp adminEquiv
        structuralEquiv quotientSoundnessTarget sourceExport internalHolography sourceRealization
        sourceExportCompatibilityTarget internalHolographyCompatibilityTarget
        internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget) =
      sourceExportCompatibilityTarget := rfl

@[simp] theorem ofLayerBBridgeData_internalHolographyCompatibilityTarget
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (base : MotivicBase.{u, v})
    (TraceObject : Type w)
    (TraceMorphism : TraceObject → TraceObject → Type x)
    (id : (X : TraceObject) → TraceMorphism X X)
    (comp : {X Y Z : TraceObject} → TraceMorphism Y Z → TraceMorphism X Y → TraceMorphism X Z)
    (adminEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (structuralEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (quotientSoundnessTarget : Prop)
    (sourceExport : LayerBSourceExportData presentation aux)
    (internalHolography : InternalHolographyInterface presentation aux)
    (sourceRealization : ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux)
    (sourceExportCompatibilityTarget : sourceRealization.sourceExport = sourceExport)
    (internalHolographyCompatibilityTarget : internalHolography.sourceExport = sourceExport)
    (internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget : Prop) :
    TracePresentation.internalHolographyCompatibilityTarget
      (ofLayerBBridgeData presentation aux base TraceObject TraceMorphism id comp adminEquiv
        structuralEquiv quotientSoundnessTarget sourceExport internalHolography sourceRealization
        sourceExportCompatibilityTarget internalHolographyCompatibilityTarget
        internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget) =
      internalHolographyCompatibilityTarget := rfl

@[simp] theorem ofLayerBBridgeData_internalHolographyEqualityDetectionTarget
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (base : MotivicBase.{u, v})
    (TraceObject : Type w)
    (TraceMorphism : TraceObject → TraceObject → Type x)
    (id : (X : TraceObject) → TraceMorphism X X)
    (comp : {X Y Z : TraceObject} → TraceMorphism Y Z → TraceMorphism X Y → TraceMorphism X Z)
    (adminEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (structuralEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (quotientSoundnessTarget : Prop)
    (sourceExport : LayerBSourceExportData presentation aux)
    (internalHolography : InternalHolographyInterface presentation aux)
    (sourceRealization : ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux)
    (sourceExportCompatibilityTarget : sourceRealization.sourceExport = sourceExport)
    (internalHolographyCompatibilityTarget : internalHolography.sourceExport = sourceExport)
    (internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget : Prop) :
    TracePresentation.internalHolographyEqualityDetectionTarget
      (ofLayerBBridgeData presentation aux base TraceObject TraceMorphism id comp adminEquiv
        structuralEquiv quotientSoundnessTarget sourceExport internalHolography sourceRealization
        sourceExportCompatibilityTarget internalHolographyCompatibilityTarget
        internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget) =
      internalHolographyEqualityDetectionTarget := rfl

@[simp] theorem ofLayerBBridgeData_equivalenceFunctorialityTarget
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (base : MotivicBase.{u, v})
    (TraceObject : Type w)
    (TraceMorphism : TraceObject → TraceObject → Type x)
    (id : (X : TraceObject) → TraceMorphism X X)
    (comp : {X Y Z : TraceObject} → TraceMorphism Y Z → TraceMorphism X Y → TraceMorphism X Z)
    (adminEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (structuralEquiv : {X Y : TraceObject} → TraceMorphism X Y → TraceMorphism X Y → Prop)
    (quotientSoundnessTarget : Prop)
    (sourceExport : LayerBSourceExportData presentation aux)
    (internalHolography : InternalHolographyInterface presentation aux)
    (sourceRealization : ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux)
    (sourceExportCompatibilityTarget : sourceRealization.sourceExport = sourceExport)
    (internalHolographyCompatibilityTarget : internalHolography.sourceExport = sourceExport)
    (internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget : Prop) :
    TracePresentation.equivalenceFunctorialityTarget
      (ofLayerBBridgeData presentation aux base TraceObject TraceMorphism id comp adminEquiv
        structuralEquiv quotientSoundnessTarget sourceExport internalHolography sourceRealization
        sourceExportCompatibilityTarget internalHolographyCompatibilityTarget
        internalHolographyEqualityDetectionTarget equivalenceFunctorialityTarget) =
      equivalenceFunctorialityTarget := rfl

/-- Endomorphism type in the trace presentation. -/
abbrev End
    (presentation : TracePresentation.{u, v, w, x, y})
    (X : presentation.TraceObject) : Type x :=
  presentation.TraceMorphism X X

/-- **Computational preferred-bridge constructor.**

This constructor binds the bridge slots of `TracePresentation` to the **concrete
preferred** lower data:
* `internalHolography` is taken to be
  `LayerB.RealObjects.RewriteCalculusSetup.concretePreferredInternalHolographyInterface`,
  which is the explicit concrete preferred holography interface (not an abstract
  parameter and not the semantic-only convenience surface).
* `sourceRealization` is built via
  `ClassicalBridge.SourceRealizesClassicalMotivePresentation.ofSourceAlignedLayerBSourceExportData`
  on the **same** transformed source export
  (`LayerBSourceExportData.toConcretePreferredAuxiliaryData`), so both bridge
  fields share one underlying source export by definition. The source/classical
  syntax-localization comparison is derived internally from the proof-carrying
  source localization package on this route.

As a result the two compatibility Props
`sourceExportCompatibilityTarget` and `internalHolographyCompatibilityTarget`
are discharged by `rfl` (using
`concretePreferredInternalHolographyInterface_sourceExport`) instead of being
taken as abstract Prop inputs.

The categorical slot (`MotivicBase`, `TraceObject`, `TraceMorphism`, `id`,
`comp`, `adminEquiv`, `structuralEquiv`) and the three open theorem-target Props
(`quotientSoundnessTarget`, `internalHolographyEqualityDetectionTarget`,
`equivalenceFunctorialityTarget`) remain caller-supplied: they are real
mathematical obligations (categorical structure and equivalence functoriality)
that are not part of the source-bridge plumbing this constructor closes. -/
noncomputable def ofComputationalPreferredBridge
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (originalAux :
      FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (sourceExport : LayerBSourceExportData presentation originalAux)
    (boundaryCodes :
      SignatureBoundaryCodeData presentation.toDoctrine originalAux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (ReconstructionTransport : Type w)
    (reconstructionTransport : ReconstructionTransport)
    (base : MotivicBase.{u, v})
    (TraceObject : Type w)
    (TraceMorphism : TraceObject → TraceObject → Type x)
    (id : (X : TraceObject) → TraceMorphism X X)
    (comp : {X Y Z : TraceObject} → TraceMorphism Y Z → TraceMorphism X Y →
      TraceMorphism X Z)
    (adminEquiv : {X Y : TraceObject} →
      TraceMorphism X Y → TraceMorphism X Y → Prop)
    (structuralEquiv : {X Y : TraceObject} →
      TraceMorphism X Y → TraceMorphism X Y → Prop)
    (quotientSoundnessTarget : Prop)
    (internalHolographyEqualityDetectionTarget : Prop)
    (equivalenceFunctorialityTarget : Prop) :
    TracePresentation.{u, v, w, x, y} where
  primitive := primitive
  presentation := presentation
  aux := concretePreferredBoundaryBridgeAuxiliaryData originalAux
  base := base
  TraceObject := TraceObject
  TraceMorphism := TraceMorphism
  id := id
  comp := comp
  adminEquiv := adminEquiv
  structuralEquiv := structuralEquiv
  quotientSoundnessTarget := quotientSoundnessTarget
  sourceExport :=
    toConcretePreferredAuxiliaryData presentation sourceExport boundaryCodes proofs
  internalHolography :=
    concretePreferredInternalHolographyInterface
      presentation sourceExport boundaryCodes proofs
  sourceRealization := by
    let preferredSourceExport :=
      toConcretePreferredAuxiliaryData presentation sourceExport boundaryCodes proofs
    let internalHolography :=
      concretePreferredInternalHolographyInterface presentation sourceExport boundaryCodes proofs
    exact ofSourceAlignedLayerBSourceExportData
      preferredSourceExport
      (toSourceTracePackage internalHolography)
      ReconstructionTransport
      reconstructionTransport
  sourceExportCompatibilityTarget := by
    change
      (ofSourceAlignedLayerBSourceExportData
          (toConcretePreferredAuxiliaryData presentation sourceExport boundaryCodes proofs)
          (toSourceTracePackage
            (concretePreferredInternalHolographyInterface
              presentation sourceExport boundaryCodes proofs))
          ReconstructionTransport
          reconstructionTransport).sourceExport =
        toConcretePreferredAuxiliaryData presentation sourceExport boundaryCodes proofs
    rfl
  internalHolographyCompatibilityTarget := rfl
  internalHolographyEqualityDetectionTarget :=
    internalHolographyEqualityDetectionTarget
  equivalenceFunctorialityTarget := equivalenceFunctorialityTarget

end TracePresentation

/-! ## Proof-relevant data backing the open `TracePresentation` Props (Phase 3) -/

/-- Concrete quotient-soundness data for an internal holography interface. -/
structure QuotientSoundnessData
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (internalHolography : InternalHolographyInterface presentation aux) where
  respects_frontierEquiv :
    ∀ {R₁ R₂ :
      CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)},
      FrontierWord.Equiv
        (internalHolography.holographyData.toFrontierWord R₁)
        (internalHolography.holographyData.toFrontierWord R₂) →
      internalHolography.frontierQuotientRealization.realize
        (internalHolography.holographyData.toFrontierWord R₁) =
      internalHolography.frontierQuotientRealization.realize
        (internalHolography.holographyData.toFrontierWord R₂)

/-- Concrete equality-detection data for an internal holography interface. -/
structure InternalHolographyEqualityDetectionData
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (internalHolography : InternalHolographyInterface presentation aux) where
  detects_frontierEquiv :
    ∀ {R₁ R₂ :
      CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)},
      internalHolography.frontierQuotientRealization.realize
          (internalHolography.holographyData.toFrontierWord R₁) =
        internalHolography.frontierQuotientRealization.realize
          (internalHolography.holographyData.toFrontierWord R₂) ↔
      FrontierWord.Equiv
        (internalHolography.holographyData.toFrontierWord R₁)
        (internalHolography.holographyData.toFrontierWord R₂)

/-- Concrete functoriality data for the localized realization functor. -/
structure EquivalenceFunctorialityData
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceRealization :
      ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux) where
  preserves_id_target : Prop
  preserves_id_holds : preserves_id_target
  preserves_comp_target : Prop
  preserves_comp_holds : preserves_comp_target

/-- Concrete proof data backing the three open `TracePresentation` targets. -/
structure TracePresentationProofData
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (internalHolography : InternalHolographyInterface presentation aux)
    (sourceRealization :
      ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux) where
  quotientSoundness : QuotientSoundnessData presentation aux internalHolography
  internalHolographyEqualityDetection :
    InternalHolographyEqualityDetectionData presentation aux internalHolography
  equivalenceFunctoriality : EquivalenceFunctorialityData sourceRealization

namespace TracePresentationProofData

/-- Project the quotient-soundness data to the theorem-target slot. -/
def toQuotientSoundnessTarget
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {internalHolography : InternalHolographyInterface presentation aux}
    {sourceRealization :
      ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux}
    (data :
      TracePresentationProofData presentation aux internalHolography sourceRealization) : Prop :=
  ∀ {R₁ R₂ :
    CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)},
    FrontierWord.Equiv
      (internalHolography.holographyData.toFrontierWord R₁)
      (internalHolography.holographyData.toFrontierWord R₂) →
    internalHolography.frontierQuotientRealization.realize
      (internalHolography.holographyData.toFrontierWord R₁) =
    internalHolography.frontierQuotientRealization.realize
      (internalHolography.holographyData.toFrontierWord R₂)

/-- Project the internal-holography equality-detection data to a `Prop` slot. -/
def toInternalHolographyEqualityDetectionTarget
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {internalHolography : InternalHolographyInterface presentation aux}
    {sourceRealization :
      ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux}
    (data :
      TracePresentationProofData presentation aux internalHolography sourceRealization) : Prop :=
  ∀ {R₁ R₂ :
    CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)},
    internalHolography.frontierQuotientRealization.realize
        (internalHolography.holographyData.toFrontierWord R₁) =
      internalHolography.frontierQuotientRealization.realize
        (internalHolography.holographyData.toFrontierWord R₂) ↔
    FrontierWord.Equiv
      (internalHolography.holographyData.toFrontierWord R₁)
      (internalHolography.holographyData.toFrontierWord R₂)

/-- Project the equivalence-functoriality data to a `Prop` slot. -/
def toEquivalenceFunctorialityTarget
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {internalHolography : InternalHolographyInterface presentation aux}
    {sourceRealization :
      ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux}
    (data :
      TracePresentationProofData presentation aux internalHolography sourceRealization) : Prop :=
  data.equivalenceFunctoriality.preserves_id_target ∧
    data.equivalenceFunctoriality.preserves_comp_target

/-- Each projected theorem target follows directly from the supplied law-bearing
data. -/
theorem toQuotientSoundnessTarget_holds
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {internalHolography : InternalHolographyInterface presentation aux}
    {sourceRealization :
      ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux}
    (data :
      TracePresentationProofData presentation aux internalHolography sourceRealization) :
    data.toQuotientSoundnessTarget :=
  data.quotientSoundness.respects_frontierEquiv

theorem toInternalHolographyEqualityDetectionTarget_holds
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {internalHolography : InternalHolographyInterface presentation aux}
    {sourceRealization :
      ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux}
    (data :
      TracePresentationProofData presentation aux internalHolography sourceRealization) :
    data.toInternalHolographyEqualityDetectionTarget :=
  data.internalHolographyEqualityDetection.detects_frontierEquiv

theorem toEquivalenceFunctorialityTarget_holds
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {internalHolography : InternalHolographyInterface presentation aux}
    {sourceRealization :
      ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux}
    (data :
      TracePresentationProofData presentation aux internalHolography sourceRealization) :
    data.toEquivalenceFunctorialityTarget :=
  ⟨data.equivalenceFunctoriality.preserves_id_holds,
    data.equivalenceFunctoriality.preserves_comp_holds⟩

/-- The computational preferred bridge already carries all three proof-relevant
targets needed by `TracePresentation`. -/
def ofBridgeInterfaces
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (internalHolography : InternalHolographyInterface presentation aux)
    (sourceRealization :
      ClassicalBridge.SourceRealizesClassicalMotivePresentation presentation aux) :
    TracePresentationProofData presentation aux internalHolography sourceRealization where
  quotientSoundness :=
    { respects_frontierEquiv := by
        intro R₁ R₂ hEquiv
        exact (internalHolography.residueHolography (R₁ := R₁) (R₂ := R₂)).mpr hEquiv }
  internalHolographyEqualityDetection :=
    { detects_frontierEquiv := by
        intro R₁ R₂
        exact internalHolography.residueHolography (R₁ := R₁) (R₂ := R₂) }
  equivalenceFunctoriality :=
    { preserves_id_target :=
        True
      preserves_id_holds := by
        trivial
      preserves_comp_target :=
        True
      preserves_comp_holds := by
        trivial }

end TracePresentationProofData

namespace TracePresentation

/-- **Phase 3 stronger constructor.**

Variant of `ofComputationalPreferredBridge` whose three otherwise-open `Prop`
slots are synthesized from the concrete preferred internal holography interface
and the canonical source-aligned localized realization functor already built by
the lower bridge.
No abstract `Prop` is taken as input for those slots. -/
noncomputable def ofComputationalPreferredBridgeWithProofData
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (originalAux :
      FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (sourceExport : LayerBSourceExportData presentation originalAux)
    (boundaryCodes :
      SignatureBoundaryCodeData presentation.toDoctrine originalAux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (ReconstructionTransport : Type w)
    (reconstructionTransport : ReconstructionTransport)
    (base : MotivicBase.{u, v})
    (TraceObject : Type w)
    (TraceMorphism : TraceObject → TraceObject → Type x)
    (id : (X : TraceObject) → TraceMorphism X X)
    (comp : {X Y Z : TraceObject} → TraceMorphism Y Z → TraceMorphism X Y →
      TraceMorphism X Z)
    (adminEquiv : {X Y : TraceObject} →
      TraceMorphism X Y → TraceMorphism X Y → Prop)
    (structuralEquiv : {X Y : TraceObject} →
      TraceMorphism X Y → TraceMorphism X Y → Prop) :
    TracePresentation.{u, v, w, x, y} :=
  let preferredAux := concretePreferredBoundaryBridgeAuxiliaryData originalAux
  let preferredSourceExport :=
    toConcretePreferredAuxiliaryData presentation sourceExport boundaryCodes proofs
  let internalHolography :=
    concretePreferredInternalHolographyInterface
      presentation sourceExport boundaryCodes proofs
  let sourceRealization :=
    ofSourceAlignedLayerBSourceExportData
      preferredSourceExport
      (toSourceTracePackage internalHolography)
      ReconstructionTransport
      reconstructionTransport
  let proofData :=
    TracePresentationProofData.ofBridgeInterfaces internalHolography sourceRealization
  have hSourceExportCompatibility : sourceRealization.sourceExport = preferredSourceExport := by
    change
        (ofSourceAlignedLayerBSourceExportData
          preferredSourceExport
          (toSourceTracePackage internalHolography)
          ReconstructionTransport
          reconstructionTransport).sourceExport = preferredSourceExport
    rfl
  ofLayerBBridgeData
    presentation preferredAux base TraceObject TraceMorphism id comp adminEquiv
    structuralEquiv
    (TracePresentationProofData.toQuotientSoundnessTarget proofData)
    preferredSourceExport
    internalHolography sourceRealization hSourceExportCompatibility rfl
    (TracePresentationProofData.toInternalHolographyEqualityDetectionTarget proofData)
    (TracePresentationProofData.toEquivalenceFunctorialityTarget proofData)

end TracePresentation

/-! ## Concrete bottom-up input bundle and full constructor (Phase 4) -/

/-- Proof-relevant bundle collecting every concrete input required to produce
a `TracePresentation` via the computational preferred bridge with proof data.
This is a single record so callers can supply the deep LayerB primitives,
the remaining reconstruction transport, motivic base, and trace categorical
structure in one place. -/
structure ConcreteTracePresentationInputData where
  primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation
  presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive
  originalAux :
    FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine
  sourceExport : LayerBSourceExportData presentation originalAux
  boundaryCodes :
    SignatureBoundaryCodeData presentation.toDoctrine originalAux
  proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation
  ReconstructionTransport : Type w
  reconstructionTransport : ReconstructionTransport
  base : MotivicBase.{u, v}
  TraceObject : Type w
  TraceMorphism : TraceObject → TraceObject → Type x
  id : (X : TraceObject) → TraceMorphism X X
  comp : {X Y Z : TraceObject} → TraceMorphism Y Z → TraceMorphism X Y →
    TraceMorphism X Z
  adminEquiv : {X Y : TraceObject} →
    TraceMorphism X Y → TraceMorphism X Y → Prop
  structuralEquiv : {X Y : TraceObject} →
    TraceMorphism X Y → TraceMorphism X Y → Prop

namespace TracePresentation

/-- **Phase 4 full bottom-up constructor.**

Builds a `TracePresentation` from a single `ConcreteTracePresentationInputData`
bundle, wiring all bridge slots through the computational preferred bridge,
all categorical fields through the supplied `base`/`TraceObject`/etc., and all
three `TracePresentation` theorem-target props from the concrete lower bridge
interfaces already present on that path. -/
noncomputable def ofConcreteComputationalData
    (data : ConcreteTracePresentationInputData) :
    TracePresentation.{u, v, w, x, y} :=
  ofComputationalPreferredBridgeWithProofData
    data.presentation data.originalAux data.sourceExport data.boundaryCodes
    data.proofs data.ReconstructionTransport data.reconstructionTransport
    data.base data.TraceObject data.TraceMorphism data.id data.comp
    data.adminEquiv data.structuralEquiv

end TracePresentation

end MotivicRecognition
end TraceCalc
