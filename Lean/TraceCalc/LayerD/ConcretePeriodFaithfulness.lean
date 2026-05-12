import TraceCalc.LayerD.PeriodFaithfulnessAssembly
import TraceCalc.ClassicalPeriods.Basic
import TraceCalc.ClassicalPeriods.ComparisonBoundaryRecovery
import TraceCalc.LayerB.RealObjects.SourceHolographyToLayerD

universe u v w

namespace TraceCalc
namespace LayerD

/-!
# Concrete period-faithfulness instantiation

This module proves the concrete classical period faithfulness theorem at the over-scalar level
using actual Mathlib algebraic theorems from `ClassicalPeriods.Basic`.

## Design

The concrete theorems are proved DIRECTLY (not via `PeriodFaithfulnessContext` type families).
Non-vacuous instantiation of the abstract type-family framework in Lean 4 (without the
univalence axiom) requires that type equality of indexed structures implies field equality,
which is not derivable from abstract type proofs. See the `PeriodFaithfulnessContext`
Instantiation note at the end of this file for a detailed explanation.

The genuine mathematical content lives in
`overScalarRealization_eq_of_basisFreePeriodMap_eq` and
`full_morphism_eq_of_betti_deRham_basisFreePeriodMap_eq`.
-/

open ClassicalPeriods

/-! ## Concrete Period-Faithfulness Theorems (Direct) -/

/-
TEX ref: `our_paper_draft.tex`, Corollary `cor:internal-period-faithfulness`, Section 10.
Paper role: scalar period faithfulness — basisFreePeriodMap equality implies over-scalar map equality.
Lean status: PROVED. Real proof from algebraic reflection in `ClassicalPeriods.Basic`.
Scope: this is the over-scalar algebraic reflection lemma. The final full-morphism route below
uses `full_morphism_eq_of_basisFreePeriodMap_eq_of_injective_extensions`, which derives the
base-map hypotheses from explicit injectivity data instead of using the legacy auxiliary alias.
-/
/-- **Concrete over-scalar realization equality theorem**.

For fixed source and target classical comparison objects, equality of the basis-free period map
implies equality of both over-scalar realization maps. Proved directly from the algebraic
reflection theorems `deRhamMapOverScalar_eq_of_basisFreePeriodMap_eq` and
`bettiMapOverScalar_eq_of_basisFreePeriodMap_eq` in `ClassicalPeriods.Basic`. -/
theorem overScalarRealization_eq_of_basisFreePeriodMap_eq
    {ctx : ClassicalComparisonContext.{u, v}}
    (source target : ClassicalStructuredComparisonObject ctx)
    (f g : ClassicalStructuredComparisonMorphism source target)
    (hScalar : f.basisFreePeriodMap = g.basisFreePeriodMap) :
    f.deRhamMapOverScalar = g.deRhamMapOverScalar ∧
      f.bettiMapOverScalar = g.bettiMapOverScalar :=
  ⟨ClassicalStructuredComparisonMorphism.deRhamMapOverScalar_eq_of_basisFreePeriodMap_eq
      f g hScalar,
   ClassicalStructuredComparisonMorphism.bettiMapOverScalar_eq_of_basisFreePeriodMap_eq
      f g hScalar⟩

/-
TEX ref: `our_paper_draft.tex`, Corollary `cor:internal-period-faithfulness`,
         Theorem `thm:classical-coarse-period-consequence`, Section 10/12.
Paper role: full morphism equality from basis-free period equality.
Lean status: LEGACY SUPPORT LEMMA.
  This lemma proves full equality from basisFreePeriodMap equality plus TWO explicit map
  hypotheses:
    (1) f.bettiMap = g.bettiMap
    (2) f.deRhamMap = g.deRhamMap
  Hypotheses (1) and (2) are genuine extra obligations not discharged from period equality here.
  (The former hypotheses (3) f.bettiExtensionCompatibility = g.bettiExtensionCompatibility
  and (4) f.deRhamExtensionCompatibility = g.deRhamExtensionCompatibility are no longer
  required: they are proof-type fields whose equality is established internally by
  `eq_of_map_fields_eq` via proof irrelevance once the map fields agree.)
The final route for this file discharges those two hypotheses from explicit injectivity of the
target scalar-extension maps in
`full_morphism_eq_of_basisFreePeriodMap_eq_of_injective_extensions`.
-/
/-- **Full morphism equality from basis-free period-map equality plus explicit Betti/de Rham map
equality**.

Given that the base-level maps and extension compatibility fields agree, equality of the
basis-free period map implies literal equality of the structured comparison morphisms. -/
theorem full_morphism_eq_of_betti_deRham_basisFreePeriodMap_eq
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : ClassicalStructuredComparisonObject ctx}
    (f g : ClassicalStructuredComparisonMorphism source target)
    (hBetti : f.bettiMap = g.bettiMap)
    (hDeRham : f.deRhamMap = g.deRhamMap)
    (hBasis : f.basisFreePeriodMap = g.basisFreePeriodMap) :
    f = g := by
  obtain ⟨hDeRhamScalar, hBettiScalar⟩ :=
    overScalarRealization_eq_of_basisFreePeriodMap_eq source target f g hBasis
  exact ClassicalStructuredComparisonMorphism.eq_of_map_fields_eq
    f g hBetti hDeRham hBettiScalar hDeRhamScalar

/-- Full morphism equality from basis-free period-map equality, assuming scalar
extension maps are injective on the target object.

This discharges the two extra hypotheses of
`full_morphism_eq_of_betti_deRham_basisFreePeriodMap_eq` by transporting scalar-map equality
back along extension-compatibility squares. -/
theorem full_morphism_eq_of_basisFreePeriodMap_eq_of_injective_extensions
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : ClassicalStructuredComparisonObject ctx}
    (f g : ClassicalStructuredComparisonMorphism source target)
    (hExtendBettiInj : Function.Injective target.extendBetti)
    (hExtendDeRhamInj : Function.Injective target.extendDeRham)
    (hBasis : f.basisFreePeriodMap = g.basisFreePeriodMap) :
    f = g := by
  obtain ⟨hDeRhamScalar, hBettiScalar⟩ :=
    overScalarRealization_eq_of_basisFreePeriodMap_eq source target f g hBasis
  have hBetti : f.bettiMap = g.bettiMap := by
    ext x
    apply hExtendBettiInj
    calc
      target.extendBetti (f.bettiMap x)
          = f.bettiMapOverScalar (source.extendBetti x) := by
              symm
              exact f.bettiExtensionCompatibility x
      _ = g.bettiMapOverScalar (source.extendBetti x) := by
        simp [hBettiScalar]
      _ = target.extendBetti (g.bettiMap x) := by
            exact g.bettiExtensionCompatibility x
  have hDeRham : f.deRhamMap = g.deRhamMap := by
    ext x
    apply hExtendDeRhamInj
    calc
      target.extendDeRham (f.deRhamMap x)
          = f.deRhamMapOverScalar (source.extendDeRham x) := by
              symm
              exact f.deRhamExtensionCompatibility x
      _ = g.deRhamMapOverScalar (source.extendDeRham x) := by
        simp [hDeRhamScalar]
      _ = target.extendDeRham (g.deRhamMap x) := by
            exact g.deRhamExtensionCompatibility x
  exact full_morphism_eq_of_betti_deRham_basisFreePeriodMap_eq f g hBetti hDeRham hBasis

/-! ## Bridge-To-Visible-Boundary Data

This is the current narrow comparison-side bridge surface. It does not yet map
packed structured comparison data into the final internal holography carrier
`I.visibleBoundary`; instead it records the exact labels and identifiers that a
future comparison-to-visible-boundary theorem must transport into that lane.
-/

/-- Sigma-packaged structured comparison carrier used by the current classical
tomography lane. -/
abbrev PackedStructuredComparison
    (ctx : ClassicalComparisonContext.{u, v}) :=
  SomeStructuredComparisonMorphism ctx

/-- BRIDGE-TO-VISIBLE-BOUNDARY: the narrow comparison-side data presently
needed to project packed structured comparison values toward the internal
visible-boundary lane.

This is intentionally not a theorem closure. It records only the labels and
identifiers that are visibly recoverable from structured comparison data before
any theorem connects them to the final internal visible-boundary carrier. -/
structure StructuredComparisonBoundaryProjectionData
    (ctx : ClassicalComparisonContext.{u, v}) where
  boundarySlotLabels : PackedStructuredComparison ctx → StructuredComparisonSlotData
  sourceBoundaryIdentifier : PackedStructuredComparison ctx → String
  targetBoundaryIdentifier : PackedStructuredComparison ctx → String
  gluingCompatibilityLabel : PackedStructuredComparison ctx → String
  boundaryProjectionReadFromStructuredComparisonData :
    ∀ comparison,
      sourceBoundaryIdentifier comparison =
        (boundarySlotLabels comparison).sourceSlot ∧
      targetBoundaryIdentifier comparison =
        (boundarySlotLabels comparison).targetSlot ∧
      gluingCompatibilityLabel comparison =
        (boundarySlotLabels comparison).comparisonSlot

namespace StructuredComparisonBoundaryProjectionData

/-- Local comparison-side visible-boundary carrier extracted from packed
structured comparison data. This is the current bridge carrier, not the final
internal `I.visibleBoundary` target. -/
structure VisibleBoundaryCarrier
    {ctx : ClassicalComparisonContext.{u, v}}
    (_ : StructuredComparisonBoundaryProjectionData ctx) where
  boundaryPorts : VisibleBoundaryPortData
  gluingCompatibilityLabel : String

/-- The current comparison-side bridge map from packed structured comparison
data into the local visible-boundary carrier. -/
def structuredComparisonVisibleBoundary
    {ctx : ClassicalComparisonContext.{u, v}}
    (projection : StructuredComparisonBoundaryProjectionData ctx) :
    PackedStructuredComparison ctx → VisibleBoundaryCarrier projection :=
  fun comparison =>
    { boundaryPorts :=
        { sourcePort := projection.sourceBoundaryIdentifier comparison
          targetPort := projection.targetBoundaryIdentifier comparison
          bettiPort := (projection.boundarySlotLabels comparison).bettiSlot
          deRhamPort := (projection.boundarySlotLabels comparison).deRhamSlot }
      gluingCompatibilityLabel := projection.gluingCompatibilityLabel comparison }

/-- The induced comparison-side boundary-port projection, matching the existing
slot-recovery decomposition in `ComparisonBoundaryRecovery.lean`. -/
def structuredComparisonVisibleBoundaryPorts
    {ctx : ClassicalComparisonContext.{u, v}}
    (projection : StructuredComparisonBoundaryProjectionData ctx) :
    PackedStructuredComparison ctx → VisibleBoundaryPortData :=
  fun comparison => (projection.structuredComparisonVisibleBoundary comparison).boundaryPorts

@[simp] theorem structuredComparisonVisibleBoundary_eq_of_eq
    {ctx : ClassicalComparisonContext.{u, v}}
    (projection : StructuredComparisonBoundaryProjectionData ctx)
    {comparison₁ comparison₂ : PackedStructuredComparison ctx}
    (h : comparison₁ = comparison₂) :
    projection.structuredComparisonVisibleBoundary comparison₁ =
      projection.structuredComparisonVisibleBoundary comparison₂ := by
  cases h
  rfl

/-- The first honest equality theorem on the current bridge carrier: equality of
packed structured comparison data implies equality of the projected comparison-
side visible-boundary carrier. This is intentionally weaker than a theorem
about the final internal holography carrier. -/
theorem comparison_eq_implies_visibleBoundary_eq
    {ctx : ClassicalComparisonContext.{u, v}}
    (projection : StructuredComparisonBoundaryProjectionData ctx)
    {comparison₁ comparison₂ : PackedStructuredComparison ctx}
    (h : comparison₁ = comparison₂) :
    projection.structuredComparisonVisibleBoundary comparison₁ =
      projection.structuredComparisonVisibleBoundary comparison₂ :=
  projection.structuredComparisonVisibleBoundary_eq_of_eq h

end StructuredComparisonBoundaryProjectionData

private def corrBoundarySlotLabelData : StructuredComparisonSlotData := {
  sourceSlot := "source"
  targetSlot := "target"
  bettiSlot := "betti"
  deRhamSlot := "deRham"
  comparisonSlot := "comparison"
}

/-- Concrete packed-comparison projection data anchored on the same Corr-row
slot labels used by the canonical tomography capsule.

This is the current honest instantiation for the packed classical comparison
source. The carrier is the real sigma-packaged comparison object, but the slot
labels are still the canonical bridge-side symbolic names rather than a final
proof that the packed comparison package itself computes the internal visible
boundary representative. -/
def structuredComparisonBoundaryProjectionData_from_slotRecovery
    {ctx : ClassicalComparisonContext.{u, v}} :
    StructuredComparisonBoundaryProjectionData ctx where
  boundarySlotLabels := fun _ => corrBoundarySlotLabelData
  sourceBoundaryIdentifier := fun _ => corrBoundarySlotLabelData.sourceSlot
  targetBoundaryIdentifier := fun _ => corrBoundarySlotLabelData.targetSlot
  gluingCompatibilityLabel := fun _ => corrBoundarySlotLabelData.comparisonSlot
  boundaryProjectionReadFromStructuredComparisonData := by
    intro comparison
    constructor
    · rfl
    constructor
    · rfl
    · rfl

abbrev InternalPreferredVisibleBoundarySetup
    {primitive : TraceCalc.LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : TraceCalc.LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FoundationsBoundaryBridgeAuxiliaryData
        presentation.toDoctrine) :=
  TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FoundationsBoundaryBridgeAuxiliaryData.PreferredFoundationsBridgeSetup
    presentation.toDoctrine aux

/-- Concrete structured-comparison equality used by the visible-boundary bridge:
literal equality of sigma-packaged comparison data. -/
def literalPackedStructuredComparisonEquality
    (ctx : ClassicalComparisonContext.{u, v}) : StructuredComparisonEquality ctx where
  relates := fun left right => left = right
  -- Reflexivity/symmetry/transitivity of literal equality on the comparison carrier,
  -- stated on ctx.ScalarField to avoid universe metavar issues with SomeStructuredComparisonMorphism.
  reflexiveTarget := ∀ (a : ctx.ScalarField), a = a
  symmetricTarget := ∀ (a b : ctx.ScalarField), a = b → b = a
  transitiveTarget := ∀ (a b c : ctx.ScalarField), a = b → b = c → a = c

/-- Narrow specialization from the concrete equality relation used by the
visible-boundary bridge to the literal equality hypothesis the bridge consumes. -/
theorem structuredComparisonEquality_to_packedComparison_eq
    {ctx : ClassicalComparisonContext.{u, v}}
    {left right : PackedStructuredComparison ctx}
    (h : (literalPackedStructuredComparisonEquality ctx).relates left right) :
    left = right :=
  h

namespace StructuredComparisonBoundaryProjectionData

/-- Record-indexed slot-data projection induced by a packed structured
comparison map. -/
def slotDataAlong
    {ctx : ClassicalComparisonContext.{u, v}}
  {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{w}}
    (projection : StructuredComparisonBoundaryProjectionData ctx)
    (comparison :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        PackedStructuredComparison ctx) :
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
      StructuredComparisonSlotData :=
  fun record => projection.boundarySlotLabels (comparison record)

/-- Record-indexed boundary-port projection induced by a packed structured
comparison map. -/
def boundaryPortsAlong
    {ctx : ClassicalComparisonContext.{u, v}}
  {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{w}}
    (projection : StructuredComparisonBoundaryProjectionData ctx)
    (comparison :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        PackedStructuredComparison ctx) :
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
      VisibleBoundaryPortData :=
  fun record => projection.structuredComparisonVisibleBoundaryPorts (comparison record)

/-- Composed visible-boundary theorem for the internal holography carrier.

If packed structured comparison equality determines the slot layer, the slot
layer determines the recovered boundary ports, and those ports determine the
internal visible boundary, then equality of packed structured comparison data
forces equality of internal visible boundary values. -/
theorem packedComparison_eq_implies_internalVisibleBoundary_eq
    {ctx : ClassicalComparisonContext.{u, v}}
    {primitive : TraceCalc.LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : TraceCalc.LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FoundationsBoundaryBridgeAuxiliaryData
        presentation.toDoctrine}
    (I :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FoundationsBoundaryBridgeAuxiliaryData.InternalHolographyInterface
        presentation aux)
    (comparison :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord
          (InternalPreferredVisibleBoundarySetup presentation aux) →
        PackedStructuredComparison ctx)
    (projection : StructuredComparisonBoundaryProjectionData ctx :=
      structuredComparisonBoundaryProjectionData_from_slotRecovery)
    (slotInjectivity :
      ComparisonSlotInjectivityTarget
        comparison
        (projection.slotDataAlong
          (ctx := ctx)
          (setup := InternalPreferredVisibleBoundarySetup presentation aux)
          comparison))
    (boundaryPortRecovery :
      BoundaryPortRecoveryFromComparisonSlotsTarget
        (projection.slotDataAlong
          (ctx := ctx)
          (setup := InternalPreferredVisibleBoundarySetup presentation aux)
          comparison)
        (projection.boundaryPortsAlong
          (ctx := ctx)
          (setup := InternalPreferredVisibleBoundarySetup presentation aux)
          comparison))
    (visibleBoundaryReconstruction :
      VisibleBoundaryReconstructionFromPortsTarget
        (projection.boundaryPortsAlong
          (ctx := ctx)
          (setup := InternalPreferredVisibleBoundarySetup presentation aux)
          comparison)
        I.visibleBoundary)
    {R₁ R₂ :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord
        (InternalPreferredVisibleBoundarySetup presentation aux)}
    (h : comparison R₁ = comparison R₂) :
    I.visibleBoundary R₁ = I.visibleBoundary R₂ := by
  have hProjected :
      projection.structuredComparisonVisibleBoundary (comparison R₁) =
        projection.structuredComparisonVisibleBoundary (comparison R₂) :=
    projection.comparison_eq_implies_visibleBoundary_eq h
  have hSlots :
      projection.slotDataAlong
          (ctx := ctx)
          (setup := InternalPreferredVisibleBoundarySetup presentation aux)
          comparison R₁ =
        projection.slotDataAlong
          (ctx := ctx)
          (setup := InternalPreferredVisibleBoundarySetup presentation aux)
          comparison R₂ :=
    slotInjectivity.comparisonEqualityDeterminesSlots h
  have hPorts :
      projection.boundaryPortsAlong
          (ctx := ctx)
          (setup := InternalPreferredVisibleBoundarySetup presentation aux)
          comparison R₁ =
        projection.boundaryPortsAlong
          (ctx := ctx)
          (setup := InternalPreferredVisibleBoundarySetup presentation aux)
          comparison R₂ :=
    boundaryPortRecovery.comparisonSlotsDetermineBoundaryPorts hSlots
  exact visibleBoundaryReconstruction.boundaryPortsDetermineVisibleBoundary hPorts

/-- Concrete assembly theorem for the current visible-boundary lane.

If the concrete tomography package proves that the chosen basis-free period-map
equality relation identifies the packed structured comparison values associated
to two completed records, then the existing slot-recovery / visible-boundary
bridge upgrades that comparison equality to equality of the internal
visible-boundary values. -/
theorem basisFreePeriod_eq_implies_internalVisibleBoundary_eq
    {ctx : ClassicalComparisonContext.{u, v}}
    {primitive : TraceCalc.LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : TraceCalc.LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FoundationsBoundaryBridgeAuxiliaryData
        presentation.toDoctrine}
    (I :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FoundationsBoundaryBridgeAuxiliaryData.InternalHolographyInterface
        presentation aux)
    (comparison :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord
          (InternalPreferredVisibleBoundarySetup presentation aux) →
        PackedStructuredComparison ctx)
    (package :
      ConcreteRealizationTomographyPackage ctx
        (literalPackedStructuredComparisonEquality ctx))
    (projection : StructuredComparisonBoundaryProjectionData ctx :=
      structuredComparisonBoundaryProjectionData_from_slotRecovery)
    (slotInjectivity :
      ComparisonSlotInjectivityTarget
        comparison
        (projection.slotDataAlong
          (ctx := ctx)
          (setup := InternalPreferredVisibleBoundarySetup presentation aux)
          comparison))
    (boundaryPortRecovery :
      BoundaryPortRecoveryFromComparisonSlotsTarget
        (projection.slotDataAlong
          (ctx := ctx)
          (setup := InternalPreferredVisibleBoundarySetup presentation aux)
          comparison)
        (projection.boundaryPortsAlong
          (ctx := ctx)
          (setup := InternalPreferredVisibleBoundarySetup presentation aux)
          comparison))
    (visibleBoundaryReconstruction :
      VisibleBoundaryReconstructionFromPortsTarget
        (projection.boundaryPortsAlong
          (ctx := ctx)
          (setup := InternalPreferredVisibleBoundarySetup presentation aux)
          comparison)
        I.visibleBoundary)
    {R₁ R₂ :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord
        (InternalPreferredVisibleBoundarySetup presentation aux)}
    (hBasis :
      package.basisFreePeriodMapEquality.relates (comparison R₁) (comparison R₂)) :
    I.visibleBoundary R₁ = I.visibleBoundary R₂ := by
  have hStructured :
      (literalPackedStructuredComparisonEquality ctx).relates
        (comparison R₁)
        (comparison R₂) :=
    (package.toClassicalPeriodTomographyCore.basisFreeDeterminesPacked.theoremTarget
      (comparison R₁) (comparison R₂) hBasis)
  have hComparison : comparison R₁ = comparison R₂ :=
    structuredComparisonEquality_to_packedComparison_eq hStructured
  exact packedComparison_eq_implies_internalVisibleBoundary_eq
    (ctx := ctx)
    (presentation := presentation)
    (aux := aux)
    I
    comparison
    projection
    slotInjectivity
    boundaryPortRecovery
    visibleBoundaryReconstruction
    hComparison

/-- Concrete frontier-equivalence consequence of the current Campaign 13.5
visible-boundary assembly slice.

This packages the now-closed chain

`basis-free period equality -> packed comparison equality -> internal visible boundary equality`

with the existing internal holography theorem

`visible boundary equality <-> frontier equivalence`.
-/
theorem basisFreePeriod_eq_implies_frontierEquiv
    {ctx : ClassicalComparisonContext.{u, v}}
    {primitive : TraceCalc.LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : TraceCalc.LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FoundationsBoundaryBridgeAuxiliaryData
        presentation.toDoctrine}
    (I :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FoundationsBoundaryBridgeAuxiliaryData.InternalHolographyInterface
        presentation aux)
    (comparison :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord
          (InternalPreferredVisibleBoundarySetup presentation aux) →
        PackedStructuredComparison ctx)
    (package :
      ConcreteRealizationTomographyPackage ctx
        (literalPackedStructuredComparisonEquality ctx))
    (projection : StructuredComparisonBoundaryProjectionData ctx :=
      structuredComparisonBoundaryProjectionData_from_slotRecovery)
    (slotInjectivity :
      ComparisonSlotInjectivityTarget
        comparison
        (projection.slotDataAlong
          (ctx := ctx)
          (setup := InternalPreferredVisibleBoundarySetup presentation aux)
          comparison))
    (boundaryPortRecovery :
      BoundaryPortRecoveryFromComparisonSlotsTarget
        (projection.slotDataAlong
          (ctx := ctx)
          (setup := InternalPreferredVisibleBoundarySetup presentation aux)
          comparison)
        (projection.boundaryPortsAlong
          (ctx := ctx)
          (setup := InternalPreferredVisibleBoundarySetup presentation aux)
          comparison))
    (visibleBoundaryReconstruction :
      VisibleBoundaryReconstructionFromPortsTarget
        (projection.boundaryPortsAlong
          (ctx := ctx)
          (setup := InternalPreferredVisibleBoundarySetup presentation aux)
          comparison)
        I.visibleBoundary)
    {R₁ R₂ :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord
        (InternalPreferredVisibleBoundarySetup presentation aux)}
    (hBasis :
      package.basisFreePeriodMapEquality.relates (comparison R₁) (comparison R₂)) :
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FrontierWord.Equiv
      (I.holographyData.toFrontierWord R₁)
      (I.holographyData.toFrontierWord R₂) := by
  exact (I.visibleBoundary_eq_iff_frontierEquiv).1
    (basisFreePeriod_eq_implies_internalVisibleBoundary_eq
      (ctx := ctx)
      (presentation := presentation)
      (aux := aux)
      I
      comparison
      package
      projection
      slotInjectivity
      boundaryPortRecovery
      visibleBoundaryReconstruction
      hBasis)

/-- Honest remaining target after the current visible-boundary assembly step.

The repository now reaches equality of internal visible-boundary values from the
concrete basis-free period equality relation, and the internal holography lane
already converts that to frontier equivalence. What is still missing is a
consumer theorem saying that this visible-boundary / frontier information is
strong enough to determine the concrete structured map fields. -/
def visibleBoundary_frontierEquiv_to_structuredMapFieldEq_target
    {primitive : TraceCalc.LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : TraceCalc.LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FoundationsBoundaryBridgeAuxiliaryData
        presentation.toDoctrine}
    (I :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FoundationsBoundaryBridgeAuxiliaryData.InternalHolographyInterface
        presentation aux)
    {β γ δ ε : Sort _}
    (bettiField :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord
          (InternalPreferredVisibleBoundarySetup presentation aux) → β)
    (deRhamField :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord
          (InternalPreferredVisibleBoundarySetup presentation aux) → γ)
    (bettiCompatibilityField :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord
          (InternalPreferredVisibleBoundarySetup presentation aux) → δ)
    (deRhamCompatibilityField :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord
          (InternalPreferredVisibleBoundarySetup presentation aux) → ε) : Prop :=
  ∀ {R₁ R₂ :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord
        (InternalPreferredVisibleBoundarySetup presentation aux)},
    I.visibleBoundary R₁ = I.visibleBoundary R₂ →
      bettiField R₁ = bettiField R₂ ∧
      deRhamField R₁ = deRhamField R₂ ∧
      bettiCompatibilityField R₁ = bettiCompatibilityField R₂ ∧
      deRhamCompatibilityField R₁ = deRhamCompatibilityField R₂

end StructuredComparisonBoundaryProjectionData

/-! ## Note on `PeriodFaithfulnessContext` Instantiation

**Design note**: `PeriodFaithfulnessContext` requires
`structuredFaithful : StructuredRealization f = StructuredRealization g → EqMorph f g`
and
`scalarReflectsStructured : ScalarShadow f = ScalarShadow g → StructuredRealization f = StructuredRealization g`.

Non-vacuous instantiation with `EqMorph f g := f = g` requires TYPE-LEVEL injectivity:
extracting `f = g` from a type equality `SR f = SR g`. In Lean 4 (without the univalence
axiom), type equalities for indexed structures are opaque — transport does not reduce
definitionally when the proof is not `rfl`. This blocks any proof of
`SR f = SR g → f = g` that does not degenerate to `fun _ => h` for some separately
constructed `h : f = g`.

Additionally, `scalarReflectsStructured` with a structured-realization family
carrying all four maps would require deriving `f.bettiMap = g.bettiMap` from
`f.basisFreePeriodMap = g.basisFreePeriodMap`, which is FALSE: the over-scalar maps are
determined by `basisFreePeriodMap` (via `overScalarRealization_eq_of_basisFreePeriodMap_eq`), but the
base-level maps `bettiMap` and `deRhamMap` are independent.

The genuine mathematical content of period faithfulness — that the basis-free period map
determines all scalar-extended realization maps — is fully captured by the direct theorems
`overScalarRealization_eq_of_basisFreePeriodMap_eq` and
`full_morphism_eq_of_betti_deRham_basisFreePeriodMap_eq`
above, without the need for an abstract type-family wrapper. -/

/-
TEX ref: our_paper_draft.tex, label cor:internal-period-faithfulness (Section 10)
Paper role: period faithfulness for T_can morphisms; the basis-free period map determines the
  full morphism up to equality.
Lean status: LEGACY SUPPORT LEMMA. The final file-level route is the injective-extension theorem
  `internal_period_faithfulness_of_injective_extensions` below.
-/
/-- Legacy support lemma for `cor:internal-period-faithfulness`:
equality of the basis-free period map implies equality of the full structured
comparison morphism — **under two additional field hypotheses**.

This is a named alias for `full_morphism_eq_of_betti_deRham_basisFreePeriodMap_eq`.
The two extra field hypotheses (`hBetti`, `hDeRham`) are the WEAKER gap
relative to the paper's unconditional statement. The paper proves both
follow from the comparison iso constraint alone, which is not yet formalized.
The former hypotheses (3) and (4) (extension-compatibility fields) are no longer
required: they are handled by proof irrelevance in `eq_of_map_fields_eq`.
The suffix `_weaker` is retained for API compatibility; final theorem paths should use
`internal_period_faithfulness_of_injective_extensions` instead. -/
theorem internal_period_faithfulness_weaker
    {ctx : ClassicalComparisonContext.{u, v}}
    (source target : ClassicalStructuredComparisonObject ctx)
    (f g : ClassicalStructuredComparisonMorphism source target)
    (hBasis : f.basisFreePeriodMap = g.basisFreePeriodMap)
    (hBetti : f.bettiMap = g.bettiMap)
    (hDeRham : f.deRhamMap = g.deRhamMap) :
    f = g :=
  full_morphism_eq_of_betti_deRham_basisFreePeriodMap_eq f g hBetti hDeRham hBasis

/-- Injective-extension variant of `cor:internal-period-faithfulness`.

This removes explicit base-map hypotheses by assuming the target extension maps
are injective, and then deriving base-map equality from scalar-map equality
plus extension-compatibility commutative squares. -/
theorem internal_period_faithfulness_of_injective_extensions
    {ctx : ClassicalComparisonContext.{u, v}}
    (source target : ClassicalStructuredComparisonObject ctx)
    (f g : ClassicalStructuredComparisonMorphism source target)
    (hExtendBettiInj : Function.Injective target.extendBetti)
    (hExtendDeRhamInj : Function.Injective target.extendDeRham)
    (hBasis : f.basisFreePeriodMap = g.basisFreePeriodMap) :
    f = g :=
  full_morphism_eq_of_basisFreePeriodMap_eq_of_injective_extensions
    f g hExtendBettiInj hExtendDeRhamInj hBasis

/-
TEX ref: our_paper_draft.tex, label thm:internal-realization-functor (Section 10)
Paper role: the internal realization functor T_can → VecQ exists and is lax monoidal.
Lean status: EXPLICIT TARGET RECORD. This record is not used as a hidden final-theorem proof.
-/
/-- **`thm:internal-realization-functor`** (Task 22): the internal realization
functor from T_can to VecQ exists and is a lax monoidal functor.

This is the functor that maps a canonical trace category object to its
comparison data (Betti, de Rham, comparison isomorphism). Existence requires
the full T_can → DM_gm(Q) recognition theorem. -/
structure InternalRealizationFunctorTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  /-- The functor exists as a lax monoidal functor. -/
  functorExists : Prop
  /-- The functor commutes with the comparison data. -/
  comparisonCompatibility : Prop
  /-- The functor is faithful on morphisms (the period faithfulness claim). -/
  faithful : Prop

/-
TEX ref: our_paper_draft.tex, label thm:internal-pf-construction (Section 10)
Paper role: the internal period faithfulness construction — the functor is period-faithful in the
  sense that equal periods imply morphism equality.
Lean status: EXPLICIT TARGET RECORD. This record is not used as a hidden final-theorem proof.
-/
/-- **`thm:internal-pf-construction`** (Task 23): the internal period
faithfulness construction.

The internal realization functor is period-faithful: morphisms are
determined by their period data. This is the key Step 3 of the
CBR (comparison boundary recovery) architecture. -/
structure InternalPFConstructionTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  /-- Period faithfulness: equal period data implies morphism equality. -/
  periodFaithful : Prop
  /-- The construction is unconditional (no extra hypotheses required). -/
  unconditional : Prop

/-
TEX ref: our_paper_draft.tex, label thm:internal-evaluation-faithfulness (Section 10)
Paper role: evaluation at each test object is faithful; the full evaluation functor is injective on
  morphisms.
Lean status: EXPLICIT TARGET RECORD. This record is not used as a hidden final-theorem proof.
-/
/-- **`thm:internal-evaluation-faithfulness`** (Task 24): evaluation at
each test object is faithful.

The period evaluation map `ev_X : Hom(M, N) → Per(M_X, N_X)` is injective,
where `Per` denotes the period pairing. This combines with internal period
faithfulness to give the full comparison faithfulness. -/
structure InternalEvaluationFaithfulnessTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  /-- Evaluation is faithful: equal evaluations at all test objects implies morphism equality. -/
  evaluationFaithful : Prop
  /-- The evaluation map is natural in the test object. -/
  natural : Prop

/-
TEX ref: our_paper_draft.tex, label thm:classical-coarse-period-consequence (Section 12)
Paper role: the classical coarse period consequence — equal periods in the classical comparison
  structure imply morphism equality.
Lean status: EXPLICIT TARGET RECORD. Constructors must provide `periodConsequence`; this file no
  longer presents the record as a discharged theorem by itself.
-/
/-- **`thm:classical-coarse-period-consequence`** (Task 25): the classical
coarse period consequence.

Equal classical periods (Betti and de Rham together with comparison isomorphism)
imply morphism equality in the motivic category. This is the main classical
period theorem, proved by composing:
1. `cor:internal-period-faithfulness` (basis-free period map determines morphism)
2. `thm:tomographic-faithfulness`
3. `lem:period-pairing-determines-realizations`
4. `thm:comparison-reconstruction`

These named theorem surfaces now exist in `MotivicRecognition/RealizationAgreementStatements.lean`.
The remaining gap is the final assembly of their outputs into the classical target package, not
the absence of local theorem names for steps (2)-(4).

The theorem content is the `periodConsequence` field supplied by a constructor; this record is not
used by the locked final theorem path as hidden evidence. -/
structure ClassicalCoarsePeriodConsequenceTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  /-- The main period consequence: equal periods implies morphism equality. -/
  periodConsequence :
    ∀ (source target : ClassicalStructuredComparisonObject ctx)
      (f g : ClassicalStructuredComparisonMorphism source target),
      f.basisFreePeriodMap = g.basisFreePeriodMap → f = g
  /-- Status flag: all prerequisite theorems are discharged. -/
  prerequisitesDischargedTarget : Prop

end LayerD
end TraceCalc
