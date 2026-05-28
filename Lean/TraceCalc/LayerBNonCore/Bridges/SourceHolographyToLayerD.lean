import TraceCalc.LayerBNonCore.Interfaces.TraceEnvelope
import TraceCalc.LayerB.RealObjects.ConcreteBoundaryPresentation
import TraceCalc.LayerC.RealObjects.ConcreteExternalOutSort
import TraceCalc.LayerB.RealObjects.CanonicalNormalForm
import TraceCalc.LayerBNonCore.Targets.InternalManuscriptTargets
import TraceCalc.LayerB.RealObjects.Replay
import TraceCalc.LayerA.CategoryInfra.Localization
import TraceCalc.LayerD.SourceTracePackage

open CategoryTheory

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup
namespace FoundationsBoundaryBridgeAuxiliaryData

open CompletedReconstructionRecord
open CompletedReconstructionRecord.PeelChain

/-- Concrete source-side objects and maps that the Layer B -> Layer D bridge
must eventually supply. This isolates the actual source-category choices from
the remaining theorem-sized coherence obligations. -/
structure LayerBConcreteSourceData
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine) where
  Syntax : Type _
  Envelope : Type _
  Localized : Type _
  [catEnvelope : Category Envelope]
  [catLocalized : Category Localized]
  includeSyntax : Syntax → Envelope
  weakEquivalence : ∀ {X Y : Envelope}, (X ⟶ Y) → Prop
  localizeObj : Envelope → Localized
  localizationInterface : CategoryInfra.LocalizationInterface

attribute [instance] LayerBConcreteSourceData.catEnvelope LayerBConcreteSourceData.catLocalized

/-- Named theorem target for matching the abstract localization interface with
the concrete source-side localization data. This isolates the exact seam fact
still needed from Layer B: source/target category alignment together with
identification of the weak-equivalence relation and localization object map. -/
structure LayerBLocalizationMatchesTheorem
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceData : LayerBConcreteSourceData presentation aux) where
  sourceCategoryAlignment : sourceData.localizationInterface.C = sourceData.Envelope
  targetCategoryAlignment : sourceData.localizationInterface.D = sourceData.Localized
  weakEquivalenceAlignment : HEq sourceData.localizationInterface.W sourceData.weakEquivalence
  localizeObjAlignment : HEq sourceData.localizationInterface.QObj sourceData.localizeObj

namespace LayerBLocalizationMatchesTheorem

/-- Build the localization-seam theorem object from the four explicit alignment
facts carried by a concrete localization presentation. -/
def ofConcreteAlignment
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {sourceData : LayerBConcreteSourceData presentation aux}
    (sourceCategoryAlignment : sourceData.localizationInterface.C = sourceData.Envelope)
    (targetCategoryAlignment : sourceData.localizationInterface.D = sourceData.Localized)
  (weakEquivalenceAlignment : HEq sourceData.localizationInterface.W sourceData.weakEquivalence)
  (localizeObjAlignment : HEq sourceData.localizationInterface.QObj sourceData.localizeObj) :
    LayerBLocalizationMatchesTheorem sourceData where
  sourceCategoryAlignment := sourceCategoryAlignment
  targetCategoryAlignment := targetCategoryAlignment
  weakEquivalenceAlignment := weakEquivalenceAlignment
  localizeObjAlignment := localizeObjAlignment

/- There is no honest generic `ofDefeq` constructor here. The bridge stores
`localizationInterface`, `weakEquivalence`, and `localizeObj` as independent
fields, so definitional equality of the source and target categories alone does
not force definitional equality of `W` with `weakEquivalence` or `QObj` with
`localizeObj`. In concrete cases where all four alignments are definitionally
equal, use `ofConcreteAlignment rfl rfl HEq.rfl HEq.rfl`. -/

end LayerBLocalizationMatchesTheorem

/-- First coherence cluster sitting directly on top of the concrete source-side
objects. The universal-property field is not repeated here because it is
already a field of `LocalizationInterface`. -/
structure LayerBLocalizationInterfaceData
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceData : LayerBConcreteSourceData presentation aux) where
  localizationMatchesTheorem : LayerBLocalizationMatchesTheorem sourceData
  localizationLaws : CategoryInfra.LocalizationInterfaceLaws sourceData.localizationInterface

/-- Symmetric-monoidal source witness cluster, isolated so the remaining source
construction witness fields can be retired one cluster at a time. -/
structure LayerBSymmetricMonoidalWitness
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (_sourceData : LayerBConcreteSourceData presentation aux) where
  symmetricMonoidalPiZero : Prop
  symmetricMonoidalPiZero_holds : symmetricMonoidalPiZero
  symmetricMonoidalInfinity : Prop
  symmetricMonoidalInfinity_holds : symmetricMonoidalInfinity

/-- Symmetric-monoidal theorem surface specialized to the real
`LayerB.MotivicLocalization` carrier. This keeps the monoidal obligations
explicit instead of pretending they follow definitionally from localization
alignment. -/
structure MotivicLocalizationSymmetricMonoidalWitness
    (ML : LayerB.MotivicLocalization) where
  symmetricMonoidalPiZero : Prop
  symmetricMonoidalPiZero_holds : symmetricMonoidalPiZero
  symmetricMonoidalInfinity : Prop
  symmetricMonoidalInfinity_holds : symmetricMonoidalInfinity

/-- Stable/triangulated source witness cluster, isolated so the remaining
source-construction witness fields can be retired one cluster at a time. -/
structure LayerBStableTriangulatedWitness
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (_sourceData : LayerBConcreteSourceData presentation aux) where
  triangulatedStablePiZero : Prop
  triangulatedStablePiZero_holds : triangulatedStablePiZero
  triangulatedStableInfinity : Prop
  triangulatedStableInfinity_holds : triangulatedStableInfinity

/-- Stable/triangulated theorem surface specialized to the real
`LayerB.MotivicLocalization` carrier. -/
structure MotivicLocalizationStableTriangulatedWitness
    (ML : LayerB.MotivicLocalization) where
  triangulatedStablePiZero : Prop
  triangulatedStablePiZero_holds : triangulatedStablePiZero
  triangulatedStableInfinity : Prop
  triangulatedStableInfinity_holds : triangulatedStableInfinity

/-- Named theorem ticket for the pi0 A1-invariance target on the Layer B
source side. This isolates the exact missing theorem target from the rest of
the local-geometry witness bundle. -/
structure LayerBA1InvariancePiZeroTicket where
  theoremTarget : Prop
  theoremTarget_holds : theoremTarget

/-- Named theorem ticket for the pi0 localization target on the Layer B
source side. This isolates the exact missing theorem target from the rest of
the local-geometry witness bundle. -/
structure LayerBLocalizationPiZeroTicket where
  verdierLocalizationPiZeroShadow : Prop
  verdierLocalizationPiZeroShadow_holds : verdierLocalizationPiZeroShadow

namespace LayerBLocalizationPiZeroTicket

/-- Build the pi0 localization ticket from an explicit triangulated-shadow
theorem target for a localization interface. This remains separate from the
infinity-side universal-property witness because the truncation step is an
additional theorem, not definitional fallout from the infinity statement. -/
def ofLocalizationPiZeroShadowTheorem
    {L : CategoryInfra.LocalizationInterface}
    (piZeroShadowTheorem : CategoryInfra.LocalizationPiZeroShadowTheorem L) :
    LayerBLocalizationPiZeroTicket where
  verdierLocalizationPiZeroShadow :=
    Nonempty (CategoryInfra.LocalizationPiZeroShadowTheorem L)
  verdierLocalizationPiZeroShadow_holds :=
    ⟨piZeroShadowTheorem⟩

end LayerBLocalizationPiZeroTicket

/-- Named theorem ticket for the infinity-side A1-invariance target on the
Layer B source side. This isolates the exact missing theorem target from the
rest of the local-geometry witness bundle. -/
structure LayerBA1InvarianceInfinityTicket where
  a1InvarianceInfinity : Prop
  a1InvarianceInfinity_holds : a1InvarianceInfinity

/-- Named theorem ticket for the infinity-side localization target on the
Layer B source side. This isolates the exact missing theorem target from the
rest of the local-geometry witness bundle. -/
structure LayerBLocalizationInfinityTicket where
  localizationUniversalPropertyInfinity : Prop
  localizationUniversalPropertyInfinity_holds : localizationUniversalPropertyInfinity

namespace LayerBLocalizationInfinityTicket

/-- Build the infinity-side localization ticket from explicit proof-relevant
universal-property data for a localization interface. -/
def ofLocalizationUniversalPropertyData
    {L : CategoryInfra.LocalizationInterface}
    (universalPropertyData : CategoryInfra.LocalizationUniversalPropertyData L) :
    LayerBLocalizationInfinityTicket where
  localizationUniversalPropertyInfinity :=
    Nonempty (CategoryInfra.LocalizationUniversalPropertyData L)
  localizationUniversalPropertyInfinity_holds :=
    ⟨universalPropertyData⟩

end LayerBLocalizationInfinityTicket

/-- Named theorem ticket for the pi0-side Nisnevich-descent target on the
Layer B source side. This isolates the exact missing theorem target from the
rest of the local-geometry witness bundle. -/
structure LayerBNisnevichDescentPiZeroTicket where
  nisnevichDescentPiZero : Prop
  nisnevichDescentPiZero_holds : nisnevichDescentPiZero

/-- Named theorem ticket for the infinity-side Nisnevich-descent target on the
Layer B source side. This isolates the exact missing theorem target from the
rest of the local-geometry witness bundle. -/
structure LayerBNisnevichDescentInfinityTicket where
  nisnevichDescentInfinity : Prop
  nisnevichDescentInfinity_holds : nisnevichDescentInfinity

/-- Local-geometry source witness cluster, isolating the A1, Nisnevich, and
localization theorem targets at both the pi0 and infinity levels. -/
structure LayerBLocalGeometryWitness
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (_sourceData : LayerBConcreteSourceData presentation aux) where
  a1InvariancePiZeroTicket : LayerBA1InvariancePiZeroTicket
  a1InvarianceInfinityTicket : LayerBA1InvarianceInfinityTicket
  nisnevichDescentPiZeroTicket : LayerBNisnevichDescentPiZeroTicket
  nisnevichDescentInfinityTicket : LayerBNisnevichDescentInfinityTicket
  localizationPiZeroTicket : LayerBLocalizationPiZeroTicket
  localizationInfinityTicket : LayerBLocalizationInfinityTicket

/-- Local-geometry theorem surface specialized to the real
`LayerB.MotivicLocalization` carrier. The ticket objects remain explicit named
targets rather than being collapsed into generic propositions. -/
structure MotivicLocalizationLocalGeometryWitness
    (ML : LayerB.MotivicLocalization) where
  a1InvariancePiZeroTicket : LayerBA1InvariancePiZeroTicket
  a1InvarianceInfinityTicket : LayerBA1InvarianceInfinityTicket
  nisnevichDescentPiZeroTicket : LayerBNisnevichDescentPiZeroTicket
  nisnevichDescentInfinityTicket : LayerBNisnevichDescentInfinityTicket
  localizationPiZeroTicket : LayerBLocalizationPiZeroTicket
  localizationInfinityTicket : LayerBLocalizationInfinityTicket

/-- Tate source witness cluster, isolating the remaining Tate-stabilization
theorem targets at both the pi0 and infinity levels. -/
structure LayerBTateWitness
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (_sourceData : LayerBConcreteSourceData presentation aux) where
  tateStabilizationPiZero : Prop
  tateStabilizationPiZero_holds : tateStabilizationPiZero
  tateStabilizationInfinity : Prop
  tateStabilizationInfinity_holds : tateStabilizationInfinity

/-- Tate theorem surface specialized to the real `LayerB.MotivicLocalization`
carrier. -/
structure MotivicLocalizationTateWitness
    (ML : LayerB.MotivicLocalization) where
  tateStabilizationPiZero : Prop
  tateStabilizationPiZero_holds : tateStabilizationPiZero
  tateStabilizationInfinity : Prop
  tateStabilizationInfinity_holds : tateStabilizationInfinity

/-- Real Layer B candidate for the source/localization bridge: an existing
`LayerB.MotivicLocalization` now supplies the syntax carrier, envelope,
localized target, stable-like data on both sides, localization object map,
weak-equivalence relation, abstract localization interface, and the alignment
theorems needed to build the bridge localization seam. -/
def layerBConcreteSourceDataCandidate
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
  (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
  (ML : LayerB.MotivicLocalization) : LayerBConcreteSourceData presentation aux where
  Syntax := ML.F.Syntax
  Envelope := ML.F.Envelope
  Localized := ML.Loc
  includeSyntax := ML.F.includeSyntax
  weakEquivalence := ML.motivicWeakEq
  localizeObj := ML.localizeObj
  localizationInterface := ML.localization

/-- The source-category alignment for the concrete Layer B localization
candidate is already exported by `LayerB.MotivicLocalization.localization_matches`. -/
theorem layerBConcreteSourceDataCandidate_sourceCategoryAlignment
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (ML : LayerB.MotivicLocalization) :
    (layerBConcreteSourceDataCandidate presentation aux ML).localizationInterface.C =
      (layerBConcreteSourceDataCandidate presentation aux ML).Envelope :=
  ML.sourceCategoryAlignment

/-- The target-category alignment for the concrete Layer B localization
candidate is already exported by `LayerB.MotivicLocalization.localization_matches`. -/
theorem layerBConcreteSourceDataCandidate_targetCategoryAlignment
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (ML : LayerB.MotivicLocalization) :
    (layerBConcreteSourceDataCandidate presentation aux ML).localizationInterface.D =
      (layerBConcreteSourceDataCandidate presentation aux ML).Localized :=
  ML.targetCategoryAlignment

/-- The strengthened `LayerB.MotivicLocalization` carrier now supplies the full
localization-seam theorem needed by the bridge candidate unconditionally. -/
def layerBConcreteSourceDataCandidate_localizationMatchesTheorem
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (ML : LayerB.MotivicLocalization) :
    LayerBLocalizationMatchesTheorem
      (layerBConcreteSourceDataCandidate presentation aux ML) :=
  LayerBLocalizationMatchesTheorem.ofConcreteAlignment
    (sourceData := layerBConcreteSourceDataCandidate presentation aux ML)
    (layerBConcreteSourceDataCandidate_sourceCategoryAlignment
      presentation aux ML)
    (layerBConcreteSourceDataCandidate_targetCategoryAlignment
      presentation aux ML)
    ML.weakEquivalence_alignment
    ML.localizeObj_alignment

/-- The localization-data wrapper is now derivable from the strengthened
`LayerB.MotivicLocalization` carrier for the concrete bridge candidate. -/
def layerBConcreteSourceDataCandidate_localizationInterfaceData
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (ML : LayerB.MotivicLocalization) :
    LayerBLocalizationInterfaceData (layerBConcreteSourceDataCandidate presentation aux ML) where
  localizationMatchesTheorem :=
    layerBConcreteSourceDataCandidate_localizationMatchesTheorem presentation aux ML
  localizationLaws := ML.localizationLaws

/-- Assemble the abstract Layer D source-trace package from concrete source-side
objects together with the first coherence and witness clusters. -/
def LayerBConcreteSourceData.toSourceTracePackage
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceData : LayerBConcreteSourceData presentation aux)
    (localizationData : LayerBLocalizationInterfaceData sourceData)
    (symmetricMonoidalWitness : LayerBSymmetricMonoidalWitness sourceData)
    (stableTriangulatedWitness : LayerBStableTriangulatedWitness sourceData)
    (localGeometryWitness : LayerBLocalGeometryWitness sourceData)
    (tateWitness : LayerBTateWitness sourceData) :
    LayerD.SourceTracePackage where
  Syntax := sourceData.Syntax
  Envelope := sourceData.Envelope
  Localized := sourceData.Localized
  includeSyntax := sourceData.includeSyntax
  weakEquivalence := sourceData.weakEquivalence
  localizeObj := sourceData.localizeObj
  localizationInterface := sourceData.localizationInterface
  localization_matches :=
    ⟨localizationData.localizationMatchesTheorem.sourceCategoryAlignment,
      localizationData.localizationMatchesTheorem.targetCategoryAlignment⟩
  localizationCompatibility :=
    { sourceCategoryAlignment :=
        localizationData.localizationMatchesTheorem.sourceCategoryAlignment
      targetCategoryAlignment :=
        localizationData.localizationMatchesTheorem.targetCategoryAlignment
      localizeObjAlignment := by
        cases localizationData.localizationMatchesTheorem.sourceCategoryAlignment
        cases localizationData.localizationMatchesTheorem.targetCategoryAlignment
        simpa using
          eq_of_heq localizationData.localizationMatchesTheorem.localizeObjAlignment
      localizationMapId := localizationData.localizationLaws.map_id
      localizationMapComp := localizationData.localizationLaws.map_comp }
  symmetricMonoidalPiZero := symmetricMonoidalWitness.symmetricMonoidalPiZero
  symmetricMonoidalPiZero_holds := symmetricMonoidalWitness.symmetricMonoidalPiZero_holds
  symmetricMonoidalInfinity := symmetricMonoidalWitness.symmetricMonoidalInfinity
  symmetricMonoidalInfinity_holds := symmetricMonoidalWitness.symmetricMonoidalInfinity_holds
  triangulatedStablePiZero := stableTriangulatedWitness.triangulatedStablePiZero
  triangulatedStablePiZero_holds := stableTriangulatedWitness.triangulatedStablePiZero_holds
  triangulatedStableInfinity := stableTriangulatedWitness.triangulatedStableInfinity
  triangulatedStableInfinity_holds := stableTriangulatedWitness.triangulatedStableInfinity_holds
  a1InvariancePiZero := localGeometryWitness.a1InvariancePiZeroTicket.theoremTarget
  a1InvariancePiZero_holds := localGeometryWitness.a1InvariancePiZeroTicket.theoremTarget_holds
  a1InvarianceInfinity := localGeometryWitness.a1InvarianceInfinityTicket.a1InvarianceInfinity
  a1InvarianceInfinity_holds := localGeometryWitness.a1InvarianceInfinityTicket.a1InvarianceInfinity_holds
  nisnevichDescentPiZero := localGeometryWitness.nisnevichDescentPiZeroTicket.nisnevichDescentPiZero
  nisnevichDescentPiZero_holds := localGeometryWitness.nisnevichDescentPiZeroTicket.nisnevichDescentPiZero_holds
  nisnevichDescentInfinity := localGeometryWitness.nisnevichDescentInfinityTicket.nisnevichDescentInfinity
  nisnevichDescentInfinity_holds := localGeometryWitness.nisnevichDescentInfinityTicket.nisnevichDescentInfinity_holds
  localizationPiZero := localGeometryWitness.localizationPiZeroTicket.verdierLocalizationPiZeroShadow
  localizationPiZero_holds := localGeometryWitness.localizationPiZeroTicket.verdierLocalizationPiZeroShadow_holds
  localizationInfinity := localGeometryWitness.localizationInfinityTicket.localizationUniversalPropertyInfinity
  localizationInfinity_holds := localGeometryWitness.localizationInfinityTicket.localizationUniversalPropertyInfinity_holds
  tateStabilizationPiZero := tateWitness.tateStabilizationPiZero
  tateStabilizationPiZero_holds := tateWitness.tateStabilizationPiZero_holds
  tateStabilizationInfinity := tateWitness.tateStabilizationInfinity
  tateStabilizationInfinity_holds := tateWitness.tateStabilizationInfinity_holds

namespace MotivicLocalizationSymmetricMonoidalWitness

/-- Repackage the motivic-localization-specific symmetric-monoidal theorem
surface as the generic Layer B bridge witness for the concrete candidate path. -/
def toLayerBSymmetricMonoidalWitness
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {ML : LayerB.MotivicLocalization}
    (witness : MotivicLocalizationSymmetricMonoidalWitness ML) :
    LayerBSymmetricMonoidalWitness
      (layerBConcreteSourceDataCandidate presentation aux ML) where
  symmetricMonoidalPiZero := witness.symmetricMonoidalPiZero
  symmetricMonoidalPiZero_holds := witness.symmetricMonoidalPiZero_holds
  symmetricMonoidalInfinity := witness.symmetricMonoidalInfinity
  symmetricMonoidalInfinity_holds := witness.symmetricMonoidalInfinity_holds

/-- The candidate-path repackaging keeps the symmetric-monoidal proposition
surface unchanged. -/
theorem toLayerBSymmetricMonoidalWitness_preserves_fields
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {ML : LayerB.MotivicLocalization}
    (witness : MotivicLocalizationSymmetricMonoidalWitness ML) :
    let repackaged :=
      MotivicLocalizationSymmetricMonoidalWitness.toLayerBSymmetricMonoidalWitness
        (presentation := presentation) (aux := aux) witness
    repackaged.symmetricMonoidalPiZero = witness.symmetricMonoidalPiZero ∧
      repackaged.symmetricMonoidalInfinity = witness.symmetricMonoidalInfinity := by
  exact ⟨rfl, rfl⟩

end MotivicLocalizationSymmetricMonoidalWitness

namespace MotivicLocalizationStableTriangulatedWitness

/-- Repackage the motivic-localization-specific stable/triangulated theorem
surface as the generic Layer B bridge witness for the concrete candidate path. -/
def toLayerBStableTriangulatedWitness
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {ML : LayerB.MotivicLocalization}
    (witness : MotivicLocalizationStableTriangulatedWitness ML) :
    LayerBStableTriangulatedWitness
      (layerBConcreteSourceDataCandidate presentation aux ML) where
  triangulatedStablePiZero := witness.triangulatedStablePiZero
  triangulatedStablePiZero_holds := witness.triangulatedStablePiZero_holds
  triangulatedStableInfinity := witness.triangulatedStableInfinity
  triangulatedStableInfinity_holds := witness.triangulatedStableInfinity_holds

/-- The candidate-path repackaging keeps the stable/triangulated proposition
surface unchanged. -/
theorem toLayerBStableTriangulatedWitness_preserves_fields
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {ML : LayerB.MotivicLocalization}
    (witness : MotivicLocalizationStableTriangulatedWitness ML) :
    let repackaged :=
      MotivicLocalizationStableTriangulatedWitness.toLayerBStableTriangulatedWitness
        (presentation := presentation) (aux := aux) witness
    repackaged.triangulatedStablePiZero = witness.triangulatedStablePiZero ∧
      repackaged.triangulatedStableInfinity = witness.triangulatedStableInfinity := by
  exact ⟨rfl, rfl⟩

end MotivicLocalizationStableTriangulatedWitness

namespace MotivicLocalizationLocalGeometryWitness

/-- Repackage the motivic-localization-specific local-geometry theorem surface
as the generic Layer B bridge witness for the concrete candidate path. -/
def toLayerBLocalGeometryWitness
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {ML : LayerB.MotivicLocalization}
    (witness : MotivicLocalizationLocalGeometryWitness ML) :
    LayerBLocalGeometryWitness
      (layerBConcreteSourceDataCandidate presentation aux ML) where
  a1InvariancePiZeroTicket := witness.a1InvariancePiZeroTicket
  a1InvarianceInfinityTicket := witness.a1InvarianceInfinityTicket
  nisnevichDescentPiZeroTicket := witness.nisnevichDescentPiZeroTicket
  nisnevichDescentInfinityTicket := witness.nisnevichDescentInfinityTicket
  localizationPiZeroTicket := witness.localizationPiZeroTicket
  localizationInfinityTicket := witness.localizationInfinityTicket

/-- The candidate-path repackaging keeps the local-geometry ticket surface
unchanged. -/
theorem toLayerBLocalGeometryWitness_preserves_fields
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {ML : LayerB.MotivicLocalization}
    (witness : MotivicLocalizationLocalGeometryWitness ML) :
    let repackaged :=
      MotivicLocalizationLocalGeometryWitness.toLayerBLocalGeometryWitness
        (presentation := presentation) (aux := aux) witness
    repackaged.a1InvariancePiZeroTicket = witness.a1InvariancePiZeroTicket ∧
      repackaged.a1InvarianceInfinityTicket = witness.a1InvarianceInfinityTicket ∧
      repackaged.nisnevichDescentPiZeroTicket = witness.nisnevichDescentPiZeroTicket ∧
      repackaged.nisnevichDescentInfinityTicket = witness.nisnevichDescentInfinityTicket ∧
      repackaged.localizationPiZeroTicket = witness.localizationPiZeroTicket ∧
      repackaged.localizationInfinityTicket = witness.localizationInfinityTicket := by
  exact ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, rfl⟩⟩⟩⟩⟩

end MotivicLocalizationLocalGeometryWitness

namespace MotivicLocalizationTateWitness

/-- Repackage the motivic-localization-specific Tate theorem surface as the
generic Layer B bridge witness for the concrete candidate path. -/
def toLayerBTateWitness
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {ML : LayerB.MotivicLocalization}
    (witness : MotivicLocalizationTateWitness ML) :
    LayerBTateWitness
      (layerBConcreteSourceDataCandidate presentation aux ML) where
  tateStabilizationPiZero := witness.tateStabilizationPiZero
  tateStabilizationPiZero_holds := witness.tateStabilizationPiZero_holds
  tateStabilizationInfinity := witness.tateStabilizationInfinity
  tateStabilizationInfinity_holds := witness.tateStabilizationInfinity_holds

/-- The candidate-path repackaging keeps the Tate proposition surface
unchanged. -/
theorem toLayerBTateWitness_preserves_fields
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {ML : LayerB.MotivicLocalization}
    (witness : MotivicLocalizationTateWitness ML) :
    let repackaged :=
      MotivicLocalizationTateWitness.toLayerBTateWitness
        (presentation := presentation) (aux := aux) witness
    repackaged.tateStabilizationPiZero = witness.tateStabilizationPiZero ∧
      repackaged.tateStabilizationInfinity = witness.tateStabilizationInfinity := by
  exact ⟨rfl, rfl⟩

end MotivicLocalizationTateWitness

/-- The symmetric-monoidal theorem surface for the real
`LayerB.MotivicLocalization` carrier repackages directly into the generic Layer
B witness expected by the abstract export seam. -/
theorem motivicLocalization_candidate_symmetricMonoidalWitness_repackages
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (ML : LayerB.MotivicLocalization)
    (witness : MotivicLocalizationSymmetricMonoidalWitness ML) :
    let repackaged :=
      MotivicLocalizationSymmetricMonoidalWitness.toLayerBSymmetricMonoidalWitness
        (presentation := presentation) (aux := aux) witness
    repackaged.symmetricMonoidalPiZero = witness.symmetricMonoidalPiZero ∧
      repackaged.symmetricMonoidalInfinity = witness.symmetricMonoidalInfinity := by
  simpa using
    (MotivicLocalizationSymmetricMonoidalWitness.toLayerBSymmetricMonoidalWitness_preserves_fields
      (presentation := presentation) (aux := aux) witness)

/-- The stable/triangulated theorem surface for the real
`LayerB.MotivicLocalization` carrier repackages directly into the generic Layer
B witness expected by the abstract export seam. -/
theorem motivicLocalization_candidate_stableTriangulatedWitness_repackages
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (ML : LayerB.MotivicLocalization)
    (witness : MotivicLocalizationStableTriangulatedWitness ML) :
    let repackaged :=
      MotivicLocalizationStableTriangulatedWitness.toLayerBStableTriangulatedWitness
        (presentation := presentation) (aux := aux) witness
    repackaged.triangulatedStablePiZero = witness.triangulatedStablePiZero ∧
      repackaged.triangulatedStableInfinity = witness.triangulatedStableInfinity := by
  simpa using
    (MotivicLocalizationStableTriangulatedWitness.toLayerBStableTriangulatedWitness_preserves_fields
      (presentation := presentation) (aux := aux) witness)

/-- The local-geometry theorem surface for the real
`LayerB.MotivicLocalization` carrier repackages directly into the generic Layer
B witness expected by the abstract export seam. -/
theorem motivicLocalization_candidate_localGeometryWitness_repackages
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (ML : LayerB.MotivicLocalization)
    (witness : MotivicLocalizationLocalGeometryWitness ML) :
    let repackaged :=
      MotivicLocalizationLocalGeometryWitness.toLayerBLocalGeometryWitness
        (presentation := presentation) (aux := aux) witness
    repackaged.a1InvariancePiZeroTicket = witness.a1InvariancePiZeroTicket ∧
      repackaged.a1InvarianceInfinityTicket = witness.a1InvarianceInfinityTicket ∧
      repackaged.nisnevichDescentPiZeroTicket = witness.nisnevichDescentPiZeroTicket ∧
      repackaged.nisnevichDescentInfinityTicket = witness.nisnevichDescentInfinityTicket ∧
      repackaged.localizationPiZeroTicket = witness.localizationPiZeroTicket ∧
      repackaged.localizationInfinityTicket = witness.localizationInfinityTicket := by
  simpa using
    (MotivicLocalizationLocalGeometryWitness.toLayerBLocalGeometryWitness_preserves_fields
      (presentation := presentation) (aux := aux) witness)

/-- The Tate theorem surface for the real `LayerB.MotivicLocalization` carrier
repackages directly into the generic Layer B witness expected by the abstract
export seam. -/
theorem motivicLocalization_candidate_tateWitness_repackages
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (ML : LayerB.MotivicLocalization)
    (witness : MotivicLocalizationTateWitness ML) :
    let repackaged :=
      MotivicLocalizationTateWitness.toLayerBTateWitness
        (presentation := presentation) (aux := aux) witness
    repackaged.tateStabilizationPiZero = witness.tateStabilizationPiZero ∧
      repackaged.tateStabilizationInfinity = witness.tateStabilizationInfinity := by
  simpa using
    (MotivicLocalizationTateWitness.toLayerBTateWitness_preserves_fields
      (presentation := presentation) (aux := aux) witness)

/-- Cautious Layer B -> Layer D bridge payload. This does not claim that the
Layer B named/free holography package already proves the full Layer D source
construction witness. Instead, it stores the Layer B export precursor together
with whatever extra source-side data and theorem fields are still needed to
populate the Layer D seam honestly. -/
structure LayerBSourceExportData
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine) where
  pkg : NamedFreeSourceHolographyPackage presentation aux
  concreteSource : LayerBConcreteSourceData presentation aux
  localizationData : LayerBLocalizationInterfaceData concreteSource
  symmetricMonoidalWitness : LayerBSymmetricMonoidalWitness concreteSource
  stableTriangulatedWitness : LayerBStableTriangulatedWitness concreteSource
  localGeometryWitness : LayerBLocalGeometryWitness concreteSource
  tateWitness : LayerBTateWitness concreteSource

namespace LayerBConcreteSourceData

/-- Transport concrete source-side data to the concrete preferred auxiliary
object. This is fieldwise because the source-side categories and localization
payload do not inspect the gluing-witness carrier. -/
def toConcretePreferredAuxiliaryData
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceData : LayerBConcreteSourceData presentation aux) :
    LayerBConcreteSourceData presentation
      (concretePreferredBoundaryBridgeAuxiliaryData aux) where
  Syntax := sourceData.Syntax
  Envelope := sourceData.Envelope
  Localized := sourceData.Localized
  catEnvelope := sourceData.catEnvelope
  catLocalized := sourceData.catLocalized
  includeSyntax := sourceData.includeSyntax
  weakEquivalence := sourceData.weakEquivalence
  localizeObj := sourceData.localizeObj
  localizationInterface := sourceData.localizationInterface

end LayerBConcreteSourceData

namespace LayerBLocalizationInterfaceData

/-- Transport localization-interface seam data to the concrete preferred
auxiliary object. -/
def toConcretePreferredAuxiliaryData
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {sourceData : LayerBConcreteSourceData presentation aux}
    (data : LayerBLocalizationInterfaceData sourceData) :
    LayerBLocalizationInterfaceData sourceData.toConcretePreferredAuxiliaryData where
  localizationMatchesTheorem := {
    sourceCategoryAlignment :=
      data.localizationMatchesTheorem.sourceCategoryAlignment
    targetCategoryAlignment :=
      data.localizationMatchesTheorem.targetCategoryAlignment
    weakEquivalenceAlignment :=
      data.localizationMatchesTheorem.weakEquivalenceAlignment
    localizeObjAlignment :=
      data.localizationMatchesTheorem.localizeObjAlignment
  }
  localizationLaws := data.localizationLaws

end LayerBLocalizationInterfaceData

namespace LayerBSymmetricMonoidalWitness

/-- Transport symmetric-monoidal witnesses to the concrete preferred auxiliary
object. -/
def toConcretePreferredAuxiliaryData
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {sourceData : LayerBConcreteSourceData presentation aux}
    (witness : LayerBSymmetricMonoidalWitness sourceData) :
    LayerBSymmetricMonoidalWitness sourceData.toConcretePreferredAuxiliaryData where
  symmetricMonoidalPiZero := witness.symmetricMonoidalPiZero
  symmetricMonoidalPiZero_holds := witness.symmetricMonoidalPiZero_holds
  symmetricMonoidalInfinity := witness.symmetricMonoidalInfinity
  symmetricMonoidalInfinity_holds := witness.symmetricMonoidalInfinity_holds

end LayerBSymmetricMonoidalWitness

namespace LayerBStableTriangulatedWitness

/-- Transport stable/triangulated witnesses to the concrete preferred auxiliary
object. -/
def toConcretePreferredAuxiliaryData
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {sourceData : LayerBConcreteSourceData presentation aux}
    (witness : LayerBStableTriangulatedWitness sourceData) :
    LayerBStableTriangulatedWitness sourceData.toConcretePreferredAuxiliaryData where
  triangulatedStablePiZero := witness.triangulatedStablePiZero
  triangulatedStablePiZero_holds := witness.triangulatedStablePiZero_holds
  triangulatedStableInfinity := witness.triangulatedStableInfinity
  triangulatedStableInfinity_holds := witness.triangulatedStableInfinity_holds

end LayerBStableTriangulatedWitness

namespace LayerBLocalGeometryWitness

/-- Transport local-geometry witnesses to the concrete preferred auxiliary
object. -/
def toConcretePreferredAuxiliaryData
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {sourceData : LayerBConcreteSourceData presentation aux}
    (witness : LayerBLocalGeometryWitness sourceData) :
    LayerBLocalGeometryWitness sourceData.toConcretePreferredAuxiliaryData where
  a1InvariancePiZeroTicket := witness.a1InvariancePiZeroTicket
  a1InvarianceInfinityTicket := witness.a1InvarianceInfinityTicket
  nisnevichDescentPiZeroTicket := witness.nisnevichDescentPiZeroTicket
  nisnevichDescentInfinityTicket := witness.nisnevichDescentInfinityTicket
  localizationPiZeroTicket := witness.localizationPiZeroTicket
  localizationInfinityTicket := witness.localizationInfinityTicket

end LayerBLocalGeometryWitness

namespace LayerBTateWitness

/-- Transport Tate witnesses to the concrete preferred auxiliary object. -/
def toConcretePreferredAuxiliaryData
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {sourceData : LayerBConcreteSourceData presentation aux}
    (witness : LayerBTateWitness sourceData) :
    LayerBTateWitness sourceData.toConcretePreferredAuxiliaryData where
  tateStabilizationPiZero := witness.tateStabilizationPiZero
  tateStabilizationPiZero_holds := witness.tateStabilizationPiZero_holds
  tateStabilizationInfinity := witness.tateStabilizationInfinity
  tateStabilizationInfinity_holds := witness.tateStabilizationInfinity_holds

end LayerBTateWitness

namespace LayerBSourceExportData

/-- Transport the cautious Layer B source export payload to the concrete
preferred auxiliary object. The boundary-facing package is rebuilt for the
concrete auxiliary object; the source-category payload is copied fieldwise. -/
def toConcretePreferredAuxiliaryData
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    LayerBSourceExportData presentation
      (concretePreferredBoundaryBridgeAuxiliaryData aux) where
  pkg :=
    namedFreeSyntax_toConcretePreferredSourceHolographyPackage
      presentation boundaryCodes proofs
  concreteSource := sourceExport.concreteSource.toConcretePreferredAuxiliaryData
  localizationData := sourceExport.localizationData.toConcretePreferredAuxiliaryData
  symmetricMonoidalWitness :=
    sourceExport.symmetricMonoidalWitness.toConcretePreferredAuxiliaryData
  stableTriangulatedWitness :=
    sourceExport.stableTriangulatedWitness.toConcretePreferredAuxiliaryData
  localGeometryWitness :=
    sourceExport.localGeometryWitness.toConcretePreferredAuxiliaryData
  tateWitness := sourceExport.tateWitness.toConcretePreferredAuxiliaryData

end LayerBSourceExportData

/-- Smallest proof-relevant internal holography interface that the current
Layer B theorem surfaces can populate honestly.

What is genuinely available today is split into two parts:

- proof-relevant boundary reconstruction on the preferred `ULift` carrier;
- proof-relevant record visibility through `toFrontierWord` plus a faithful
  frontier quotient realization;
- the actual source/localization export path into Layer D through
  `LayerBSourceExportData`.

What is *not* claimed here is a full boundary-to-completed-record inverse: that
still needs additional theorem content, and is named separately below. -/
structure InternalHolographyInterface
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine) where
  boundaryReconstruction : BoundaryReconstructionInterface
  preferredBoundaryWitness : PreferredCommutativeBoundaryExposureDesignWitness aux
  holographyData :
    HolographicReconstructionData
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)
  boundaryPresentation :
    SyntacticBoundaryPresentation
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)
  frontierQuotientRealization :
    FrontierQuotientRealization
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)
  residueHolography :
    ∀ {R₁ R₂ :
      CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)},
      frontierQuotientRealization.realize (holographyData.toFrontierWord R₁) =
          frontierQuotientRealization.realize (holographyData.toFrontierWord R₂) ↔
        FrontierWord.Equiv
          (holographyData.toFrontierWord R₁)
          (holographyData.toFrontierWord R₂)
  sourceExport : LayerBSourceExportData presentation aux

/-- Concrete preferred internal holography interface on the concrete preferred
auxiliary object. The boundary-facing package is rebuilt directly for the
concrete auxiliary object, while the source-export payload is transported
fieldwise from the old auxiliary object. -/
def concretePreferredInternalHolographyInterface
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    InternalHolographyInterface presentation
      (concretePreferredBoundaryBridgeAuxiliaryData aux) where
  boundaryReconstruction :=
    preferredBoundaryReconstructionInterface
      (concretePreferredBoundaryBridgeAuxiliaryData aux)
  preferredBoundaryWitness :=
    namedFreeSyntax_toPreferredCommutativeBoundaryExposureDesignWitness
      (aux := concretePreferredBoundaryBridgeAuxiliaryData aux)
      presentation boundaryCodes.toConcretePreferredAuxiliaryData proofs
  holographyData := HolographicReconstructionData.identity
  boundaryPresentation :=
    theorem_named_free_syntax_gives_preferredBoundaryPresentation
      presentation boundaryCodes proofs
  frontierQuotientRealization :=
    theorem_named_free_syntax_gives_preferredFrontierQuotientRealization
      presentation boundaryCodes proofs
  residueHolography := by
    intro R₁ R₂
    simpa using
      (theorem_named_free_syntax_gives_preferredResidueHolographicReconstruction
        presentation
        boundaryCodes
        proofs
        HolographicReconstructionData.identity
        (R₁ := R₁) (R₂ := R₂))
  sourceExport :=
    sourceExport.toConcretePreferredAuxiliaryData presentation boundaryCodes proofs

@[simp] theorem concretePreferredInternalHolographyInterface_toFrontierWord
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux))) :
    (concretePreferredInternalHolographyInterface
      presentation sourceExport boundaryCodes proofs).holographyData.toFrontierWord R =
      FrontierWord.ofResidue R :=
  rfl

@[simp] theorem concretePreferredInternalHolographyInterface_sourceExport
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
  (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    (concretePreferredInternalHolographyInterface
      presentation sourceExport boundaryCodes proofs).sourceExport =
      sourceExport.toConcretePreferredAuxiliaryData presentation boundaryCodes proofs :=
  rfl

/-- Preferred concrete syntactic boundary presentation for the concrete
preferred auxiliary setup. This is just the boundary-presentation field already
carried by the concrete preferred internal holography interface, named as a
standalone manuscript-facing object. -/
def concretePreferredSyntacticBoundaryPresentation
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    SyntacticBoundaryPresentation
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux)) :=
  (concretePreferredInternalHolographyInterface
    presentation sourceExport boundaryCodes proofs).boundaryPresentation

@[simp] theorem concretePreferredSyntacticBoundaryPresentation_eq
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    concretePreferredSyntacticBoundaryPresentation
      presentation sourceExport boundaryCodes proofs =
      (concretePreferredInternalHolographyInterface
        presentation sourceExport boundaryCodes proofs).boundaryPresentation :=
  rfl

/-- Missing target for a full internal reconstruction theorem from boundary
records back to completed reconstruction records. The current theorem surface
does not yet provide this map, so it remains an explicit target. -/
def BoundaryToCompletedRecordReconstructionTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine) : Prop :=
  ∃ reconstructRecord :
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux).BoundaryObject →
        CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup presentation.toDoctrine aux),
    ∀ b,
      (reconstructRecord b).Y = b

/-- Boundary-only completed-record placeholder on the preferred setup.
This is the smallest honest record-level constructor needed to discharge the
current boundary-to-record target: it carries no packets and preserves the
requested visible target boundary literally in the `Y` field. -/
def boundaryOnlyCompletedRecord
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (b : (PreferredFoundationsBridgeSetup presentation.toDoctrine aux).BoundaryObject) :
    CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux) where
  n := 0
  X := b
  Y := b
  ports :=
    { externalIn := []
      externalOut := []
      packetIn := fun i => i.elim0
      packetOut := fun i => i.elim0 }
  packets := fun i => i.elim0
  dep :=
    { edge := fun i _ => i.elim0
      acyclic := by
        intro i
        exact i.elim0 }
  attach := fun i => i.elim0
  tensor := { blocks := [] }
  key :=
    { pos := fun i => i
      total := by
        intro i
        exact i.elim0
      bijective := by
        refine ⟨?_, ?_⟩
        · intro i
          exact i.elim0
        · intro i
          exact i.elim0 }

/-- The current boundary-to-record target is already realized by the generic
boundary-only zero-packet record on the preferred setup. This closes the
remaining bridge seam at the exact theorem shape currently requested, without
pretending to provide a stronger canonical inverse than the code actually has. -/
theorem boundaryOnlyCompletedRecord_realizes_BoundaryToCompletedRecordReconstructionTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine) :
    BoundaryToCompletedRecordReconstructionTarget presentation aux := by
  refine ⟨boundaryOnlyCompletedRecord presentation aux, ?_⟩
  intro b
  rfl

/-- Missing target for the normal-form / canonicality input that would let the
internal holography lane move from boundary presentation to stronger canonical
reconstruction statements. On the preferred path this is exactly the sharpened
boundary-code completeness theorem. -/
def InternalHolographyCanonicalityNormalFormTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine) : Prop :=
  preferred_boundary_code_eq_generated_by_local_two_step_swaps aux

/-- Alias exposing the separate pi0-shadow localization target now required on
the proof-relevant localization side. -/
abbrev InternalHolographyPiZeroShadowTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    (ML : LayerB.MotivicLocalization) :=
  CategoryInfra.LocalizationPiZeroShadowTheorem ML.localization

namespace InternalHolographyInterface

/-- The quotient-visible boundary value associated to an internal record. This
is the actual visible target carried by the current internal holography path. -/
def visibleBoundary
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux) →
      I.frontierQuotientRealization.Target :=
  fun R => I.frontierQuotientRealization.realize (I.holographyData.toFrontierWord R)

/-- The internal holography interface remembers a faithful quotient-visible
boundary map from completed records. -/
theorem visibleBoundary_eq_iff_frontierEquiv
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    {R₁ R₂ :
      CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)} :
    I.visibleBoundary R₁ = I.visibleBoundary R₂ ↔
      FrontierWord.Equiv
        (I.holographyData.toFrontierWord R₁)
        (I.holographyData.toFrontierWord R₂) :=
  I.residueHolography

theorem frontierEquiv_of_visibleBoundary_eq
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    {R₁ R₂ :
      CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)}
    (h : I.visibleBoundary R₁ = I.visibleBoundary R₂) :
    FrontierWord.Equiv
      (I.holographyData.toFrontierWord R₁)
      (I.holographyData.toFrontierWord R₂) :=
  (I.visibleBoundary_eq_iff_frontierEquiv).1 h

theorem visibleBoundary_eq_of_frontierEquiv
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    {R₁ R₂ :
      CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)}
    (h : FrontierWord.Equiv
      (I.holographyData.toFrontierWord R₁)
      (I.holographyData.toFrontierWord R₂)) :
    I.visibleBoundary R₁ = I.visibleBoundary R₂ :=
  (I.visibleBoundary_eq_iff_frontierEquiv).2 h

/-- Campaign-6 direct packaging of the internal visible-boundary route: the
existing theorem `visibleBoundary_eq_iff_frontierEquiv` already realizes the
manuscript-facing target that visible-boundary equality determines the current
frontier-word equality carrier. -/
theorem realizes_VisibleBoundaryDeterminesFrontierWordTarget_of_visibleBoundary_eq_iff_frontierEquiv
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    VisibleBoundaryDeterminesFrontierWordTarget
      I.visibleBoundary
      I.holographyData.toFrontierWord := by
  refine VisibleBoundaryDeterminesFrontierWordTarget.ofImplication _ _ ?_
  intro R₁ R₂ hVisible
  exact I.frontierEquiv_of_visibleBoundary_eq hVisible

/-- Preferred visible-boundary equality feeds the concrete zero-boundary
generated trace/frontier route once the remaining setup-conversion seam is
supplied as a narrow target object. This is the precise bridge from the current
preferred internal holography lane into Campaign 6's concrete generated-trace
equality on `concreteBoundaryMinimalSetup RI`. -/
theorem visibleBoundary_eq_implies_concreteGeneratedTraceFrontierEquiv
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    (RI : Type _) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    (bridge : PreferredVisibleBoundaryToConcreteZeroBoundaryTarget
      (presentation := presentation) (aux := aux) RI I.holographyData.toFrontierWord)
    {R₁ R₂ :
      CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)}
    (hVisible : I.visibleBoundary R₁ = I.visibleBoundary R₂) :
    GeneratedTraceFrontierEquiv RI D
      (traceFrontierWord_of_zeroBoundaryFrontierWord RI
        (bridge.concreteFrontierWord R₁)
        (bridge.zero_boundary_source R₁)
        (bridge.zero_boundary_target R₁))
      (traceFrontierWord_of_zeroBoundaryFrontierWord RI
        (bridge.concreteFrontierWord R₂)
        (bridge.zero_boundary_source R₂)
        (bridge.zero_boundary_target R₂)) := by
  apply generatedTraceFrontierEquiv_of_projectionFrontierEquiv
  simpa [traceFrontierWord_of_zeroBoundaryFrontierWord, TraceFrontierWord.toFrontierWord] using
    bridge.preserves_frontier_equiv (I.frontierEquiv_of_visibleBoundary_eq hVisible)

/-- Downstream corrected-residue CanNF consequence of the narrow preferred to
concrete zero-boundary setup bridge. This keeps Campaign 6 on the sound route:
preferred visible-boundary equality implies equality of the concrete corrected
residue normal forms, without using any reverse completeness result. -/
theorem visibleBoundary_eq_implies_concreteCorrectedResidueCanNF_eq
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    (RI : Type _) [DecidableEq RI] [LinearOrder RI]
    (D : AdjacentCertifiedStepTraceCompressionData (concreteBoundaryMinimalSetup RI))
    (bridge : PreferredVisibleBoundaryToConcreteZeroBoundaryTarget
      (presentation := presentation) (aux := aux) RI I.holographyData.toFrontierWord)
    {R₁ R₂ :
      CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)}
    (hVisible : I.visibleBoundary R₁ = I.visibleBoundary R₂) :
    correctedResidueCanNF RI (bridge.concreteFrontierWord R₁) =
      correctedResidueCanNF RI (bridge.concreteFrontierWord R₂) := by
  let hGenerated :=
    visibleBoundary_eq_implies_concreteGeneratedTraceFrontierEquiv
      I RI D bridge hVisible
  simpa [traceFrontierWord_of_zeroBoundaryFrontierWord, TraceFrontierWord.toFrontierWord] using
    generatedTraceFrontierEquiv_preservesCorrectedResidueCanNF_closed RI D hGenerated

/-- Boundary-admin-equivalent records have equal visible boundary values in the
internal holography interface. -/
theorem visibleBoundary_respects_admin
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    {R₁ R₂ :
      CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)}
    (h : RecordStructEquiv
      (@BoundaryAdminEquiv (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
      R₁ R₂) :
    I.visibleBoundary R₁ = I.visibleBoundary R₂ :=
  holographic_invariant_sound_on_records
    I.frontierQuotientRealization.toFrontierQuotientInvariant
    I.holographyData
    h

/-- A strict replay certificate yields the boundary-admin structural
equivalence needed by the quotient-visible holography interface. This is the
honest weakening from literal replay correctness down to the quotient-visible
record relation actually used by `visibleBoundary_respects_admin`. -/
theorem recordEquiv_to_boundaryAdminStructEquiv
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {R₁ R₂ :
      CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)}
    (h : RecordEquiv R₁ R₂) :
    RecordStructEquiv
      (@BoundaryAdminEquiv
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
      R₁ R₂ := by
  let hStruct : RecordStructEquiv Eq R₁ R₂ := h.toStructEquiv
  refine
    { hStruct with
      Y_rel := ?_ }
  rw [h.Y_eq]
  exact BoundaryAdminEquiv.refl R₂.Y

/-- Smallest next proof-relevant reconstruction object for the internal
holography lane, matching the manuscript's constructive proof spine more
closely than the earlier boundary-only inverse.

It records exactly the replayable data currently available in Lean:

- a completed-record witness, so the canonical peel algorithm applies;
- the canonical peel chain itself;
- the replay certificate showing that replaying that chain recovers the
  original record up to strict `RecordEquiv`;
- the preferred boundary replay certificate on the actual boundary object.

This is still weaker than a full boundary-to-record inverse, but it is already
strong enough to support quotient-visible reconstruction theorems. -/
structure QuotientVisibleReconstructionSpine
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    (R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)) where
  completedWitness : R.IsCompleted
  canonicalPeelChain : CompletedReconstructionRecord.PeelChain R
  replayRecordEquiv : RecordEquiv (RewriteCalculusSetup.PeelChain.replay canonicalPeelChain) R
  boundaryReplay :
    BoundaryReplayCertificate
      (preferredBoundaryReconstructionInterface
        (Dc := presentation.toDoctrine) aux).boundary
      (preferredBoundaryReconstructionInterface
        (Dc := presentation.toDoctrine) aux).reconstruct
      R.Y

/-- Canonical constructor for the quotient-visible reconstruction spine from a
completed record. This is the direct Lean realization of the manuscript's
algorithmic clause: canonical sink peel, recursive replay, and boundary replay
data. -/
noncomputable def quotientVisibleReconstructionSpine
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    (R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
    (hCompleted : R.IsCompleted) :
    QuotientVisibleReconstructionSpine I R where
  completedWitness := hCompleted
  canonicalPeelChain :=
    CompletedReconstructionRecord.PeelChain.canonicalPeelChain R hCompleted
  replayRecordEquiv :=
    RewriteCalculusSetup.PeelChain.replay_recordEquiv
      (CompletedReconstructionRecord.PeelChain.canonicalPeelChain R hCompleted)
  boundaryReplay :=
    (preferredBoundaryReconstructionInterface
      (Dc := presentation.toDoctrine) aux).boundaryReplay R.Y

/-- Next proof-relevant strengthening toward the manuscript's gluing step for
nonempty records.

This packages the one-step data used after canonical sink deletion:

- the canonical sink itself and its sink proof;
- the predecessor completedness witness;
- the predecessor replay spine;
- the concrete sink/gluing data `SinkData`, whose `attach` field is exactly the
  stored attachment witness `Attach(s)` from the manuscript;
- the one-step glued replay certificate back to the original record.

This stays honest about scope: it does not claim full boundary-to-record
reconstruction, only the proof-relevant gluing step currently available from
the replay infrastructure. -/
structure CanonicalGluingWitnessSpine
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    (R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)) where
  quotientVisible : QuotientVisibleReconstructionSpine I R
  nonempty : 0 < R.n
  canonicalSink : Fin R.n
  canonicalSink_eq : canonicalSink = CompletedReconstructionRecord.canonicalSink R nonempty
  canonicalSinkIsSink : R.IsSink canonicalSink
  predecessorCompletedWitness : (peelSink R canonicalSink).IsCompleted
  predecessorReplay : QuotientVisibleReconstructionSpine I (peelSink R canonicalSink)
  sinkData : RewriteCalculusSetup.SinkData _ (peelSink R canonicalSink)
  sinkData_eq : sinkData = RewriteCalculusSetup.sinkData R canonicalSink
  gluedReplayRecordEquiv :
    RecordEquiv
      (RewriteCalculusSetup.unpeelSink
        (RewriteCalculusSetup.PeelChain.replay predecessorReplay.canonicalPeelChain)
        (sinkData.castN
          (RewriteCalculusSetup.PeelChain.replay_n predecessorReplay.canonicalPeelChain).symm))
      R

/-- Canonical constructor for the one-step gluing witness data mined from the
manuscript's sink-deletion inverse clause. -/
noncomputable def canonicalGluingWitnessSpine
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    (R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
    (hCompleted : R.IsCompleted)
    (hpos : 0 < R.n) :
    CanonicalGluingWitnessSpine I R := by
  let s : Fin R.n := CompletedReconstructionRecord.canonicalSink R hpos
  let hSink : R.IsSink s := CompletedReconstructionRecord.canonicalSink_isSink R hpos
  let hPredCompleted : (peelSink R s).IsCompleted :=
    sink_peel_preserves_completedness hSink hCompleted
  let predecessorReplay :=
    quotientVisibleReconstructionSpine I (peelSink R s) hPredCompleted
  let step1 :
      RecordEquiv
        (RewriteCalculusSetup.unpeelSink
          (RewriteCalculusSetup.PeelChain.replay predecessorReplay.canonicalPeelChain)
          ((RewriteCalculusSetup.sinkData R s).castN
            (RewriteCalculusSetup.PeelChain.replay_n predecessorReplay.canonicalPeelChain).symm))
        (RewriteCalculusSetup.unpeelSink
          (peelSink R s)
          (RewriteCalculusSetup.sinkData R s)) :=
    RewriteCalculusSetup.unpeelSink_castN_recordEquiv
      predecessorReplay.replayRecordEquiv
      (RewriteCalculusSetup.sinkData R s)
  let step2 :
      RecordEquiv
        (RewriteCalculusSetup.unpeelSink
          (peelSink R s)
          (RewriteCalculusSetup.sinkData R s))
        R :=
    RewriteCalculusSetup.unpeelSink_peelSink R s hSink
  exact
    { quotientVisible := quotientVisibleReconstructionSpine I R hCompleted
      nonempty := hpos
      canonicalSink := s
      canonicalSink_eq := rfl
      canonicalSinkIsSink := hSink
      predecessorCompletedWitness := hPredCompleted
      predecessorReplay := predecessorReplay
      sinkData := RewriteCalculusSetup.sinkData R s
      sinkData_eq := rfl
      gluedReplayRecordEquiv := RecordEquiv.trans step1 step2 }

/-- The replayed canonical reconstruction has exactly the preferred replayed
boundary obtained from the boundary-level inverse. This is the bridge from the
existing boundary reconstruction interface to the new record-level replay
spine. -/
theorem replayedRecord_boundary_eq_boundaryReplay
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {I : InternalHolographyInterface presentation aux}
    {R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)}
    (S : QuotientVisibleReconstructionSpine I R) :
    (RewriteCalculusSetup.PeelChain.replay S.canonicalPeelChain).Y =
      (preferredBoundaryReconstructionInterface
        (Dc := presentation.toDoctrine) aux).boundary
        ((preferredBoundaryReconstructionInterface
          (Dc := presentation.toDoctrine) aux).reconstruct R.Y) := by
  calc
    (RewriteCalculusSetup.PeelChain.replay S.canonicalPeelChain).Y = R.Y :=
      S.replayRecordEquiv.Y_eq
    _ =
        (preferredBoundaryReconstructionInterface
          (Dc := presentation.toDoctrine) aux).boundary
          ((preferredBoundaryReconstructionInterface
            (Dc := presentation.toDoctrine) aux).reconstruct R.Y) := by
          symm
          simpa using S.boundaryReplay.agrees

/-- Honest quotient-visible strengthening of the current internal holography
lane: replaying the canonical peel chain derived from a completed record lands
in the same quotient-visible boundary class as the original record.

This is the precise theorem currently supported by the Lean surface:

- stronger than the bare boundary-level inverse, because it speaks about a
  replayed completed record;
- weaker than full record equality from boundary data, because the conclusion
  is only quotient-visible equality. -/
theorem replayedRecord_visibleBoundary_eq
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {I : InternalHolographyInterface presentation aux}
    {R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)}
    (S : QuotientVisibleReconstructionSpine I R) :
    I.visibleBoundary (RewriteCalculusSetup.PeelChain.replay S.canonicalPeelChain) =
      I.visibleBoundary R :=
  I.visibleBoundary_respects_admin
    (recordEquiv_to_boundaryAdminStructEquiv S.replayRecordEquiv)

/-- One-step quotient-visible stability for the manuscript's gluing clause:
replaying the predecessor subrecord and then gluing back the canonical sink via
its stored attachment witness preserves the visible boundary class. -/
theorem canonicalGluedReplay_visibleBoundary_eq
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {I : InternalHolographyInterface presentation aux}
    {R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)}
    (G : CanonicalGluingWitnessSpine I R) :
    I.visibleBoundary
      (RewriteCalculusSetup.unpeelSink
        (RewriteCalculusSetup.PeelChain.replay G.predecessorReplay.canonicalPeelChain)
        (G.sinkData.castN
          (RewriteCalculusSetup.PeelChain.replay_n G.predecessorReplay.canonicalPeelChain).symm)) =
      I.visibleBoundary R :=
  I.visibleBoundary_respects_admin
    (recordEquiv_to_boundaryAdminStructEquiv G.gluedReplayRecordEquiv)

/-- Global proof-relevant replay spine for the sink-peel branch of the
manuscript's reconstruction algorithm.

This packages the recursive delete/recurse/glue proof shape, but only for the
part of the algorithm currently represented in Lean:

- the zero-packet terminal case, where the canonical peel chain is literally
  empty;
- the nonempty sink-peel case, where a canonical gluing witness advances one
  step and the predecessor record carries the recursive spine.

The tensor-factor branch is intentionally excluded here because the current
scoped files do not yet expose proof-relevant component extraction and
reassembly data. That branch remains a separate explicit theorem target below. -/
inductive RecursiveReplayCongruenceSpine
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    (R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)) → Type _ where
  | zero
      (R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
      (quotientVisible : QuotientVisibleReconstructionSpine I R)
      (hzero : R.n = 0)
      (canonicalPeelChain_eq :
        quotientVisible.canonicalPeelChain =
          CompletedReconstructionRecord.PeelChain.nil R hzero) :
      RecursiveReplayCongruenceSpine I R
  | step
      (R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
      (gluing : CanonicalGluingWitnessSpine I R)
      (predecessor :
        RecursiveReplayCongruenceSpine I (peelSink R gluing.canonicalSink)) :
      RecursiveReplayCongruenceSpine I R

/-- Canonical recursive replay-congruence spine for the sink-peel recursion.

This is the manuscript's delete/recurse/glue induction written as actual Lean
data. The constructor follows the same two branches the current replay surface
can support:

- `R.n = 0`: the canonical peel chain is empty;
- `0 < R.n`: use the canonical gluing witness and recurse on the peeled
  predecessor record.

The tensor-factor branch is still a separate theorem target because the current
surface does not yet provide component records and a reassembly witness. -/
noncomputable def recursiveReplayCongruenceSpine
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    (R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
    (hCompleted : R.IsCompleted) :
    RecursiveReplayCongruenceSpine I R := by
  by_cases hzero : R.n = 0
  · refine RecursiveReplayCongruenceSpine.zero R
      (quotientVisibleReconstructionSpine I R hCompleted) hzero ?_
    change
      CompletedReconstructionRecord.PeelChain.canonicalPeelChain R hCompleted =
        CompletedReconstructionRecord.PeelChain.nil R hzero
    simpa using
      (CompletedReconstructionRecord.PeelChain.canonicalPeelChain_zero R hCompleted hzero)
  · let hpos : 0 < R.n := Nat.pos_of_ne_zero hzero
    let G := canonicalGluingWitnessSpine I R hCompleted hpos
    refine RecursiveReplayCongruenceSpine.step R G ?_
    simpa [G.canonicalSink_eq] using
      recursiveReplayCongruenceSpine I
        (peelSink R (CompletedReconstructionRecord.canonicalSink R hpos))
        G.predecessorCompletedWitness
termination_by R.n
decreasing_by
  show (peelSink R (CompletedReconstructionRecord.canonicalSink R hpos)).n < R.n
  show R.n - 1 < R.n
  omega

/-- Recursive replay associated to a global sink-peel congruence spine, paired
with the strict `RecordEquiv` certificate back to the indexed record. -/
noncomputable def recursiveReplayRecordAux
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {I : InternalHolographyInterface presentation aux} :
    ∀ {R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)},
      RecursiveReplayCongruenceSpine I R →
        {R' : CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup presentation.toDoctrine aux) //
          RecordEquiv R' R}
  | _, .zero _ quotientVisible _ _ =>
      ⟨RewriteCalculusSetup.PeelChain.replay quotientVisible.canonicalPeelChain,
        quotientVisible.replayRecordEquiv⟩
  | R, .step _ gluing predecessor =>
      let predecessorReplay := recursiveReplayRecordAux predecessor
      let replayed :=
        RewriteCalculusSetup.unpeelSink
          predecessorReplay.1
          ((RewriteCalculusSetup.sinkData R gluing.canonicalSink).castN
            predecessorReplay.2.n_eq.symm)
      let step1 : RecordEquiv replayed
          (RewriteCalculusSetup.unpeelSink
            (peelSink R gluing.canonicalSink)
            (RewriteCalculusSetup.sinkData R gluing.canonicalSink)) :=
        RewriteCalculusSetup.unpeelSink_castN_recordEquiv
          predecessorReplay.2
          (RewriteCalculusSetup.sinkData R gluing.canonicalSink)
      let step2 : RecordEquiv
          (RewriteCalculusSetup.unpeelSink
            (peelSink R gluing.canonicalSink)
            (RewriteCalculusSetup.sinkData R gluing.canonicalSink))
          R :=
        RewriteCalculusSetup.unpeelSink_peelSink
          R gluing.canonicalSink gluing.canonicalSinkIsSink
      ⟨replayed, RecordEquiv.trans step1 step2⟩

/-- The replayed record extracted from a recursive sink-peel congruence spine. -/
noncomputable def recursiveReplayRecord
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {I : InternalHolographyInterface presentation aux}
    {R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)}
    (S : RecursiveReplayCongruenceSpine I R) :
    CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux) :=
  (recursiveReplayRecordAux S).1

/-- The recursive replay record is strictly `RecordEquiv` to the original
completed record indexed by the spine. -/
theorem recursiveReplayRecord_recordEquiv
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {I : InternalHolographyInterface presentation aux}
    {R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)}
    (S : RecursiveReplayCongruenceSpine I R) :
    RecordEquiv (recursiveReplayRecord S) R :=
  (recursiveReplayRecordAux S).2

/-- Global quotient-visible congruence for the sink-peel replay spine. This is
the recursive version of the local gluing theorem: replaying the entire
sink-peel spine preserves the visible boundary class of the indexed completed
record. -/
theorem recursiveReplayRecord_visibleBoundary_eq
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {I : InternalHolographyInterface presentation aux}
    {R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)}
    (S : RecursiveReplayCongruenceSpine I R) :
    I.visibleBoundary (recursiveReplayRecord S) = I.visibleBoundary R :=
  I.visibleBoundary_respects_admin
    (recordEquiv_to_boundaryAdminStructEquiv
      (recursiveReplayRecord_recordEquiv S))

/-- Combined replay-spine theorem: the canonical replayed reconstruction has
the preferred replayed boundary and the same quotient-visible boundary value as
the original record. This is the current Lean realization of the manuscript's
"delete a canonical sink, recurse, glue back" uniqueness spine. -/
theorem replayedRecord_reconstructs_boundary_and_visibleBoundary
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {I : InternalHolographyInterface presentation aux}
    {R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)}
    (S : QuotientVisibleReconstructionSpine I R) :
    (RewriteCalculusSetup.PeelChain.replay S.canonicalPeelChain).Y =
        (preferredBoundaryReconstructionInterface
          (Dc := presentation.toDoctrine) aux).boundary
          ((preferredBoundaryReconstructionInterface
            (Dc := presentation.toDoctrine) aux).reconstruct R.Y)
      ∧
      I.visibleBoundary
          (RewriteCalculusSetup.PeelChain.replay S.canonicalPeelChain) =
        I.visibleBoundary R :=
  ⟨replayedRecord_boundary_eq_boundaryReplay S,
    replayedRecord_visibleBoundary_eq S⟩

end InternalHolographyInterface

/-- Refined gluing target: every nonempty completed record in the internal
holography interface admits the manuscript's local gluing step in the form of
an actual `CanonicalGluingWitnessSpine`, together with the quotient-visible
stability law for the glued replay.

This is the honest replacement for the earlier coarse target
`∀ Y L₁ L₂, Nonempty GluingWitness`, which forgot the predecessor record, the
specific sink, and the replay certificate needed by the manuscript proof. -/
def BoundaryGluingWitnessTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) : Prop :=
  ∀ (R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
      (_hCompleted : R.IsCompleted) (_hpos : 0 < R.n),
    ∃ G : InternalHolographyInterface.CanonicalGluingWitnessSpine I R,
      I.visibleBoundary
        (RewriteCalculusSetup.unpeelSink
          (RewriteCalculusSetup.PeelChain.replay G.predecessorReplay.canonicalPeelChain)
          (G.sinkData.castN
            (RewriteCalculusSetup.PeelChain.replay_n
              G.predecessorReplay.canonicalPeelChain).symm)) =
        I.visibleBoundary R

/-- The current canonical gluing spine fully realizes the refined gluing target:
for every nonempty completed record, the manuscript's local delete/recurse/
glue step is now available as proof-relevant data together with the quotient-
visible stability law proved from that data. -/
theorem canonicalGluingWitnessSpine_realizes_BoundaryGluingWitnessTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    BoundaryGluingWitnessTarget I := by
  intro R hCompleted hpos
  let G := InternalHolographyInterface.canonicalGluingWitnessSpine I R hCompleted hpos
  exact ⟨G, InternalHolographyInterface.canonicalGluedReplay_visibleBoundary_eq G⟩

/-- Base-case quotient-visible congruence target for the manuscript's
reconstruction proof: single-packet records should admit a proof-relevant
replay spine whose replay stays in the visible boundary class of the original
record. The current sink-peel infrastructure already realizes this case via the
global recursive replay spine. -/
def BaseSinglePacketQuotientCongruenceTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) : Prop :=
  ∀ (R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
      (_hCompleted : R.IsCompleted),
    R.n = 1 →
      ∃ S : InternalHolographyInterface.RecursiveReplayCongruenceSpine I R,
        I.visibleBoundary
            (InternalHolographyInterface.recursiveReplayRecord S) =
          I.visibleBoundary R

/-- Pending theorem target for the manuscript's tensor-factor branch.

The scoped Lean surface does not yet expose proof-relevant extraction of the
component completed records or a tensor reassembly operator on completed
records. The next honest object therefore packages exactly the missing replay
data the manuscript's tensor case needs:

- a completed record for each tensor block;
- a completedness witness for each component;
- a canonical replay spine for each component.

This is intentionally record-indexed and proof-relevant; it does not pretend
that the tensor branch can be recovered from boundary equality alone. -/
structure RestrictedCompletedRecordData
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    (R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
    (b : Fin R.tensor.blocks.length) where
  componentSize : Nat
  componentRecord :
    CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)
  componentSize_eq : componentRecord.n = componentSize
  blockRepresentative : Fin R.n
  blockRepresentative_mem :
    (R.tensor.blocks.get b) blockRepresentative
  packetEmbedding : Fin componentSize → Fin R.n
  packetInBlock :
    ∀ i : Fin componentSize,
      (R.tensor.blocks.get b) (packetEmbedding i)
  packetsCompleteForBlock :
    ∀ j : Fin R.n,
      (R.tensor.blocks.get b) j →
        ∃ i : Fin componentSize, packetEmbedding i = j
  packetsInjective : Function.Injective packetEmbedding
  componentPacketEquiv :
    Fin componentRecord.n ≃ {j : Fin R.n // (R.tensor.blocks.get b) j}
  depRestricted : Prop
  portsRestricted : Prop
  boundaryRestricted : Prop
  attachRestricted : Prop
  keyRestricted : Prop
  componentKeyCompatible :
    componentRecord.key.IsCompatibleWith componentRecord.dep
  componentBoundaryCompatible : Prop
  componentCompleted : componentRecord.IsCompleted
  c1_internal_or_exposed : Prop
  c2_attach_compatible : Prop
  c3_tensor_induced : Prop
  c4_key_restricted : Prop

/-- Proof-relevant package of block-indexed restricted completed-record data.

This is the honest tensor restriction interface: `R.tensor.blocks` still only
provides WCC predicates, so the actual restricted component record and its
restriction witnesses are carried explicitly here, one block at a time, together
with the ambient `Key`-ordering data needed by the downstream tensor spine. -/
structure RestrictedCompletedRecordDataFamily
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    (R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)) where
  componentData :
    (b : Fin R.tensor.blocks.length) → RestrictedCompletedRecordData I R b
  orderedComponents : List (Fin R.tensor.blocks.length)
  orderedComponents_nodup : orderedComponents.Nodup
  orderedComponents_complete :
    ∀ i : Fin R.tensor.blocks.length, i ∈ orderedComponents
  orderedComponents_key_sorted :
    orderedComponents.Pairwise
      (fun i j =>
        R.key.pos (componentData i).blockRepresentative <
          R.key.pos (componentData j).blockRepresentative)

structure TensorComponentExtractionSpine
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)) where
  componentRecord :
    Fin R.tensor.blocks.length →
      CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)
  componentRepresentative :
    (i : Fin R.tensor.blocks.length) → Fin R.n
  componentRepresentative_mem :
    ∀ i : Fin R.tensor.blocks.length,
      (R.tensor.blocks.get i) (componentRepresentative i)
  componentPacketEquiv :
    ∀ i : Fin R.tensor.blocks.length,
      Fin (componentRecord i).n ≃ {j : Fin R.n // (R.tensor.blocks.get i) j}
  componentCompleted :
    ∀ i : Fin R.tensor.blocks.length, (componentRecord i).IsCompleted
  componentKeyCompatible :
    ∀ i : Fin R.tensor.blocks.length,
      (componentRecord i).key.IsCompatibleWith (componentRecord i).dep
  orderedComponents : List (Fin R.tensor.blocks.length)
  orderedComponents_nodup : orderedComponents.Nodup
  orderedComponents_complete :
    ∀ i : Fin R.tensor.blocks.length, i ∈ orderedComponents
  orderedComponents_key_sorted :
    orderedComponents.Pairwise
      (fun i j => R.key.pos (componentRepresentative i) <
        R.key.pos (componentRepresentative j))

/-- Forward the explicit restricted-record package to the existing component
extraction spine by simple field projection. This keeps the downstream tensor
proof surfaces stable while making the missing restriction data explicit. -/
def restrictedCompletedRecordData_to_TensorComponentExtractionSpine
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    {R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)}
    (F : RestrictedCompletedRecordDataFamily I R) :
    TensorComponentExtractionSpine R := by
  refine {
    componentRecord := fun i => (F.componentData i).componentRecord
    componentRepresentative := fun i => (F.componentData i).blockRepresentative
    componentRepresentative_mem := fun i => (F.componentData i).blockRepresentative_mem
    componentPacketEquiv := fun i => (F.componentData i).componentPacketEquiv
    componentCompleted := fun i => (F.componentData i).componentCompleted
    componentKeyCompatible := fun i => (F.componentData i).componentKeyCompatible
    orderedComponents := F.orderedComponents
    orderedComponents_nodup := F.orderedComponents_nodup
    orderedComponents_complete := F.orderedComponents_complete
    orderedComponents_key_sorted := F.orderedComponents_key_sorted
  }

/-- Exact proof-relevant target for the tensor restriction theorem.

This is the honest replacement for pretending that `R.tensor.blocks` alone can
construct the completed subrecords `R|_B`: it asks instead for explicit
restriction data for each tensor block, packaged in `Type`. -/
def RestrictedCompletedRecordDataFamilyTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) : Prop :=
  ∀ (R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
      (_hCompleted : R.IsCompleted) (_hTensor : 1 < R.tensor.blocks.length),
    Nonempty (RestrictedCompletedRecordDataFamily I R)

/-- Exact missing extraction target for the manuscript's tensor branch.

The current Lean surface knows that `R.tensor.blocks` is a WCC decomposition of
`R.dep`, but it does not yet know how to turn those block predicates into the
induced completed subrecords required by Step 1 of the reconstruction
algorithm. This target names that missing theorem precisely. -/
def TensorComponentCompletedRecordExtractionTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) : Prop :=
  ∀ (R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
      (_hCompleted : R.IsCompleted) (_hTensor : 1 < R.tensor.blocks.length),
    Nonempty (TensorComponentExtractionSpine R)

/-- The new restricted-record family target realizes the older component
extraction target by projecting away the extra proof-relevant restriction data.
-/
theorem restrictedCompletedRecordData_realizes_TensorComponentCompletedRecordExtractionTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    RestrictedCompletedRecordDataFamilyTarget I →
      TensorComponentCompletedRecordExtractionTarget I := by
  intro hRestricted
  intro R hCompleted hTensor
  obtain ⟨F⟩ := hRestricted R hCompleted hTensor
  exact ⟨restrictedCompletedRecordData_to_TensorComponentExtractionSpine I F⟩

/-- Exact remaining tensor reassembly target once component extraction is
available.

This is the manuscript's visible-boundary monoidality/reassembly step stated at
the record level actually used by the current internal holography lane: given
component completed subrecords extracted from `R.tensor.blocks` and given the
recursive replay spine on each component, produce a reassembled completed
record in the same visible boundary class as `R`. -/
structure TensorReassemblyFromComponentReplayData
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    (R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
    (E : TensorComponentExtractionSpine R)
    (componentReplay :
      ∀ i : Fin R.tensor.blocks.length,
        InternalHolographyInterface.RecursiveReplayCongruenceSpine I
          (E.componentRecord i)) where
  tensorReplay : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)
  visibleBoundary_eq : I.visibleBoundary tensorReplay = I.visibleBoundary R

/-- Proof-relevant reassembly target for the tensor branch.

The current existential target only asks for some reassembled replay record in
the visible boundary class of `R`. This refined target packages that missing
record and its visible-boundary theorem explicitly in `Type`, matching the rest
of the proof-relevant tensor lane. -/
def TensorReassemblyFromComponentReplayDataTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) : Prop :=
  ∀ (R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
      (_hCompleted : R.IsCompleted) (_hTensor : 1 < R.tensor.blocks.length)
      (E : TensorComponentExtractionSpine R)
      (componentReplay :
        ∀ i : Fin R.tensor.blocks.length,
          InternalHolographyInterface.RecursiveReplayCongruenceSpine I
            (E.componentRecord i)),
    Nonempty (TensorReassemblyFromComponentReplayData I R E componentReplay)

/-- Exact missing primitive for the tensor branch's reassembly step.

Search of the scoped real-objects files finds replay-representative
concatenation and trace-class composition, but no constructor that tensors a
family of completed replay records back into a completed record together with
the admin/visible-boundary witnesses the manuscript uses. This structure names
that primitive exactly.

Concretely, the remaining gap is not just the tagged disjoint union on packet
indices. The current `RewriteCalculusSetup` still keeps `BoundaryObject` and
`GluingWitness` opaque, so the tensor branch lacks a generic constructor for:

- the ordered tensor boundary object of the replayed components;
- retagging/combining component attachment witnesses into one ambient record;
- the resulting admin-equivalence witness back to the ambient tensor record.

Those setup-level constructors are exactly what this target is asking to be
supplied in proof-relevant form. -/
structure CompletedRecordTensorReassemblyConstructor
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    (R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
    (E : TensorComponentExtractionSpine R)
    (componentReplay :
      ∀ i : Fin R.tensor.blocks.length,
        InternalHolographyInterface.RecursiveReplayCongruenceSpine I
          (E.componentRecord i)) where
  tensorRecord : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)
  componentEmbeddings :
    ∀ i : Fin R.tensor.blocks.length,
      Fin (InternalHolographyInterface.recursiveReplayRecord (componentReplay i)).n →
        Fin tensorRecord.n
  recordEquiv_to_original : RecordStructEquiv
      (@BoundaryAdminEquiv
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
      tensorRecord R
  visibleBoundary_tensor : I.visibleBoundary tensorRecord = I.visibleBoundary R

/-- Primitive target for constructing the tensor reassembly of replayed
components as a completed record. This is the remaining honest obstruction once
component extraction and component replay data are available. -/
def CompletedRecordTensorReassemblyConstructorTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) : Prop :=
  ∀ (R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
      (_hCompleted : R.IsCompleted) (_hTensor : 1 < R.tensor.blocks.length)
      (E : TensorComponentExtractionSpine R)
      (componentReplay :
        ∀ i : Fin R.tensor.blocks.length,
          InternalHolographyInterface.RecursiveReplayCongruenceSpine I
            (E.componentRecord i)),
    Nonempty (CompletedRecordTensorReassemblyConstructor I R E componentReplay)

/-- Setup-level tensor boundary/gluing structure specialized to the preferred
real-objects bridge setup and strengthened to produce the theorem-level tensor
reassembly constructor required by the holography tensor branch. -/
structure PreferredTensorBoundaryGluingStructure
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) where
  base : RewriteCalculusSetup.CompletedReconstructionRecord.TensorBoundaryGluingStructure
    (setup := PreferredFoundationsBridgeSetup presentation.toDoctrine aux)
  buildCompletedRecordTensorReassembly :
    ∀ (R : CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
        (_hCompleted : R.IsCompleted) (_hTensor : 1 < R.tensor.blocks.length)
        (E : TensorComponentExtractionSpine R)
        (componentReplay :
          ∀ i : Fin R.tensor.blocks.length,
            InternalHolographyInterface.RecursiveReplayCongruenceSpine I
              (E.componentRecord i)),
      Nonempty (CompletedRecordTensorReassemblyConstructor I R E componentReplay)

/-- Preferred foundations bridge tensor data induces the holography-facing
tensor boundary/gluing structure by applying the preferred reassembly
constructor to the family of recursive replay records and then transporting the
admin-equivalence witness through `visibleBoundary_respects_admin`. -/
def PreferredFoundationsTensorBoundaryGluingData.toPreferredTensorBoundaryGluingStructure
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    (tensorData : PreferredFoundationsTensorBoundaryGluingData
      presentation.toDoctrine aux) :
    PreferredTensorBoundaryGluingStructure I where
  base := tensorData.base
  buildCompletedRecordTensorReassembly := by
    intro R hCompleted hTensor E componentReplay
    let replayRecord :
        Fin R.tensor.blocks.length →
          CompletedReconstructionRecord
            (PreferredFoundationsBridgeSetup presentation.toDoctrine aux) :=
      fun i => InternalHolographyInterface.recursiveReplayRecord (componentReplay i)
    obtain ⟨T⟩ := tensorData.buildPreferredTensorReassembly
      R hCompleted hTensor replayRecord
    exact ⟨{
      tensorRecord := T.tensorRecord
      componentEmbeddings := T.componentEmbeddings
      recordEquiv_to_original := T.recordEquiv_to_original
      visibleBoundary_tensor :=
        I.visibleBoundary_respects_admin T.recordEquiv_to_original
    }⟩

/-- Preferred foundations bridge tensor data directly discharges the
holography-facing tensor constructor target. -/
theorem PreferredFoundationsTensorBoundaryGluingData_realizes_CompletedRecordTensorReassemblyConstructorTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    (tensorData : PreferredFoundationsTensorBoundaryGluingData
      presentation.toDoctrine aux) :
    CompletedRecordTensorReassemblyConstructorTarget I := by
  intro R hCompleted hTensor E componentReplay
  let tensorStructure :=
    tensorData.toPreferredTensorBoundaryGluingStructure I
  exact tensorStructure.buildCompletedRecordTensorReassembly
    R hCompleted hTensor E componentReplay

/-- Once the ambient rewrite-calculus setup supplies the tensor boundary and
gluing interface together with the induced proof-relevant reassembly witness,
the holography tensor branch's remaining constructor target is discharged. -/
theorem PreferredTensorBoundaryGluingStructure_realizes_CompletedRecordTensorReassemblyConstructorTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    PreferredTensorBoundaryGluingStructure I →
      CompletedRecordTensorReassemblyConstructorTarget I := by
  intro hTensorStructure
  intro R hCompleted hTensor E componentReplay
  exact hTensorStructure.buildCompletedRecordTensorReassembly
    R hCompleted hTensor E componentReplay

/-- The preferred tensor auxiliary extension resolves the tensor branch by
first producing preferred tensor boundary/gluing data and then applying the
existing bridge into the holography-facing constructor target. -/
theorem FoundationsTensorBoundaryGluingAuxiliaryData_realizes_CompletedRecordTensorReassemblyConstructorTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    (tensorAux : FoundationsTensorBoundaryGluingAuxiliaryData
      presentation.toDoctrine aux) :
    CompletedRecordTensorReassemblyConstructorTarget I :=
  PreferredFoundationsTensorBoundaryGluingData_realizes_CompletedRecordTensorReassemblyConstructorTarget
    I tensorAux.toPreferredFoundationsTensorBoundaryGluingData

/-- Once the preferred boundary tensor constructors are fixed concretely, a
preferred gluing-witness implementation package plus the proof-relevant tensor
reassembly constructor yields the full preferred tensor auxiliary record and
therefore discharges the holography-facing tensor constructor target. -/
theorem PreferredTensorBoundaryGluingImplementationData_realizes_CompletedRecordTensorReassemblyConstructorTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    (impl : PreferredTensorBoundaryGluingImplementationData
      presentation.toDoctrine aux)
    (buildPreferredTensorReassembly :
      ∀ (R : CompletedReconstructionRecord
            (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
          (_hCompleted : R.IsCompleted) (_hTensor : 1 < R.tensor.blocks.length)
          (componentReplay :
            Fin R.tensor.blocks.length →
              CompletedReconstructionRecord
                (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)),
        Nonempty (PreferredTensorReassemblyData aux R componentReplay)) :
    CompletedRecordTensorReassemblyConstructorTarget I :=
  FoundationsTensorBoundaryGluingAuxiliaryData_realizes_CompletedRecordTensorReassemblyConstructorTarget
    I
    (preferredTensorBoundaryGluingAuxiliaryData
      (Dc := presentation.toDoctrine) impl buildPreferredTensorReassembly)

/-- The primitive completed-record tensor reassembly constructor immediately
realizes the current proof-relevant reassembly data target by forgetting the
extra structural witness fields. -/
theorem completedRecordTensorReassemblyConstructor_realizes_TensorReassemblyFromComponentReplayDataTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    CompletedRecordTensorReassemblyConstructorTarget I →
      TensorReassemblyFromComponentReplayDataTarget I := by
  intro hTensorConstructor
  intro R hCompleted hTensor E componentReplay
  obtain ⟨T⟩ := hTensorConstructor R hCompleted hTensor E componentReplay
  exact ⟨{
    tensorReplay := T.tensorRecord
    visibleBoundary_eq := T.visibleBoundary_tensor
  }⟩

def TensorReassemblyFromComponentReplayTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) : Prop :=
  ∀ (R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
      (_hCompleted : R.IsCompleted) (_hTensor : 1 < R.tensor.blocks.length)
      (E : TensorComponentExtractionSpine R)
      (componentReplay :
        ∀ i : Fin R.tensor.blocks.length,
          InternalHolographyInterface.RecursiveReplayCongruenceSpine I
            (E.componentRecord i)),
    ∃ tensorReplay : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux),
      I.visibleBoundary tensorReplay = I.visibleBoundary R

/-- The proof-relevant tensor reassembly data target realizes the older
existential reassembly target by forgetting the packaged record and theorem
down to existence. -/
theorem tensorReassemblyFromComponentReplayData_realizes_TensorReassemblyFromComponentReplayTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    TensorReassemblyFromComponentReplayDataTarget I →
      TensorReassemblyFromComponentReplayTarget I := by
  intro hData
  intro R hCompleted hTensor E componentReplay
  obtain ⟨T⟩ := hData R hCompleted hTensor E componentReplay
  exact ⟨T.tensorReplay, T.visibleBoundary_eq⟩

structure TensorFactorReplaySpine
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    (R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)) where
  componentCount : Nat
  componentCount_eq : componentCount = R.tensor.blocks.length
  componentRecords :
    Fin componentCount →
      CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)
  componentCompletedWitness :
    ∀ i : Fin componentCount, (componentRecords i).IsCompleted
  componentReplaySpines :
    ∀ i : Fin componentCount,
      InternalHolographyInterface.QuotientVisibleReconstructionSpine I (componentRecords i)

/-- Forget the stronger component-extraction spine down to the existing
component replay-data container by filling the quotient-visible replay spines
canonically from completedness. -/
noncomputable def TensorComponentExtractionSpine.toTensorFactorReplaySpine
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    {R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)}
    (E : TensorComponentExtractionSpine R) :
    TensorFactorReplaySpine I R where
  componentCount := R.tensor.blocks.length
  componentCount_eq := rfl
  componentRecords := E.componentRecord
  componentCompletedWitness := E.componentCompleted
  componentReplaySpines :=
    fun i =>
      InternalHolographyInterface.quotientVisibleReconstructionSpine
        I (E.componentRecord i) (E.componentCompleted i)

/-- Each component replay spine in a tensor-factor replay spine already carries
the componentwise quotient-visible congruence law. -/
theorem TensorFactorReplaySpine.componentwise_visibleBoundary_eq
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {I : InternalHolographyInterface presentation aux}
    {R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)}
    (T : TensorFactorReplaySpine I R)
    (i : Fin T.componentCount) :
    I.visibleBoundary
        (RewriteCalculusSetup.PeelChain.replay
          (T.componentReplaySpines i).canonicalPeelChain) =
      I.visibleBoundary (T.componentRecords i) :=
  InternalHolographyInterface.replayedRecord_visibleBoundary_eq
    (T.componentReplaySpines i)

/-- Stronger proof-relevant tensor spine matching the manuscript's full tensor
factor case more closely.

`TensorFactorReplaySpine` records only the componentwise replay data. The
manuscript's tensor step needs more:

- a chosen representative inside each tensor block, so the canonical order can
  be read from `Key` on component representatives;
- an explicit ordering witness for those components;
- an actual reassembled completed record;
- the visible-boundary theorem for that reassembly.

This structure packages exactly that stronger tensor branch without pretending
that the current scoped files can construct it yet. -/
structure TensorReassemblyVisibleBoundarySpine
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    (R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)) where
  factorReplay : TensorFactorReplaySpine I R
  componentRepresentatives : Fin factorReplay.componentCount → Fin R.n
  componentRepresentative_mem :
    ∀ i : Fin factorReplay.componentCount,
      (R.tensor.blocks.get (Fin.cast factorReplay.componentCount_eq i))
        (componentRepresentatives i)
  componentOrder : List (Fin factorReplay.componentCount)
  componentOrder_nodup : componentOrder.Nodup
  componentOrder_complete :
    ∀ i : Fin factorReplay.componentCount, i ∈ componentOrder
  componentOrder_key_sorted :
    componentOrder.Pairwise
      (fun i j => R.key.pos (componentRepresentatives i) <
        R.key.pos (componentRepresentatives j))
  tensorReplay : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)
  visibleBoundary_eq : I.visibleBoundary tensorReplay = I.visibleBoundary R

/-- Exact stronger theorem target for the manuscript's tensor-factor branch.

This keeps the current reduced tensor target honest while naming the full
proof-relevant object still missing from the scoped Lean surface: component
replay data, canonical `Key`-ordering data on tensor factors, a reassembled
completed record, and the visible-boundary theorem for that reassembly. -/
def TensorReassemblyVisibleBoundarySpineTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) : Prop :=
  ∀ (R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
      (_hCompleted : R.IsCompleted) (_hTensor : 1 < R.tensor.blocks.length),
    Nonempty (TensorReassemblyVisibleBoundarySpine I R)

/-- Exact extraction target for the tensor branch: given a completed record with
more than one tensor block, produce proof-relevant replay spines for the block-
indexed component completed records. -/
def TensorFactorReplaySpineTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) : Prop :=
  ∀ (R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
      (_hCompleted : R.IsCompleted) (_hTensor : 1 < R.tensor.blocks.length),
    Nonempty (TensorFactorReplaySpine I R)

/-- Exact reassembly target for the tensor branch.

Once proof-relevant component replay data are available, the only remaining
tensor obligation is to reassemble those component replays into a completed
record whose visible boundary class agrees with the original tensorized record. -/
def TensorReassemblyVisibleBoundaryTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) : Prop :=
  ∀ (R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
      (_hCompleted : R.IsCompleted) (_hTensor : 1 < R.tensor.blocks.length)
      (T : TensorFactorReplaySpine I R),
    (∀ i : Fin T.componentCount,
        I.visibleBoundary
            (RewriteCalculusSetup.PeelChain.replay
              (T.componentReplaySpines i).canonicalPeelChain) =
          I.visibleBoundary (T.componentRecords i)) →
      ∃ tensorReplay : CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup presentation.toDoctrine aux),
        I.visibleBoundary tensorReplay = I.visibleBoundary R

/-- Refined tensor-factor quotient-congruence target.

The current Layer B surface cannot yet implement the manuscript's tensor case
directly, because it lacks both component-record extraction and a tensor
reassembly operator on completed records. The tensor target is therefore split
exactly into those two proof-relevant missing pieces:

- extraction of block-indexed component replay spines;
- visible-boundary compatibility for the tensor reassembly step. -/
def TensorReconstructionQuotientCongruenceTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) : Prop :=
  TensorFactorReplaySpineTarget I ∧
    TensorReassemblyVisibleBoundaryTarget I

/-- The refined tensor target is definitionally the conjunction of the
component-spine extraction target and the tensor reassembly compatibility
target. -/
theorem TensorReconstructionQuotientCongruenceTarget_iff_replaySpineAndReassembly
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    TensorReconstructionQuotientCongruenceTarget I ↔
      TensorFactorReplaySpineTarget I ∧ TensorReassemblyVisibleBoundaryTarget I :=
  Iff.rfl

/-- Componentwise quotient-visible congruence plus tensor reassembly
compatibility yields the tensor-factor quotient-congruence theorem in the
manuscript's shape: for every tensorized completed record, there is a replayed
record in the same visible boundary class. -/
theorem tensorFactorReplayAndReassembly_yield_tensorReplayVisibleBoundary
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    {I : InternalHolographyInterface presentation aux}
    (hExtract : TensorFactorReplaySpineTarget I)
    (hReassemble : TensorReassemblyVisibleBoundaryTarget I) :
    ∀ (R : CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
        (hCompleted : R.IsCompleted) (hTensor : 1 < R.tensor.blocks.length),
      ∃ tensorReplay : CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup presentation.toDoctrine aux),
        I.visibleBoundary tensorReplay = I.visibleBoundary R := by
  intro R hCompleted hTensor
  obtain ⟨T⟩ := hExtract R hCompleted hTensor
  exact hReassemble R hCompleted hTensor T
    (fun i => T.componentwise_visibleBoundary_eq i)

/-- Exact reduction from the manuscript's remaining tensor obligations to the
stronger tensor reassembly spine.

If one can extract completed component subrecords from `R.tensor.blocks` and
one can reassemble the recursive replays of those extracted components back into
the visible boundary class of `R`, then the stronger proof-relevant tensor
object `TensorReassemblyVisibleBoundarySpine` follows. -/
theorem tensorComponentExtractionAndReassembly_realize_TensorReassemblyVisibleBoundarySpineTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    TensorComponentCompletedRecordExtractionTarget
  (presentation := presentation) (aux := aux) I →
      TensorReassemblyFromComponentReplayTarget I →
        TensorReassemblyVisibleBoundarySpineTarget I := by
  intro hExtract hReassemble
  intro R hCompleted hTensor
  obtain ⟨E⟩ := hExtract R hCompleted hTensor
  let componentReplay :=
    fun i : Fin R.tensor.blocks.length =>
      InternalHolographyInterface.recursiveReplayCongruenceSpine
        I (E.componentRecord i) (E.componentCompleted i)
  obtain ⟨tensorReplay, hVisible⟩ :=
    hReassemble R hCompleted hTensor E componentReplay
  refine ⟨{
    factorReplay := E.toTensorFactorReplaySpine I
    componentRepresentatives := E.componentRepresentative
    componentRepresentative_mem := E.componentRepresentative_mem
    componentOrder := E.orderedComponents
    componentOrder_nodup := E.orderedComponents_nodup
    componentOrder_complete := E.orderedComponents_complete
    componentOrder_key_sorted := E.orderedComponents_key_sorted
    tensorReplay := tensorReplay
    visibleBoundary_eq := hVisible
  }⟩

/-- The new restricted-record family target plugs into the existing tensor
reduction chain by first projecting to `TensorComponentExtractionSpine` and then
using the already established reassembly reduction. -/
theorem restrictedCompletedRecordDataAndReassembly_realize_TensorReassemblyVisibleBoundarySpineTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    RestrictedCompletedRecordDataFamilyTarget I →
      TensorReassemblyFromComponentReplayTarget I →
        TensorReassemblyVisibleBoundarySpineTarget I := by
  intro hRestricted hReassemble
  exact
    tensorComponentExtractionAndReassembly_realize_TensorReassemblyVisibleBoundarySpineTarget
      I
      (restrictedCompletedRecordData_realizes_TensorComponentCompletedRecordExtractionTarget
        I hRestricted)
      hReassemble

/-- The proof-relevant tensor reassembly data target plugs into the same
restricted-data extraction chain by first forgetting to the existential
reassembly target and then using the existing reduction to the stronger tensor
reassembly spine. -/
theorem restrictedCompletedRecordDataAndProofRelevantReassembly_realize_TensorReassemblyVisibleBoundarySpineTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    RestrictedCompletedRecordDataFamilyTarget I →
      TensorReassemblyFromComponentReplayDataTarget I →
        TensorReassemblyVisibleBoundarySpineTarget I := by
  intro hRestricted hReassembleData
  exact
    restrictedCompletedRecordDataAndReassembly_realize_TensorReassemblyVisibleBoundarySpineTarget
      I hRestricted
      (tensorReassemblyFromComponentReplayData_realizes_TensorReassemblyFromComponentReplayTarget
        I hReassembleData)

/-- The exact missing primitive tensor constructor target plugs directly into
the current tensor chain by first yielding the proof-relevant reassembly data
target and then applying the existing reduction to the stronger tensor spine. -/
theorem restrictedCompletedRecordDataAndTensorConstructor_realize_TensorReassemblyVisibleBoundarySpineTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    RestrictedCompletedRecordDataFamilyTarget I →
      CompletedRecordTensorReassemblyConstructorTarget I →
        TensorReassemblyVisibleBoundarySpineTarget I := by
  intro hRestricted hTensorConstructor
  exact
    restrictedCompletedRecordDataAndProofRelevantReassembly_realize_TensorReassemblyVisibleBoundarySpineTarget
      I hRestricted
      (completedRecordTensorReassemblyConstructor_realizes_TensorReassemblyFromComponentReplayDataTarget
        I hTensorConstructor)

/-- A stronger manuscript-aligned tensor spine target directly realizes the
current reduced tensor quotient-congruence target.

The stronger spine packages more than the reduced target asks for: it carries
its own factor replay data, a canonical `Key`-ordering witness on tensor
factors, an explicit tensor reassembly record, and the visible-boundary theorem
for that reassembly. Since the reduced tensor target only asks for existence of
factor replay data plus existence of some reassembled visible-boundary witness,
the stronger spine discharges it immediately. -/
theorem tensorReassemblyVisibleBoundarySpine_realizes_TensorReconstructionQuotientCongruenceTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    TensorReassemblyVisibleBoundarySpineTarget I →
      TensorReconstructionQuotientCongruenceTarget I := by
  intro hSpine
  refine ⟨?_, ?_⟩
  · intro R hCompleted hTensor
    obtain ⟨S⟩ := hSpine R hCompleted hTensor
    exact ⟨S.factorReplay⟩
  · intro R hCompleted hTensor _T _hComponents
    obtain ⟨S⟩ := hSpine R hCompleted hTensor
    exact ⟨S.tensorReplay, S.visibleBoundary_eq⟩

/-- The preferred tensor implementation data closes the reduced tensor target
once the separate component-extraction target is supplied. This follows the
existing chain through the completed-record tensor constructor target. -/
theorem PreferredTensorBoundaryGluingImplementationData_realizes_TensorReconstructionQuotientCongruenceTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    (hRestricted : RestrictedCompletedRecordDataFamilyTarget I)
    (impl : PreferredTensorBoundaryGluingImplementationData
      presentation.toDoctrine aux)
    (buildPreferredTensorReassembly :
      ∀ (R : CompletedReconstructionRecord
            (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
          (_hCompleted : R.IsCompleted) (_hTensor : 1 < R.tensor.blocks.length)
          (componentReplay :
            Fin R.tensor.blocks.length →
              CompletedReconstructionRecord
                (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)),
        Nonempty (PreferredTensorReassemblyData aux R componentReplay)) :
    TensorReconstructionQuotientCongruenceTarget I := by
  apply tensorReassemblyVisibleBoundarySpine_realizes_TensorReconstructionQuotientCongruenceTarget
  apply restrictedCompletedRecordDataAndTensorConstructor_realize_TensorReassemblyVisibleBoundarySpineTarget I hRestricted
  exact
    PreferredTensorBoundaryGluingImplementationData_realizes_CompletedRecordTensorReassemblyConstructorTarget
      I impl buildPreferredTensorReassembly

/-- Global sink-peel congruence target: every completed record admits the
recursive replay spine extracted from the current delete/recurse/glue Lean
surface, and that replay preserves the visible boundary class. -/
def RecursiveSinkReplayQuotientCongruenceTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) : Prop :=
  ∀ (R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
      (hCompleted : R.IsCompleted),
    ∃ S : InternalHolographyInterface.RecursiveReplayCongruenceSpine I R,
      I.visibleBoundary
          (InternalHolographyInterface.recursiveReplayRecord S) =
        I.visibleBoundary R

/-- Admin-descent target already carried by the internal holography interface:
boundary-admin-equivalent records have equal visible boundary values. -/
def InternalHolographyAdminDescentTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) : Prop :=
  ∀ {R₁ R₂ : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)},
    RecordStructEquiv
        (@BoundaryAdminEquiv
          (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
        R₁ R₂ →
      I.visibleBoundary R₁ = I.visibleBoundary R₂

/-- Frontier-quotient compatibility target already carried by the internal
holography interface: visible-boundary equality is exactly frontier-word
equivalence. -/
def InternalHolographyFrontierQuotientCompatibilityTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) : Prop :=
  ∀ {R₁ R₂ : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)},
    I.visibleBoundary R₁ = I.visibleBoundary R₂ ↔
      FrontierWord.Equiv
        (I.holographyData.toFrontierWord R₁)
        (I.holographyData.toFrontierWord R₂)

/-- Refined global quotient-congruence target.

The earlier boundary-only target was too coarse: the manuscript's proof uses
completed-record data (`Dep`, `Attach`, `Tensor`, `Key`) and recursive replay,
not just equality of `Y`. The refined target therefore splits the global proof
into the exact theorem surfaces now visible in Lean:

- the single-packet base case;
- the still-pending tensor-factor branch;
- the recursive sink-peel replay branch;
- admin-descent;
- frontier-quotient compatibility.

This keeps the currently proved sink-peel content separate from the missing
tensor reassembly content, rather than overclaiming that boundary equality
alone forces quotient-visible agreement. -/
def InternalHolographyQuotientCongruenceTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) : Prop :=
  BaseSinglePacketQuotientCongruenceTarget I ∧
    TensorReconstructionQuotientCongruenceTarget I ∧
    RecursiveSinkReplayQuotientCongruenceTarget I ∧
    InternalHolographyAdminDescentTarget I ∧
    InternalHolographyFrontierQuotientCompatibilityTarget I

/-- The global recursive sink-peel replay spine realizes the base single-packet
case: a single-packet completed record already lies in the visible boundary
class of its canonical recursive replay. -/
theorem recursiveReplayCongruenceSpine_realizes_BaseSinglePacketQuotientCongruenceTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    BaseSinglePacketQuotientCongruenceTarget I := by
  intro R _hCompleted _hOne
  let S := InternalHolographyInterface.recursiveReplayCongruenceSpine I R _hCompleted
  exact ⟨S, InternalHolographyInterface.recursiveReplayRecord_visibleBoundary_eq S⟩

/-- The current recursive replay surface fully realizes the sink-peel branch of
the manuscript's quotient-congruence argument. -/
theorem recursiveReplayCongruenceSpine_realizes_RecursiveSinkReplayQuotientCongruenceTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    RecursiveSinkReplayQuotientCongruenceTarget I := by
  intro R hCompleted
  let S := InternalHolographyInterface.recursiveReplayCongruenceSpine I R hCompleted
  exact ⟨S, InternalHolographyInterface.recursiveReplayRecord_visibleBoundary_eq S⟩

/-- Admin-descent is already present in the internal holography interface. -/
theorem internalHolographyInterface_realizes_InternalHolographyAdminDescentTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    InternalHolographyAdminDescentTarget I := by
  intro R₁ R₂ h
  exact I.visibleBoundary_respects_admin h

/-- Frontier-quotient compatibility is already present in the internal
holography interface. -/
theorem internalHolographyInterface_realizes_InternalHolographyFrontierQuotientCompatibilityTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    InternalHolographyFrontierQuotientCompatibilityTarget I := by
  intro R₁ R₂
  exact I.visibleBoundary_eq_iff_frontierEquiv

/-- The refined global quotient-congruence target is now reduced exactly to the
still-missing tensor-factor branch. All other pieces are already realized by
the current proof-relevant replay and holography interfaces. -/
theorem InternalHolographyQuotientCongruenceTarget_iff_tensorTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    InternalHolographyQuotientCongruenceTarget I ↔
      TensorReconstructionQuotientCongruenceTarget I := by
  constructor
  · intro h
    exact h.2.1
  · intro hTensor
    exact ⟨
      recursiveReplayCongruenceSpine_realizes_BaseSinglePacketQuotientCongruenceTarget I,
      hTensor,
      recursiveReplayCongruenceSpine_realizes_RecursiveSinkReplayQuotientCongruenceTarget I,
      internalHolographyInterface_realizes_InternalHolographyAdminDescentTarget I,
      internalHolographyInterface_realizes_InternalHolographyFrontierQuotientCompatibilityTarget I
    ⟩

/-- Preferred tensor implementation data plus the separate component-
extraction target closes the full internal holography quotient-congruence
target by reducing to the already-isolated tensor branch. -/
theorem PreferredTensorBoundaryGluingImplementationData_realizes_InternalHolographyQuotientCongruenceTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux)
    (hRestricted : RestrictedCompletedRecordDataFamilyTarget I)
    (impl : PreferredTensorBoundaryGluingImplementationData
      presentation.toDoctrine aux)
    (buildPreferredTensorReassembly :
      ∀ (R : CompletedReconstructionRecord
            (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
          (_hCompleted : R.IsCompleted) (_hTensor : 1 < R.tensor.blocks.length)
          (componentReplay :
            Fin R.tensor.blocks.length →
              CompletedReconstructionRecord
                (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)),
        Nonempty (PreferredTensorReassemblyData aux R componentReplay)) :
    InternalHolographyQuotientCongruenceTarget I := by
  exact
    (InternalHolographyQuotientCongruenceTarget_iff_tensorTarget I).2
      (PreferredTensorBoundaryGluingImplementationData_realizes_TensorReconstructionQuotientCongruenceTarget
        I hRestricted impl buildPreferredTensorReassembly)

/-- Concrete preferred tensor-reassembly target with the exact ambient tensor
extraction data made explicit.

The generic preferred reassembly constructor in
`ConcreteBoundaryPresentation.lean` only receives the family of replayed
component records, but not the extraction spine that relates those records back
to the ambient tensor decomposition of `R`. The concrete tensor constructor
cannot honestly recover component embeddings or the ambient admin-equivalence
witness from replay records alone, so the concrete lane names the stronger
target directly: pass the extracted component data as well. -/
def ConcretePreferredTensorReassemblyTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation
      (concretePreferredBoundaryBridgeAuxiliaryData aux)) : Prop :=
  ∀ (R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)))
      (_hCompleted : R.IsCompleted) (_hTensor : 1 < R.tensor.blocks.length)
      (E : TensorComponentExtractionSpine R)
      (componentReplay :
        ∀ i : Fin R.tensor.blocks.length,
          InternalHolographyInterface.RecursiveReplayCongruenceSpine I
            (E.componentRecord i)),
    let replayRecord :=
      fun i : Fin R.tensor.blocks.length =>
        InternalHolographyInterface.recursiveReplayRecord (componentReplay i)
    Nonempty
      (PreferredTensorReassemblyData
        (concretePreferredBoundaryBridgeAuxiliaryData aux) R replayRecord)

/-- The concrete preferred tensor-reassembly target is already inhabited from
the current extraction spine and recursive replay data.

The preferred reassembly witness requested by the current theorem surface is
still intentionally weak: it asks only for a tensor record, component
embeddings into that record, an admin-equivalence witness back to the ambient
tensor record, and a key-order compatibility slot. The current concrete lane
can discharge this honestly by taking the ambient tensor record itself as the
reassembled record and deriving the embeddings from:

- replay-size preservation for each component replay spine; and
- the extraction spine's packet equivalence into the ambient tensor blocks.

No additional boundary/gluing wrapper is needed for this theorem-level target. -/
theorem concretePreferredTensorReassemblyTarget_inhabited
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation
      (concretePreferredBoundaryBridgeAuxiliaryData aux)) :
    ConcretePreferredTensorReassemblyTarget I := by
  intro R hCompleted hTensor E componentReplay
  dsimp [ConcretePreferredTensorReassemblyTarget]
  refine ⟨{
    tensorRecord := R
    componentEmbeddings := ?_
    recordEquiv_to_original := ?_
  }⟩
  · intro i k
    let hReplay :=
      InternalHolographyInterface.recursiveReplayRecord_recordEquiv
        (componentReplay i)
    exact ((E.componentPacketEquiv i) (Fin.cast hReplay.n_eq k)).1
  · exact
      by
        let hStruct : RecordStructEquiv Eq R R := (RecordEquiv.refl R).toStructEquiv
        refine
          { hStruct with
            Y_rel := ?_ }
        exact BoundaryAdminEquiv.refl R.Y

/-- The stronger concrete preferred tensor-reassembly target immediately
realizes the theorem-level completed-record tensor constructor target by
forgetting the extraction spine after using it to build the preferred
reassembly witness. -/
theorem concretePreferredTensorReassemblyTarget_realizes_CompletedRecordTensorReassemblyConstructorTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation
      (concretePreferredBoundaryBridgeAuxiliaryData aux)) :
    ConcretePreferredTensorReassemblyTarget I →
      CompletedRecordTensorReassemblyConstructorTarget I := by
  intro hConcrete
  intro R hCompleted hTensor E componentReplay
  let replayRecord :=
    fun i : Fin R.tensor.blocks.length =>
      InternalHolographyInterface.recursiveReplayRecord (componentReplay i)
  obtain ⟨T⟩ := hConcrete R hCompleted hTensor E componentReplay
  exact ⟨{
    tensorRecord := T.tensorRecord
    componentEmbeddings := T.componentEmbeddings
    recordEquiv_to_original := T.recordEquiv_to_original
    visibleBoundary_tensor :=
      I.visibleBoundary_respects_admin T.recordEquiv_to_original
  }⟩

/-- Concrete preferred tensor-reassembly target closes the full concrete
internal quotient-congruence target once restricted component extraction is
available. This is the sharpened forward theorem surface for the concrete
auxiliary lane. -/
private def concretePreferredInternalInterfaceLocal
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    InternalHolographyInterface presentation
      (concretePreferredBoundaryBridgeAuxiliaryData aux) :=
  concretePreferredInternalHolographyInterface
    presentation sourceExport boundaryCodes proofs

theorem concretePreferredTensorReassemblyTarget_realizes_InternalHolographyQuotientCongruenceTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (hRestricted : RestrictedCompletedRecordDataFamilyTarget
      (concretePreferredInternalInterfaceLocal
        presentation sourceExport boundaryCodes proofs))
    (hConcreteReassembly : ConcretePreferredTensorReassemblyTarget
      (concretePreferredInternalInterfaceLocal
        presentation sourceExport boundaryCodes proofs)) :
    InternalHolographyQuotientCongruenceTarget
      (concretePreferredInternalInterfaceLocal
        presentation sourceExport boundaryCodes proofs) := by
  let I := concretePreferredInternalInterfaceLocal
    presentation sourceExport boundaryCodes proofs
  have hRestrictedI : RestrictedCompletedRecordDataFamilyTarget I := by
    simpa [I, concretePreferredInternalInterfaceLocal] using hRestricted
  have hConcreteI : ConcretePreferredTensorReassemblyTarget I := by
    simpa [I, concretePreferredInternalInterfaceLocal] using hConcreteReassembly
  let hTensorData :=
    completedRecordTensorReassemblyConstructor_realizes_TensorReassemblyFromComponentReplayDataTarget
      I
      (concretePreferredTensorReassemblyTarget_realizes_CompletedRecordTensorReassemblyConstructorTarget
        I hConcreteI)
  let hSpine :=
    restrictedCompletedRecordDataAndProofRelevantReassembly_realize_TensorReassemblyVisibleBoundarySpineTarget
      I hRestrictedI hTensorData
  simpa [I, concretePreferredInternalInterfaceLocal] using
    (InternalHolographyQuotientCongruenceTarget_iff_tensorTarget I).2
      (tensorReassemblyVisibleBoundarySpine_realizes_TensorReconstructionQuotientCongruenceTarget
        I hSpine)

/-- The concrete preferred internal holography interface now closes the full
quotient-congruence target from restricted component extraction alone: the
concrete tensor reassembly target is inhabited directly. -/
theorem concretePreferredInternalHolographyInterface_realizes_InternalHolographyQuotientCongruenceTarget_of_concreteTensorReassembly
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (hRestricted : RestrictedCompletedRecordDataFamilyTarget
      (concretePreferredInternalInterfaceLocal
        presentation sourceExport boundaryCodes proofs)) :
    InternalHolographyQuotientCongruenceTarget
      (concretePreferredInternalInterfaceLocal
        presentation sourceExport boundaryCodes proofs) := by
  have hConcrete : ConcretePreferredTensorReassemblyTarget
      (concretePreferredInternalInterfaceLocal presentation sourceExport boundaryCodes proofs) :=
    concretePreferredTensorReassemblyTarget_inhabited _
  simpa [concretePreferredInternalInterfaceLocal] using
    concretePreferredTensorReassemblyTarget_realizes_InternalHolographyQuotientCongruenceTarget
      presentation sourceExport boundaryCodes proofs hRestricted hConcrete

/-- Concrete preferred auxiliary assembly theorem.

Once the boundary/source package is transported to the concrete preferred
auxiliary object, the existing restricted component-extraction target together
with direct inhabitance of the concrete preferred tensor reassembly target
close the full internal quotient-congruence target on the concrete auxiliary
setup. -/
theorem concretePreferredInternalHolographyInterface_realizes_InternalHolographyQuotientCongruenceTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (hRestricted : RestrictedCompletedRecordDataFamilyTarget
      (concretePreferredInternalInterfaceLocal
        presentation sourceExport boundaryCodes proofs)) :
    InternalHolographyQuotientCongruenceTarget
      (concretePreferredInternalInterfaceLocal
        presentation sourceExport boundaryCodes proofs) := by
  simpa [concretePreferredInternalInterfaceLocal] using
    concretePreferredInternalHolographyInterface_realizes_InternalHolographyQuotientCongruenceTarget_of_concreteTensorReassembly
      presentation sourceExport boundaryCodes proofs hRestricted

/-- Manuscript-facing alias for the concrete internal lane: the concrete
preferred internal holography interface, together with the already-closed
quotient-congruence theorem and the quotient-based frontier-word CanNF,
detects visible-boundary equality with no extra canonical-word hypothesis. -/
theorem concreteInternalHolography_implies_CanNF_detects_boundaryEquality
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (hRestricted : RestrictedCompletedRecordDataFamilyTarget
      (concretePreferredInternalInterfaceLocal
        presentation sourceExport boundaryCodes proofs))
    (O : ResidueCanonicalOrder
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux)))
    {R₁ R₂ : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux))} :
    (concretePreferredInternalInterfaceLocal
      presentation sourceExport boundaryCodes proofs).visibleBoundary R₁ =
        (concretePreferredInternalInterfaceLocal
          presentation sourceExport boundaryCodes proofs).visibleBoundary R₂ ↔
      (frontierWordEquivFrontierWordCanNF (setup :=
        PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)) O).normalize R₁ =
        (frontierWordEquivFrontierWordCanNF (setup :=
          PreferredFoundationsBridgeSetup presentation.toDoctrine
            (concretePreferredBoundaryBridgeAuxiliaryData aux)) O).normalize R₂ := by
  let I := concretePreferredInternalInterfaceLocal
    presentation sourceExport boundaryCodes proofs
  have _ : InternalHolographyQuotientCongruenceTarget I := by
    simpa [I, concretePreferredInternalInterfaceLocal] using
    concretePreferredInternalHolographyInterface_realizes_InternalHolographyQuotientCongruenceTarget
      presentation sourceExport boundaryCodes proofs hRestricted
  constructor
  · intro hVisible
    have hFrontier :
        FrontierWord.Equiv
          ((concretePreferredInternalHolographyInterface
            presentation sourceExport boundaryCodes proofs).holographyData.toFrontierWord R₁)
          ((concretePreferredInternalHolographyInterface
            presentation sourceExport boundaryCodes proofs).holographyData.toFrontierWord R₂) :=
      ((concretePreferredInternalHolographyInterface
        presentation sourceExport boundaryCodes proofs).visibleBoundary_eq_iff_frontierEquiv).1 hVisible
    exact
      (frontierWordEquivFrontierWordCanNF_detects_equality
        (setup := PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux))
        (O := O) R₁ R₂).2
        (by
          simpa [concretePreferredInternalHolographyInterface_toFrontierWord]
            using hFrontier)
  · intro hCanNF
    have hFrontier :
        FrontierWord.Equiv (FrontierWord.ofResidue R₁) (FrontierWord.ofResidue R₂) :=
      (frontierWordEquivFrontierWordCanNF_detects_equality
        (setup := PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux))
        (O := O) R₁ R₂).1 hCanNF
    exact
      ((concretePreferredInternalHolographyInterface
        presentation sourceExport boundaryCodes proofs).visibleBoundary_eq_iff_frontierEquiv).2
        (by
          simpa [concretePreferredInternalHolographyInterface_toFrontierWord]
            using hFrontier)

theorem concreteInternalHolography_implies_CanNF_of_visibleBoundary_eq
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (hRestricted : RestrictedCompletedRecordDataFamilyTarget
      (concretePreferredInternalHolographyInterface
        presentation sourceExport boundaryCodes proofs))
    (O : ResidueCanonicalOrder
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux)))
    {R₁ R₂ : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux))}
    (hVisible :
      (concretePreferredInternalHolographyInterface
        presentation sourceExport boundaryCodes proofs).visibleBoundary R₁ =
          (concretePreferredInternalHolographyInterface
            presentation sourceExport boundaryCodes proofs).visibleBoundary R₂) :
    (frontierWordEquivFrontierWordCanNF (setup :=
      PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux)) O).normalize R₁ =
      (frontierWordEquivFrontierWordCanNF (setup :=
        PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)) O).normalize R₂ :=
  (concreteInternalHolography_implies_CanNF_detects_boundaryEquality
    presentation sourceExport boundaryCodes proofs hRestricted O).1 hVisible

theorem concreteInternalHolography_implies_visibleBoundary_eq_of_CanNF
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (hRestricted : RestrictedCompletedRecordDataFamilyTarget
      (concretePreferredInternalHolographyInterface
        presentation sourceExport boundaryCodes proofs))
    (O : ResidueCanonicalOrder
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux)))
    {R₁ R₂ : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux))}
    (hCanNF :
      (frontierWordEquivFrontierWordCanNF (setup :=
        PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)) O).normalize R₁ =
        (frontierWordEquivFrontierWordCanNF (setup :=
          PreferredFoundationsBridgeSetup presentation.toDoctrine
            (concretePreferredBoundaryBridgeAuxiliaryData aux)) O).normalize R₂) :
    (concretePreferredInternalHolographyInterface
      presentation sourceExport boundaryCodes proofs).visibleBoundary R₁ =
        (concretePreferredInternalHolographyInterface
          presentation sourceExport boundaryCodes proofs).visibleBoundary R₂ :=
  (concreteInternalHolography_implies_CanNF_detects_boundaryEquality
    presentation sourceExport boundaryCodes proofs hRestricted O).2 hCanNF

theorem internalHolographyCanNFSpine_complete
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (hRestricted : RestrictedCompletedRecordDataFamilyTarget
      (concretePreferredInternalHolographyInterface
        presentation sourceExport boundaryCodes proofs))
    (O : ResidueCanonicalOrder
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux)))
    {R₁ R₂ : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux))} :
    (concretePreferredInternalHolographyInterface
      presentation sourceExport boundaryCodes proofs).visibleBoundary R₁ =
        (concretePreferredInternalHolographyInterface
          presentation sourceExport boundaryCodes proofs).visibleBoundary R₂ ↔
      (frontierWordEquivFrontierWordCanNF (setup :=
        PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)) O).normalize R₁ =
        (frontierWordEquivFrontierWordCanNF (setup :=
          PreferredFoundationsBridgeSetup presentation.toDoctrine
            (concretePreferredBoundaryBridgeAuxiliaryData aux)) O).normalize R₂ :=
  concreteInternalHolography_implies_CanNF_detects_boundaryEquality
    presentation sourceExport boundaryCodes proofs hRestricted O

/-- The concrete quotient-based CanNF package already fills the manuscript's
named target asserting that CanNF equality detects the current scaffold-level
notion of morphism equality, namely frontier-word equivalence of residues. -/
theorem frontierWordEquivFrontierWordCanNF_realizes_CanNFEqualityDetectsMorphismEqualityTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (O : ResidueCanonicalOrder
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux))) :
    CanNFEqualityDetectsMorphismEqualityTarget
      (frontierWordEquivFrontierWordCanNF (setup :=
        PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)) O)
      (fun R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)) =>
          FrontierWord.ofResidue R) := by
  refine CanNFEqualityDetectsMorphismEqualityTarget.ofImplication _ _ ?_
  intro R₁ R₂ hCanNF
  exact frontierWordEquivFrontierWordCanNF_of_normalize_eq
    (setup := PreferredFoundationsBridgeSetup presentation.toDoctrine
      (concretePreferredBoundaryBridgeAuxiliaryData aux))
    (O := O) hCanNF

/-- Downstream from the existing internal holography and quotient-based CanNF
spine, visible-boundary equality already determines frontier-word equivalence. -/
theorem concretePreferredInternalHolographyInterface_realizes_VisibleBoundaryDeterminesFrontierWordTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (hRestricted : RestrictedCompletedRecordDataFamilyTarget
      (concretePreferredInternalHolographyInterface
        presentation sourceExport boundaryCodes proofs))
    (O : ResidueCanonicalOrder
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux))) :
    VisibleBoundaryDeterminesFrontierWordTarget
      (fun R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)) =>
          (concretePreferredInternalHolographyInterface
            presentation sourceExport boundaryCodes proofs).visibleBoundary R)
      (fun R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)) =>
          FrontierWord.ofResidue R) := by
  refine VisibleBoundaryDeterminesFrontierWordTarget.ofImplication _ _ ?_
  intro R₁ R₂ hVisible
  have hCanNF :=
    concreteInternalHolography_implies_CanNF_of_visibleBoundary_eq
      presentation sourceExport boundaryCodes proofs hRestricted O hVisible
  exact frontierWordEquivFrontierWordCanNF_of_normalize_eq
    (setup := PreferredFoundationsBridgeSetup presentation.toDoctrine
      (concretePreferredBoundaryBridgeAuxiliaryData aux))
    (O := O) hCanNF

/-- Once structured comparison data determine the visible boundary, the current
internal holography / CanNF spine already forces equality of the quotient-based
canonical normal forms. -/
theorem concretePreferredInternalHolographyInterface_comparisonToCanNFEquality
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (hRestricted : RestrictedCompletedRecordDataFamilyTarget
      (concretePreferredInternalHolographyInterface
        presentation sourceExport boundaryCodes proofs))
    (O : ResidueCanonicalOrder
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux)))
    {α : Type _}
    (comparison :
      CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup presentation.toDoctrine
            (concretePreferredBoundaryBridgeAuxiliaryData aux)) → α)
    (hComparison : StructuredComparisonDeterminesVisibleBoundaryTarget
      comparison
      (fun R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)) =>
          (concretePreferredInternalHolographyInterface
            presentation sourceExport boundaryCodes proofs).visibleBoundary R))
    {R₁ R₂ : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux))} :
    comparison R₁ = comparison R₂ →
      (frontierWordEquivFrontierWordCanNF (setup :=
        PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)) O).normalize R₁ =
        (frontierWordEquivFrontierWordCanNF (setup :=
          PreferredFoundationsBridgeSetup presentation.toDoctrine
            (concretePreferredBoundaryBridgeAuxiliaryData aux)) O).normalize R₂ := by
  intro hCmp
  have hVisible := hComparison.determinesVisibleBoundary hCmp
  have hFrontier :=
    (concretePreferredInternalHolographyInterface_realizes_VisibleBoundaryDeterminesFrontierWordTarget
      presentation sourceExport boundaryCodes proofs hRestricted O).determinesFrontierWord hVisible
  exact frontierWordEquivFrontierWordCanNF_normalize_eq_of_equiv
    (setup := PreferredFoundationsBridgeSetup presentation.toDoctrine
      (concretePreferredBoundaryBridgeAuxiliaryData aux))
    (O := O) hFrontier

/-- The downstream part of the hard theorem is now discharged: the only
remaining input is the theorem that structured comparison equality determines
the visible boundary. Everything after that point follows from internal
holography and the quotient-based CanNF spine. -/
theorem concretePreferredInternalHolographyInterface_comparisonToBoundaryFaithfulness
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (hRestricted : RestrictedCompletedRecordDataFamilyTarget
      (concretePreferredInternalHolographyInterface
        presentation sourceExport boundaryCodes proofs))
    (O : ResidueCanonicalOrder
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux)))
    {α : Type _}
    (comparison :
      CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup presentation.toDoctrine
            (concretePreferredBoundaryBridgeAuxiliaryData aux)) → α)
    (hComparison : StructuredComparisonDeterminesVisibleBoundaryTarget
      comparison
      (fun R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)) =>
          (concretePreferredInternalHolographyInterface
            presentation sourceExport boundaryCodes proofs).visibleBoundary R))
    {R₁ R₂ : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux))} :
    comparison R₁ = comparison R₂ →
      FrontierWord.Equiv (FrontierWord.ofResidue R₁) (FrontierWord.ofResidue R₂) := by
  intro hCmp
  have hCanNF :=
    concretePreferredInternalHolographyInterface_comparisonToCanNFEquality
      presentation sourceExport boundaryCodes proofs hRestricted O comparison hComparison hCmp
  exact
    (frontierWordEquivFrontierWordCanNF_realizes_CanNFEqualityDetectsMorphismEqualityTarget
      presentation O).detectsMorphismEquality hCanNF

/-- Manuscript-facing CBR statement on the concrete preferred internal lane.

This is the current formalization of classical boundary reflection: equality of
the chosen structured comparison data forces equality of the visible boundary
value carried by the concrete preferred internal holography interface. -/
def concretePreferredClassicalBoundaryReflectionStatement
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    {α : Type _}
    (comparison :
      CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup presentation.toDoctrine
            (concretePreferredBoundaryBridgeAuxiliaryData aux)) → α) : Prop :=
  ∀ {R₁ R₂ : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux))},
    comparison R₁ = comparison R₂ →
      (concretePreferredInternalInterfaceLocal
        presentation sourceExport boundaryCodes proofs).visibleBoundary R₁ =
        (concretePreferredInternalInterfaceLocal
          presentation sourceExport boundaryCodes proofs).visibleBoundary R₂

/-- Manuscript-facing CSPC statement on the concrete preferred internal lane.

This is the current formalization of the classical structured period
conjecture: equality of the chosen structured comparison data forces equality
of canonical words, represented here by frontier-word equivalence on residues. -/
def concretePreferredClassicalStructuredPeriodConjectureStatement
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    {α : Type _}
    (comparison :
      CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup presentation.toDoctrine
            (concretePreferredBoundaryBridgeAuxiliaryData aux)) → α) : Prop :=
  ∀ {R₁ R₂ : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux))},
    comparison R₁ = comparison R₂ →
      FrontierWord.Equiv (FrontierWord.ofResidue R₁) (FrontierWord.ofResidue R₂)

/-- Any proof-relevant comparison-to-visible-boundary target realizes the
manuscript CBR proposition on the concrete preferred internal lane. -/
theorem concretePreferredClassicalBoundaryReflectionStatement_of_target
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    {α : Type _}
    (comparison :
      CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup presentation.toDoctrine
            (concretePreferredBoundaryBridgeAuxiliaryData aux)) → α)
    (hComparison : StructuredComparisonDeterminesVisibleBoundaryTarget
      comparison
      (fun R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)) =>
          (concretePreferredInternalHolographyInterface
            presentation sourceExport boundaryCodes proofs).visibleBoundary R)) :
    concretePreferredClassicalBoundaryReflectionStatement
      presentation sourceExport boundaryCodes proofs comparison := by
  intro R₁ R₂ hCmp
  exact hComparison.determinesVisibleBoundary hCmp

/-- CBR implies the classical structured period conjecture on the concrete
preferred internal lane. -/
theorem concretePreferred_classicalStructuredPeriodConjecture_of_boundaryReflection
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (hRestricted : RestrictedCompletedRecordDataFamilyTarget
      (concretePreferredInternalHolographyInterface
        presentation sourceExport boundaryCodes proofs))
    (O : ResidueCanonicalOrder
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux)))
    {α : Type _}
    (comparison :
      CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup presentation.toDoctrine
            (concretePreferredBoundaryBridgeAuxiliaryData aux)) → α)
    (hCBR : concretePreferredClassicalBoundaryReflectionStatement
      presentation sourceExport boundaryCodes proofs comparison) :
    concretePreferredClassicalStructuredPeriodConjectureStatement
      presentation sourceExport boundaryCodes proofs comparison := by
  intro R₁ R₂ hCmp
  have hVisible := hCBR hCmp
  exact
    (concretePreferredInternalHolographyInterface_realizes_VisibleBoundaryDeterminesFrontierWordTarget
      presentation sourceExport boundaryCodes proofs hRestricted O).determinesFrontierWord hVisible

/-- The classical structured period conjecture implies CBR on the concrete
preferred internal lane. -/
theorem concretePreferred_boundaryReflection_of_classicalStructuredPeriodConjecture
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    {α : Type _}
    (comparison :
      CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup presentation.toDoctrine
            (concretePreferredBoundaryBridgeAuxiliaryData aux)) → α)
    (hCSPC : concretePreferredClassicalStructuredPeriodConjectureStatement
      presentation sourceExport boundaryCodes proofs comparison) :
    concretePreferredClassicalBoundaryReflectionStatement
      presentation sourceExport boundaryCodes proofs comparison := by
  intro R₁ R₂ hCmp
  have hFrontier : FrontierWord.Equiv (FrontierWord.ofResidue R₁) (FrontierWord.ofResidue R₂) :=
    hCSPC hCmp
  exact
    (concretePreferredInternalHolographyInterface
      presentation sourceExport boundaryCodes proofs).visibleBoundary_eq_of_frontierEquiv
      (by simpa [concretePreferredInternalHolographyInterface_toFrontierWord] using hFrontier)

/-- Manuscript-facing `thm:cbr-equivalence` on the concrete preferred equality
carrier: classical boundary reflection is equivalent to the classical
structured period conjecture. -/
theorem concretePreferred_cbr_equivalence
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (hRestricted : RestrictedCompletedRecordDataFamilyTarget
      (concretePreferredInternalHolographyInterface
        presentation sourceExport boundaryCodes proofs))
    (O : ResidueCanonicalOrder
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux)))
    {α : Type _}
    (comparison :
      CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup presentation.toDoctrine
            (concretePreferredBoundaryBridgeAuxiliaryData aux)) → α) :
    concretePreferredClassicalBoundaryReflectionStatement
        presentation sourceExport boundaryCodes proofs comparison ↔
      concretePreferredClassicalStructuredPeriodConjectureStatement
        presentation sourceExport boundaryCodes proofs comparison := by
  constructor
  · intro hCBR
    exact concretePreferred_classicalStructuredPeriodConjecture_of_boundaryReflection
      presentation sourceExport boundaryCodes proofs hRestricted O comparison hCBR
  · intro hCSPC
    exact concretePreferred_boundaryReflection_of_classicalStructuredPeriodConjecture
      presentation sourceExport boundaryCodes proofs comparison hCSPC

/-- Manuscript-facing `cor:classical-period-conjecture` on the concrete
preferred equality carrier. This is the corollary form of
`concretePreferred_cbr_equivalence`. -/
theorem concretePreferred_classical_period_conjecture
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (hRestricted : RestrictedCompletedRecordDataFamilyTarget
      (concretePreferredInternalHolographyInterface
        presentation sourceExport boundaryCodes proofs))
    (O : ResidueCanonicalOrder
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux)))
    {α : Type _}
    (comparison :
      CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup presentation.toDoctrine
            (concretePreferredBoundaryBridgeAuxiliaryData aux)) → α) :
    concretePreferredClassicalStructuredPeriodConjectureStatement
        presentation sourceExport boundaryCodes proofs comparison ↔
      concretePreferredClassicalBoundaryReflectionStatement
        presentation sourceExport boundaryCodes proofs comparison := by
  simpa [Iff.comm] using
    concretePreferred_cbr_equivalence
      presentation sourceExport boundaryCodes proofs hRestricted O comparison

/-- Bundle the already-proved downstream steps of the comparison-to-boundary
faithfulness theorem for the concrete preferred internal holography lane. The
only unproved input carried here is the structured-comparison-to-visible-
boundary theorem target. -/
def concretePreferredInternalHolographyInterface_realizes_ComparisonToBoundaryFaithfulnessDecompositionTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport : LayerBSourceExportData presentation aux)
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (hRestricted : RestrictedCompletedRecordDataFamilyTarget
      (concretePreferredInternalHolographyInterface
        presentation sourceExport boundaryCodes proofs))
    (O : ResidueCanonicalOrder
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux)))
    {α : Type _}
    (comparison :
      CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup presentation.toDoctrine
            (concretePreferredBoundaryBridgeAuxiliaryData aux)) → α)
    (hComparison : StructuredComparisonDeterminesVisibleBoundaryTarget
      comparison
      (fun R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)) =>
          (concretePreferredInternalHolographyInterface
            presentation sourceExport boundaryCodes proofs).visibleBoundary R)) :
    ComparisonToBoundaryFaithfulnessDecompositionTarget
      comparison
      (fun R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)) =>
          (concretePreferredInternalHolographyInterface
            presentation sourceExport boundaryCodes proofs).visibleBoundary R)
      (fun R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)) =>
          FrontierWord.ofResidue R)
      (frontierWordEquivFrontierWordCanNF (setup :=
        PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)) O) :=
  ComparisonToBoundaryFaithfulnessDecompositionTarget.ofFields
    comparison
    (fun R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux)) =>
        (concretePreferredInternalHolographyInterface
          presentation sourceExport boundaryCodes proofs).visibleBoundary R)
    (fun R : CompletedReconstructionRecord
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux)) =>
        FrontierWord.ofResidue R)
    (frontierWordEquivFrontierWordCanNF (setup :=
      PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux)) O)
    hComparison
    (concretePreferredInternalHolographyInterface_realizes_VisibleBoundaryDeterminesFrontierWordTarget
      presentation sourceExport boundaryCodes proofs hRestricted O)
    (frontierWordEquivFrontierWordCanNF_realizes_CanNFEqualityDetectsMorphismEqualityTarget
      presentation O)
    (fun {R₁ R₂} =>
      concretePreferredInternalHolographyInterface_comparisonToCanNFEquality
        presentation sourceExport boundaryCodes proofs hRestricted O comparison hComparison)
    (fun {R₁ R₂} =>
      concretePreferredInternalHolographyInterface_comparisonToBoundaryFaithfulness
        presentation sourceExport boundaryCodes proofs hRestricted O comparison hComparison)

  /-- The concrete preferred internal holography lane now fills the manuscript's
  internal comparison-faithfulness target: visible-boundary equality is detected
  exactly by the existing quotient-based CanNF package. -/
  theorem concretePreferredInternalHolographyInterface_realizes_InternalComparisonFaithfulnessTarget
      {primitive : NamedPrimitiveInterfacePresentation}
      (presentation : NamedDoctrinePresentation primitive)
      {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
      (sourceExport : LayerBSourceExportData presentation aux)
      (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
      (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
      (hRestricted : RestrictedCompletedRecordDataFamilyTarget
        (concretePreferredInternalHolographyInterface
          presentation sourceExport boundaryCodes proofs))
      (O : ResidueCanonicalOrder
        (PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux))) :
      InternalComparisonFaithfulnessTarget
        (fun R : CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup presentation.toDoctrine
            (concretePreferredBoundaryBridgeAuxiliaryData aux)) =>
            (concretePreferredInternalHolographyInterface
              presentation sourceExport boundaryCodes proofs).visibleBoundary R)
        (frontierWordEquivFrontierWordCanNF (setup :=
          PreferredFoundationsBridgeSetup presentation.toDoctrine
            (concretePreferredBoundaryBridgeAuxiliaryData aux)) O) := by
    refine InternalComparisonFaithfulnessTarget.ofIff _ _ ?_
    intro R₁ R₂
    exact
      concreteInternalHolography_implies_CanNF_detects_boundaryEquality
        presentation sourceExport boundaryCodes proofs hRestricted O

  /-- Preferred concrete internal manuscript spine target. The preferred concrete
  setup already carries a genuine syntactic boundary presentation through the
  concrete internal holography interface, so the summary manuscript spine is
  inhabited directly from existing data.

  Field **(H)** is closed via
  `semanticQuotientFrontierWordCompleteNormalizer`
  (see `INV CanNF-Contract`). This is semantic quotient closure, not an
  executable CanNF algorithm. No external obligation parameter required. -/
  noncomputable def concretePreferredInternalManuscriptSpineTarget
      {primitive : NamedPrimitiveInterfacePresentation}
      (presentation : NamedDoctrinePresentation primitive)
      {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
      (sourceExport : LayerBSourceExportData presentation aux)
      (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
      (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
      (hRestricted : RestrictedCompletedRecordDataFamilyTarget
        (concretePreferredInternalHolographyInterface
          presentation sourceExport boundaryCodes proofs))
      (O : ResidueCanonicalOrder
        (PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux))) :
      InternalManuscriptSpineTarget
        (PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux))
        (concretePreferredSyntacticBoundaryPresentation
          presentation sourceExport boundaryCodes proofs)
        (fun R : CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup presentation.toDoctrine
            (concretePreferredBoundaryBridgeAuxiliaryData aux)) =>
            (concretePreferredInternalHolographyInterface
              presentation sourceExport boundaryCodes proofs).visibleBoundary R)
        (frontierWordEquivFrontierWordCanNF (setup :=
          PreferredFoundationsBridgeSetup presentation.toDoctrine
            (concretePreferredBoundaryBridgeAuxiliaryData aux)) O) :=
    InternalManuscriptSpineTarget.ofPresentationClosed
      (concretePreferredSyntacticBoundaryPresentation
        presentation sourceExport boundaryCodes proofs)
      (fun R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)) =>
          (concretePreferredInternalHolographyInterface
            presentation sourceExport boundaryCodes proofs).visibleBoundary R)
      (frontierWordEquivFrontierWordCanNF (setup :=
        PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)) O)
      (concretePreferredInternalHolographyInterface_realizes_InternalComparisonFaithfulnessTarget
        presentation sourceExport boundaryCodes proofs hRestricted O)

  /-- Preferred concrete internal manuscript spine target through the
  executable CanNF route.

  This is the computational sibling of
  `concretePreferredInternalManuscriptSpineTarget`: the same lower preferred
  boundary/holography data are packaged, but field **(H)** is closed using a
  proof-relevant `ComputationalFrontierNormalizer` rather than the semantic
  quotient normalizer. -/
  noncomputable def concretePreferredInternalManuscriptSpineTargetComputational
      {primitive : NamedPrimitiveInterfacePresentation}
      (presentation : NamedDoctrinePresentation primitive)
      {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
      (sourceExport : LayerBSourceExportData presentation aux)
      (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
      (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
      (hRestricted : RestrictedCompletedRecordDataFamilyTarget
        (concretePreferredInternalHolographyInterface
          presentation sourceExport boundaryCodes proofs))
      (O : ResidueCanonicalOrder
        (PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)))
      (N : ComputationalFrontierNormalizer
        (PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux))) :
      InternalManuscriptSpineTarget
        (PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux))
        (concretePreferredSyntacticBoundaryPresentation
          presentation sourceExport boundaryCodes proofs)
        (fun R : CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup presentation.toDoctrine
            (concretePreferredBoundaryBridgeAuxiliaryData aux)) =>
            (concretePreferredInternalHolographyInterface
              presentation sourceExport boundaryCodes proofs).visibleBoundary R)
        (frontierWordEquivFrontierWordCanNF (setup :=
          PreferredFoundationsBridgeSetup presentation.toDoctrine
            (concretePreferredBoundaryBridgeAuxiliaryData aux)) O) :=
    InternalManuscriptSpineTarget.ofPresentationComputational
      (concretePreferredSyntacticBoundaryPresentation
        presentation sourceExport boundaryCodes proofs)
      (fun R : CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)) =>
          (concretePreferredInternalHolographyInterface
            presentation sourceExport boundaryCodes proofs).visibleBoundary R)
      (frontierWordEquivFrontierWordCanNF (setup :=
        PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux)) O)
      (concretePreferredInternalHolographyInterface_realizes_InternalComparisonFaithfulnessTarget
        presentation sourceExport boundaryCodes proofs hRestricted O)
      N

/-- Assemble the cautious bridge payload directly from the real
`LayerB.MotivicLocalization` candidate path and the candidate-specific witness
clusters. The localization seam is derived from `ML`; the remaining witness
obligations stay explicit inputs. -/
def layerBSourceExportData_fromMotivicLocalizationCandidate
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (pkg : NamedFreeSourceHolographyPackage presentation aux)
    (ML : LayerB.MotivicLocalization)
    (symmetricMonoidalWitness : MotivicLocalizationSymmetricMonoidalWitness ML)
    (stableTriangulatedWitness : MotivicLocalizationStableTriangulatedWitness ML)
    (localGeometryWitness : MotivicLocalizationLocalGeometryWitness ML)
    (tateWitness : MotivicLocalizationTateWitness ML) :
    LayerBSourceExportData presentation aux where
  pkg := pkg
  concreteSource := layerBConcreteSourceDataCandidate presentation aux ML
  localizationData :=
    layerBConcreteSourceDataCandidate_localizationInterfaceData presentation aux ML
  symmetricMonoidalWitness :=
    MotivicLocalizationSymmetricMonoidalWitness.toLayerBSymmetricMonoidalWitness
      (presentation := presentation) (aux := aux) symmetricMonoidalWitness
  stableTriangulatedWitness :=
    MotivicLocalizationStableTriangulatedWitness.toLayerBStableTriangulatedWitness
      (presentation := presentation) (aux := aux) stableTriangulatedWitness
  localGeometryWitness :=
    MotivicLocalizationLocalGeometryWitness.toLayerBLocalGeometryWitness
      (presentation := presentation) (aux := aux) localGeometryWitness
  tateWitness :=
    MotivicLocalizationTateWitness.toLayerBTateWitness
      (presentation := presentation) (aux := aux) tateWitness

/-- Build the combined internal holography interface from the existing
named/free holography package plus the real `MotivicLocalization` candidate
path and explicit witness clusters. -/
def internalHolographyInterface_fromMotivicLocalizationCandidate
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (pkg : NamedFreeSourceHolographyPackage presentation aux)
    (ML : LayerB.MotivicLocalization)
    (symmetricMonoidalWitness : MotivicLocalizationSymmetricMonoidalWitness ML)
    (stableTriangulatedWitness : MotivicLocalizationStableTriangulatedWitness ML)
    (localGeometryWitness : MotivicLocalizationLocalGeometryWitness ML)
    (tateWitness : MotivicLocalizationTateWitness ML) :
    InternalHolographyInterface presentation aux where
  boundaryReconstruction :=
    preferredBoundaryReconstructionInterface (Dc := presentation.toDoctrine) aux
  preferredBoundaryWitness := pkg.preferredBoundaryWitness
  holographyData := pkg.holographyData
  boundaryPresentation := pkg.boundaryPresentation
  frontierQuotientRealization :=
    syntactic_boundary_presentation_gives_holographic_quotient_realization
      pkg.boundaryPresentation
  residueHolography := by
    intro R₁ R₂
    simpa using pkg.residueHolography (R₁ := R₁) (R₂ := R₂)
  sourceExport :=
    layerBSourceExportData_fromMotivicLocalizationCandidate
      (pkg := pkg) ML symmetricMonoidalWitness stableTriangulatedWitness
      localGeometryWitness tateWitness

/-- Forget the cautious Layer B bridge payload down to the abstract Layer D
source-trace package seam. -/
def layerBSourceExportData_to_SourceTracePackage
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (exportData : LayerBSourceExportData presentation aux) :
    LayerD.SourceTracePackage :=
  exportData.concreteSource.toSourceTracePackage
    exportData.localizationData
    exportData.symmetricMonoidalWitness
    exportData.stableTriangulatedWitness
    exportData.localGeometryWitness
    exportData.tateWitness

namespace InternalHolographyInterface

/-- Forget the internal holography interface down to the existing Layer D
source-trace package seam. -/
def toSourceTracePackage
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    LayerD.SourceTracePackage :=
  layerBSourceExportData_to_SourceTracePackage I.sourceExport

/-- Stronger seam theorem: the internal holography interface feeds the concrete
source-construction theorem carried by the existing Layer D source package. -/
theorem feeds_sourceConstructionReadiness
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (I : InternalHolographyInterface presentation aux) :
    (I.toSourceTracePackage).sourceConstructionReadiness :=
  LayerD.SourceTracePackage.sourceConstructionReadiness_holds
    I.toSourceTracePackage

/-- The combined internal holography interface feeds the Layer D source seam
through the existing candidate export helper exactly as intended. -/
theorem internalHolographyInterface_fromMotivicLocalizationCandidate_feeds_sourceConstructionReadiness
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (pkg : NamedFreeSourceHolographyPackage presentation aux)
    (ML : LayerB.MotivicLocalization)
    (symmetricMonoidalWitness : MotivicLocalizationSymmetricMonoidalWitness ML)
    (stableTriangulatedWitness : MotivicLocalizationStableTriangulatedWitness ML)
    (localGeometryWitness : MotivicLocalizationLocalGeometryWitness ML)
    (tateWitness : MotivicLocalizationTateWitness ML) :
    let I :=
      internalHolographyInterface_fromMotivicLocalizationCandidate
        (pkg := pkg) ML symmetricMonoidalWitness stableTriangulatedWitness
        localGeometryWitness tateWitness
    (I.toSourceTracePackage).sourceConstructionReadiness := by
  exact
    (internalHolographyInterface_fromMotivicLocalizationCandidate
      (pkg := pkg) ML symmetricMonoidalWitness stableTriangulatedWitness
      localGeometryWitness tateWitness).feeds_sourceConstructionReadiness

end InternalHolographyInterface

/-- For the `MotivicLocalization`-generated candidate path, the explicit
symmetric-monoidal theorem surface is written directly onto the Layer D source
package through the existing export seam. No monoidal obligation is collapsed
into definitional equality here: the bridge only forwards the supplied theorem
fields. -/
theorem motivicLocalization_candidate_symmetricMonoidalWitness_feeds_SourceTracePackage
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (pkg : NamedFreeSourceHolographyPackage presentation aux)
    (ML : LayerB.MotivicLocalization)
    (symmetricMonoidalWitness : MotivicLocalizationSymmetricMonoidalWitness ML)
    (stableTriangulatedWitness :
      MotivicLocalizationStableTriangulatedWitness ML)
    (localGeometryWitness :
      MotivicLocalizationLocalGeometryWitness ML)
    (tateWitness : MotivicLocalizationTateWitness ML) :
    let exportData :=
      layerBSourceExportData_fromMotivicLocalizationCandidate
        (pkg := pkg) ML symmetricMonoidalWitness stableTriangulatedWitness
        localGeometryWitness tateWitness
    let sourcePackage := layerBSourceExportData_to_SourceTracePackage exportData
    sourcePackage.symmetricMonoidalPiZero = symmetricMonoidalWitness.symmetricMonoidalPiZero ∧
      sourcePackage.symmetricMonoidalInfinity = symmetricMonoidalWitness.symmetricMonoidalInfinity := by
  exact ⟨rfl, rfl⟩

/-- For the `MotivicLocalization`-generated candidate path, the explicit
stable/triangulated theorem surface is written directly onto the Layer D source package
exactly through the existing export seam. -/
theorem motivicLocalization_candidate_stableTriangulatedWitness_feeds_SourceTracePackage
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (pkg : NamedFreeSourceHolographyPackage presentation aux)
    (ML : LayerB.MotivicLocalization)
    (symmetricMonoidalWitness : MotivicLocalizationSymmetricMonoidalWitness ML)
    (stableTriangulatedWitness : MotivicLocalizationStableTriangulatedWitness ML)
    (localGeometryWitness : MotivicLocalizationLocalGeometryWitness ML)
    (tateWitness : MotivicLocalizationTateWitness ML) :
    let exportData :=
      layerBSourceExportData_fromMotivicLocalizationCandidate
        (pkg := pkg) ML symmetricMonoidalWitness stableTriangulatedWitness
        localGeometryWitness tateWitness
    let sourcePackage := layerBSourceExportData_to_SourceTracePackage exportData
    sourcePackage.triangulatedStablePiZero = stableTriangulatedWitness.triangulatedStablePiZero ∧
      sourcePackage.triangulatedStableInfinity = stableTriangulatedWitness.triangulatedStableInfinity := by
  exact ⟨rfl, rfl⟩

/-- For the `MotivicLocalization`-generated candidate path, the explicit
local-geometry theorem surface is written directly onto the Layer D source package
exactly through the existing export seam. -/
theorem motivicLocalization_candidate_localGeometryWitness_feeds_SourceTracePackage
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (pkg : NamedFreeSourceHolographyPackage presentation aux)
    (ML : LayerB.MotivicLocalization)
    (symmetricMonoidalWitness : MotivicLocalizationSymmetricMonoidalWitness ML)
    (stableTriangulatedWitness : MotivicLocalizationStableTriangulatedWitness ML)
    (localGeometryWitness : MotivicLocalizationLocalGeometryWitness ML)
    (tateWitness : MotivicLocalizationTateWitness ML) :
    let exportData :=
      layerBSourceExportData_fromMotivicLocalizationCandidate
        (pkg := pkg) ML symmetricMonoidalWitness stableTriangulatedWitness
        localGeometryWitness tateWitness
    let sourcePackage := layerBSourceExportData_to_SourceTracePackage exportData
    sourcePackage.a1InvariancePiZero = localGeometryWitness.a1InvariancePiZeroTicket.theoremTarget ∧
      sourcePackage.a1InvarianceInfinity =
        localGeometryWitness.a1InvarianceInfinityTicket.a1InvarianceInfinity ∧
      sourcePackage.nisnevichDescentPiZero =
        localGeometryWitness.nisnevichDescentPiZeroTicket.nisnevichDescentPiZero ∧
      sourcePackage.nisnevichDescentInfinity =
        localGeometryWitness.nisnevichDescentInfinityTicket.nisnevichDescentInfinity ∧
      sourcePackage.localizationPiZero =
        localGeometryWitness.localizationPiZeroTicket.verdierLocalizationPiZeroShadow ∧
      sourcePackage.localizationInfinity =
        localGeometryWitness.localizationInfinityTicket.localizationUniversalPropertyInfinity := by
  exact ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, rfl⟩⟩⟩⟩⟩

/-- For the `MotivicLocalization`-generated candidate path, the explicit Tate
theorem surface is written directly onto the Layer D source package exactly through the
existing export seam. -/
theorem motivicLocalization_candidate_tateWitness_feeds_SourceTracePackage
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine)
    (pkg : NamedFreeSourceHolographyPackage presentation aux)
    (ML : LayerB.MotivicLocalization)
    (symmetricMonoidalWitness : MotivicLocalizationSymmetricMonoidalWitness ML)
    (stableTriangulatedWitness : MotivicLocalizationStableTriangulatedWitness ML)
    (localGeometryWitness : MotivicLocalizationLocalGeometryWitness ML)
    (tateWitness : MotivicLocalizationTateWitness ML) :
    let exportData :=
      layerBSourceExportData_fromMotivicLocalizationCandidate
        (pkg := pkg) ML symmetricMonoidalWitness stableTriangulatedWitness
        localGeometryWitness tateWitness
    let sourcePackage := layerBSourceExportData_to_SourceTracePackage exportData
    sourcePackage.tateStabilizationPiZero = tateWitness.tateStabilizationPiZero ∧
      sourcePackage.tateStabilizationInfinity = tateWitness.tateStabilizationInfinity := by
  exact ⟨rfl, rfl⟩

end FoundationsBoundaryBridgeAuxiliaryData
end RewriteCalculusSetup
end RealObjects
end LayerB
end TraceCalc
