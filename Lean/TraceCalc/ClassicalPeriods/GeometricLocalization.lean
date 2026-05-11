import TraceCalc.ClassicalPeriods.GeometricRealizations
import TraceCalc.ClassicalPeriods.GraphCorrespondences

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

/-- Trace-native cylinder/endpoints packet for future $\mathbb A^1$ replay soundness. -/
structure A1CylinderEndpointReplayTarget where
  ReplayWitness : Type w
  replayWitness : ReplayWitness
  basePacketTarget : Prop
  cylinderPacketTarget : Prop
  endpointZeroPacketTarget : Prop
  endpointOnePacketTarget : Prop
  cylinderReplayTarget : Prop
  endpointZeroReplayTarget : Prop
  endpointOneReplayTarget : Prop
  endpointAgreementTarget : Prop
  endpointComparisonNaturalityTarget : Prop

/-- Trace-native replay packet intended to be the primitive source of $\mathbb A^1$ invariance. -/
structure CertifiedA1HomotopyReplayData
    (ctx : ClassicalComparisonContext.{u, v})
  (endpointAgreementTarget homotopyInvarianceTarget : Sort _) where
  cylinderEndpointReplayTarget : A1CylinderEndpointReplayTarget
  baseBettiReplayTarget : Prop
  cylinderBettiReplayTarget : Prop
  baseDeRhamReplayTarget : Prop
  cylinderDeRhamReplayTarget : Prop
  projectionZeroComparisonNaturalityTarget : Prop
  projectionOneComparisonNaturalityTarget : Prop
  endpointAgreement_holds : endpointAgreementTarget
  homotopyInvariance_holds : homotopyInvarianceTarget

/-- Theorem-target interface for $^1$-invariance on geometric source objects.

This is only a typed host for the future geometric theorem. It records which realization-object
indices are meant to be related by the affine-line extension and the compatibility targets that
the corresponding comparison data should satisfy. -/
structure GeometricA1InvarianceTarget
    (ctx : ClassicalComparisonContext.{u, v})
    (realization : GeometricRealizationFunctorData ctx) where
  affineLineIndex : realization.ObjectIndex → realization.ObjectIndex
  objectAssignmentTarget :
    ∀ idx : realization.ObjectIndex,
      let sourceObject := realization.geometricObject idx
      let affineObject := realization.geometricObject (affineLineIndex idx)
      sourceObject.geometricAdmissibilityTarget ∧
        affineObject.geometricAdmissibilityTarget
  comparisonInvarianceTarget : Prop
  framedExtractionInvarianceTarget : Prop
  traceNativeHomotopyReplayData :
    CertifiedA1HomotopyReplayData ctx
      comparisonInvarianceTarget
      framedExtractionInvarianceTarget

namespace GeometricA1InvarianceTarget

theorem a1EndpointAgreement_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (target : GeometricA1InvarianceTarget ctx realization) :
    target.comparisonInvarianceTarget :=
  target.traceNativeHomotopyReplayData.endpointAgreement_holds

theorem a1HomotopyInvariance_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (target : GeometricA1InvarianceTarget ctx realization) :
    target.framedExtractionInvarianceTarget :=
  target.traceNativeHomotopyReplayData.homotopyInvariance_holds

theorem a1HomotopyInvarianceShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (target : GeometricA1InvarianceTarget ctx realization) :
    target.framedExtractionInvarianceTarget :=
  target.a1HomotopyInvariance_from_certifiedReplay

end GeometricA1InvarianceTarget

/-- Theorem-target interface for Nisnevich descent on geometric source objects. -/
structure NisSquareOverlapGluingTarget where
  ReplayWitness : Type w
  replayWitness : ReplayWitness
  basePacketTarget : Prop
  patchPacketTarget : Prop
  overlapPacketTarget : Prop
  basePatchAgreementOnOverlapTarget : Prop
  gluedReplayTarget : Prop
  gluedReplayRestrictsToBaseTarget : Prop
  gluedReplayRestrictsToPatchTarget : Prop
  overlapComparisonNaturalityTarget : Prop

/-- Trace-native Nis replay package intended to be the primitive source of descent compatibility. -/
structure CertifiedNisPatchReplayData
    (ctx : ClassicalComparisonContext.{u, v})
  (overlapAgreementTarget descentSquareCompatibilityTarget : Sort _) where
  overlapGluingTarget : NisSquareOverlapGluingTarget
  bettiPatchReplayTarget : Prop
  deRhamPatchReplayTarget : Prop
  baseComparisonNaturalityTarget : Prop
  patchComparisonNaturalityTarget : Prop
  overlapComparisonNaturalityTarget : Prop
  overlapAgreement_holds : overlapAgreementTarget
  descentSquareCompatibility_holds : descentSquareCompatibilityTarget

structure GeometricNisnevichDescentTarget
    (ctx : ClassicalComparisonContext.{u, v})
    (realization : GeometricRealizationFunctorData ctx) where
  CoverIndex : Type w
  baseIndex : CoverIndex → realization.ObjectIndex
  patchIndex : CoverIndex → realization.ObjectIndex
  overlapIndex : CoverIndex → realization.ObjectIndex
  coverCompatibilityTarget :
    ∀ cover : CoverIndex,
      let baseObject := realization.geometricObject (baseIndex cover)
      let patchObject := realization.geometricObject (patchIndex cover)
      let overlapObject := realization.geometricObject (overlapIndex cover)
      baseObject.realizationDefinedTarget ∧
        patchObject.realizationDefinedTarget ∧
        overlapObject.realizationDefinedTarget
  comparisonDescentTarget :
    ∀ cover : CoverIndex,
      let baseComparison := realization.comparisonData (baseIndex cover)
      let patchComparison := realization.comparisonData (patchIndex cover)
      let overlapComparison := realization.comparisonData (overlapIndex cover)
      baseComparison.grothendieckComparisonTarget ∧
        patchComparison.grothendieckComparisonTarget ∧
        overlapComparison.grothendieckComparisonTarget
  gluingTheoremTarget : Prop
  traceNativePatchReplayData :
    CertifiedNisPatchReplayData ctx
      (∀ cover : CoverIndex,
        let baseComparison := realization.comparisonData (baseIndex cover)
        let patchComparison := realization.comparisonData (patchIndex cover)
        let overlapComparison := realization.comparisonData (overlapIndex cover)
        baseComparison.grothendieckComparisonTarget ∧
          patchComparison.grothendieckComparisonTarget ∧
          overlapComparison.grothendieckComparisonTarget)
      gluingTheoremTarget

namespace GeometricNisnevichDescentTarget

theorem nisOverlapAgreement_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (target : GeometricNisnevichDescentTarget ctx realization) :
    ∀ cover : target.CoverIndex,
      let baseComparison := realization.comparisonData (target.baseIndex cover)
      let patchComparison := realization.comparisonData (target.patchIndex cover)
      let overlapComparison := realization.comparisonData (target.overlapIndex cover)
      baseComparison.grothendieckComparisonTarget ∧
        patchComparison.grothendieckComparisonTarget ∧
        overlapComparison.grothendieckComparisonTarget :=
  target.traceNativePatchReplayData.overlapAgreement_holds

theorem nisDescentSquareCompatibility_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (target : GeometricNisnevichDescentTarget ctx realization) :
    target.gluingTheoremTarget :=
  target.traceNativePatchReplayData.descentSquareCompatibility_holds

theorem nisDescentSquareCompatibilityShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (target : GeometricNisnevichDescentTarget ctx realization) :
    target.gluingTheoremTarget :=
  target.nisDescentSquareCompatibility_from_certifiedReplay

end GeometricNisnevichDescentTarget

/-- Typed distinguished-square morphism data attached to a Nis row after geometric objects have
been realized as Wall 10A smooth schemes.

The map-level Nis descent construction only needs the overlap-to-patch and overlap-to-base legs to
form the Mayer-Vietoris map, but we also record the patch-to-base leg and graph witnesses for all
three morphisms so the square is carried as actual geometric data rather than as a bare Prop. -/
structure GeometricNisnevichDistinguishedSquareData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (smoothRealization : GeometricSmoothRealizationFunctorData realization)
    (CoverIndex : Type w)
    (baseIndex patchIndex overlapIndex : CoverIndex → realization.ObjectIndex) where
  patchToBase :
    (cover : CoverIndex) →
      Wall10A.SchemeOverQ.Hom
        (smoothRealization.scheme (patchIndex cover))
        (smoothRealization.scheme (baseIndex cover))
  overlapToPatch :
    (cover : CoverIndex) →
      Wall10A.SchemeOverQ.Hom
        (smoothRealization.scheme (overlapIndex cover))
        (smoothRealization.scheme (patchIndex cover))
  overlapToBase :
    (cover : CoverIndex) →
      Wall10A.SchemeOverQ.Hom
        (smoothRealization.scheme (overlapIndex cover))
        (smoothRealization.scheme (baseIndex cover))
  patchToBaseGraph :
    ∀ cover : CoverIndex,
      Wall10A.SchemeOverQ.GraphFiniteCorrespondenceData (patchToBase cover)
  overlapToPatchGraph :
    ∀ cover : CoverIndex,
      Wall10A.SchemeOverQ.GraphFiniteCorrespondenceData (overlapToPatch cover)
  overlapToBaseGraph :
    ∀ cover : CoverIndex,
      Wall10A.SchemeOverQ.GraphFiniteCorrespondenceData (overlapToBase cover)
  commutativeSquareTarget : Prop

/-- Exact trace-native blocker for future `Loc` triangle compatibility.

The current Layer B real-object library exposes sink peeling, replay, and boundary administration,
but it does not yet expose a localization-shaped certified packet proving that peeling the ambient
packet produces the open complement together with a boundary defect identified with the shifted
closed packet. This structure names that missing layer directly. -/
structure LocSinkPeelExposesClosedDefectTarget where
  ReplayWitness : Type w
  replayWitness : ReplayWitness
  ambientPacketTarget : Prop
  openComplementPacketTarget : Prop
  closedSupportPacketTarget : Prop
  canonicalSinkTarget : Prop
  peelResultTarget : Prop
  exposedBoundaryDefectTarget : Prop
  defectMatchesShiftedClosedTarget : Prop
  replayReconstructsAmbientTarget : Prop

/-- Trace-native replay package intended to replace the provisional cone shadow.

This records the exact lower-level replay data that a future `Loc` proof should consume before any
categorical cone/functoriality statement is exported as a shadow. -/
structure CertifiedLocPacketReplayData
    (ctx : ClassicalComparisonContext.{u, v})
  (connectingPacketComparisonNaturalityTarget : Sort _) where
  sinkPeelReplayTarget : LocSinkPeelExposesClosedDefectTarget
  bettiReplayTarget : Prop
  deRhamReplayTarget : Prop
  ambientComparisonNaturalityTarget : Prop
  openComparisonNaturalityTarget : Prop
  closedComparisonNaturalityTarget : Prop
  connectingPacketComparisonNaturality_holds : connectingPacketComparisonNaturalityTarget

/-- Concrete arrow data for the local cone calculus used by localization triangles. -/
structure LocalizationArrowData where
  Closed : Type u
  Ambient : Type v
  closedToAmbient : Closed → Ambient

namespace LocalizationArrowData

/-- The concrete cone object used locally for localization triangles. -/
abbrev coneObject (arrow : LocalizationArrowData) :=
  Sum arrow.Ambient arrow.Closed

/-- The local shift used by the concrete cone calculus. -/
abbrev shiftClosed (arrow : LocalizationArrowData) :=
  Option arrow.Closed

/-- The ambient-to-cone map for the concrete cone model. -/
def ambientToCone (arrow : LocalizationArrowData) :
    arrow.Ambient → Sum arrow.Ambient arrow.Closed :=
  Sum.inl

/-- The connecting morphism for the concrete cone model. -/
def connectingMorphism (arrow : LocalizationArrowData) :
    Sum arrow.Ambient arrow.Closed → Option arrow.Closed
  | Sum.inl _ => none
  | Sum.inr closedPoint => some closedPoint

end LocalizationArrowData

/-- A concrete morphism of closed-to-ambient arrows. -/
structure LocalizationArrowMorphism
    (source target : LocalizationArrowData) where
  left : source.Closed → target.Closed
  right : source.Ambient → target.Ambient
  squareCommutes : target.closedToAmbient ∘ left = right ∘ source.closedToAmbient

namespace LocalizationArrowMorphism

/-- Shift the closed-side map along the local concrete shift. -/
def shiftMap
    {source target : LocalizationArrowData}
    (morphism : LocalizationArrowMorphism source target) :
    source.shiftClosed → target.shiftClosed :=
  Option.map morphism.left

/-- The induced map on local cone objects. -/
def inducedConeMap
    {source target : LocalizationArrowData}
    (morphism : LocalizationArrowMorphism source target) :
  Sum source.Ambient source.Closed → Sum target.Ambient target.Closed :=
  Sum.map morphism.right morphism.left

end LocalizationArrowMorphism

/-- Concrete data encoding the ladder

`morphism of arrows -> morphism of cones -> morphism of localization triangles`.

This is the current provisional shadow replacement for the previous assumed cone-functoriality
field. The long-term source of this theorem should be `CertifiedLocPacketReplayData`, not a generic
cone API. -/
structure ConeTriangleFunctorialityData where
  sourceArrow : LocalizationArrowData
  targetArrow : LocalizationArrowData
  arrowMorphism : LocalizationArrowMorphism sourceArrow targetArrow

namespace ConeTriangleFunctorialityData

def inducedConeMap (data : ConeTriangleFunctorialityData) :
    Sum data.sourceArrow.Ambient data.sourceArrow.Closed →
      Sum data.targetArrow.Ambient data.targetArrow.Closed :=
  fun point => data.arrowMorphism.inducedConeMap point

def connectingSquareTarget (data : ConeTriangleFunctorialityData) : Prop :=
  ∀ point : Sum data.sourceArrow.Ambient data.sourceArrow.Closed,
    Option.map data.arrowMorphism.left
        (match point with
        | Sum.inl _ => none
        | Sum.inr closedPoint => some closedPoint) =
      match data.inducedConeMap point with
      | Sum.inl _ => none
      | Sum.inr closedPoint => some closedPoint

theorem coneFunctorialityForLocalizationTriangles
    (data : ConeTriangleFunctorialityData) :
    data.connectingSquareTarget := by
  intro sourcePoint
  cases sourcePoint <;>
    rfl

end ConeTriangleFunctorialityData

/-- Minimal lower-level data currently used to discharge the localization-triangle comparison claim.

The first two squares are the comparison/naturality compatibilities for the closed-to-ambient and
ambient-to-open maps. The connecting-morphism square is currently proved from the concrete cone
shadow below, but the trace-native blocker is recorded separately in `traceNativeReplayData` so the
next pass can replace the shadow with sink-peel / replay data. -/
structure LocalizationConeNaturalityData
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (LocalizationIndex : Type w)
    (ambientIndex openIndex closedIndex : LocalizationIndex → realization.ObjectIndex) where
  leftSquareCommutes : Prop
  middleSquareCommutes : Prop
  coneInducedMapEqOpenComparison : Prop
  coneTriangleFunctorialityData : ConeTriangleFunctorialityData
  traceNativeReplayData :
    CertifiedLocPacketReplayData ctx coneTriangleFunctorialityData.connectingSquareTarget
  leftSquareCommutes_holds : leftSquareCommutes
  middleSquareCommutes_holds : middleSquareCommutes
  coneInducedMapEqOpenComparison_holds : coneInducedMapEqOpenComparison

namespace LocalizationConeNaturalityData

def connectingMorphismCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    {LocalizationIndex : Type w}
    {ambientIndex openIndex closedIndex : LocalizationIndex → realization.ObjectIndex}
    (data : LocalizationConeNaturalityData realization LocalizationIndex ambientIndex openIndex closedIndex) :
    Prop :=
  data.coneTriangleFunctorialityData.connectingSquareTarget

def triangleCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    {LocalizationIndex : Type w}
    {ambientIndex openIndex closedIndex : LocalizationIndex → realization.ObjectIndex}
    (data : LocalizationConeNaturalityData realization LocalizationIndex ambientIndex openIndex closedIndex) :
    Prop :=
  data.leftSquareCommutes ∧
    data.middleSquareCommutes ∧
      data.connectingMorphismCompatibilityTarget

theorem locConnectingPacket_comparison_naturality_from_replay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    {LocalizationIndex : Type w}
    {ambientIndex openIndex closedIndex : LocalizationIndex → realization.ObjectIndex}
    (data : LocalizationConeNaturalityData realization LocalizationIndex ambientIndex openIndex closedIndex) :
    data.connectingMorphismCompatibilityTarget :=
  data.traceNativeReplayData.connectingPacketComparisonNaturality_holds

theorem coneFunctorialityForLocalizationTriangles_of_certifiedLocReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    {LocalizationIndex : Type w}
    {ambientIndex openIndex closedIndex : LocalizationIndex → realization.ObjectIndex}
    (data : LocalizationConeNaturalityData realization LocalizationIndex ambientIndex openIndex closedIndex) :
    data.connectingMorphismCompatibilityTarget :=
  data.locConnectingPacket_comparison_naturality_from_replay

theorem connectingMorphismCompatibilityFromConeFunctoriality
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    {LocalizationIndex : Type w}
    {ambientIndex openIndex closedIndex : LocalizationIndex → realization.ObjectIndex}
    (data : LocalizationConeNaturalityData realization LocalizationIndex ambientIndex openIndex closedIndex) :
    data.connectingMorphismCompatibilityTarget :=
  data.coneFunctorialityForLocalizationTriangles_of_certifiedLocReplay

theorem locTriangleCompatibility_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    {LocalizationIndex : Type w}
    {ambientIndex openIndex closedIndex : LocalizationIndex → realization.ObjectIndex}
    (data : LocalizationConeNaturalityData realization LocalizationIndex ambientIndex openIndex closedIndex) :
    data.triangleCompatibilityTarget := by
  exact ⟨data.leftSquareCommutes_holds, data.middleSquareCommutes_holds,
    data.locConnectingPacket_comparison_naturality_from_replay⟩

theorem locTriangleCompatibilityFromConeFunctoriality
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    {LocalizationIndex : Type w}
    {ambientIndex openIndex closedIndex : LocalizationIndex → realization.ObjectIndex}
    (data : LocalizationConeNaturalityData realization LocalizationIndex ambientIndex openIndex closedIndex) :
    data.triangleCompatibilityTarget := by
  exact data.locTriangleCompatibility_from_certifiedReplay

end LocalizationConeNaturalityData

/-- Theorem-target interface for open/closed localization triangles on the geometric source side.
-/
structure GeometricOpenClosedLocalizationTarget
    (ctx : ClassicalComparisonContext.{u, v})
    (realization : GeometricRealizationFunctorData ctx) where
  LocalizationIndex : Type w
  ambientIndex : LocalizationIndex → realization.ObjectIndex
  openIndex : LocalizationIndex → realization.ObjectIndex
  closedIndex : LocalizationIndex → realization.ObjectIndex
  openImmersionTarget :
    ∀ loc : LocalizationIndex,
      let ambientObject := realization.geometricObject (ambientIndex loc)
      let openObject := realization.geometricObject (openIndex loc)
      ambientObject.geometricAdmissibilityTarget ∧ openObject.geometricAdmissibilityTarget
  closedImmersionTarget :
    ∀ loc : LocalizationIndex,
      let ambientObject := realization.geometricObject (ambientIndex loc)
      let closedObject := realization.geometricObject (closedIndex loc)
      ambientObject.geometricAdmissibilityTarget ∧ closedObject.geometricAdmissibilityTarget
  comparisonLocalizationTarget :
    ∀ loc : LocalizationIndex,
      let ambientComparison := realization.comparisonData (ambientIndex loc)
      let openComparison := realization.comparisonData (openIndex loc)
      let closedComparison := realization.comparisonData (closedIndex loc)
      ambientComparison.periodCompatibilityTarget ∧
        openComparison.periodCompatibilityTarget ∧
        closedComparison.periodCompatibilityTarget
  coneNaturalityData :
    LocalizationConeNaturalityData realization LocalizationIndex ambientIndex openIndex closedIndex

namespace GeometricOpenClosedLocalizationTarget

def localizationTriangleTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (target : GeometricOpenClosedLocalizationTarget ctx realization) : Prop :=
  target.coneNaturalityData.triangleCompatibilityTarget

theorem connectingMorphismCompatibilityFromConeFunctoriality
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (target : GeometricOpenClosedLocalizationTarget ctx realization) :
    target.coneNaturalityData.connectingMorphismCompatibilityTarget :=
  target.coneNaturalityData.connectingMorphismCompatibilityFromConeFunctoriality

theorem locConnectingPacket_comparison_naturality_from_replay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (target : GeometricOpenClosedLocalizationTarget ctx realization) :
    target.coneNaturalityData.connectingMorphismCompatibilityTarget :=
  target.coneNaturalityData.locConnectingPacket_comparison_naturality_from_replay

theorem locTriangleCompatibility_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (target : GeometricOpenClosedLocalizationTarget ctx realization) :
    target.localizationTriangleTarget :=
  target.coneNaturalityData.locTriangleCompatibility_from_certifiedReplay

theorem locTriangleCompatibilityFromConeFunctoriality
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (target : GeometricOpenClosedLocalizationTarget ctx realization) :
    target.localizationTriangleTarget :=
  target.locTriangleCompatibility_from_certifiedReplay

end GeometricOpenClosedLocalizationTarget

/-- Theorem-target interface for functoriality of geometric correspondences on realization data. -/
structure GeometricCorrespondenceFunctorialityTarget
    (ctx : ClassicalComparisonContext.{u, v})
    (realization : GeometricRealizationFunctorData ctx) where
  theoremTarget :
    ∀ corr : realization.CorrespondenceIndex,
      let sourceObject := realization.geometricObject (realization.sourceIndex corr)
      let targetObject := realization.geometricObject (realization.targetIndex corr)
      let sourceComparison := realization.comparisonData (realization.sourceIndex corr)
      let targetComparison := realization.comparisonData (realization.targetIndex corr)
      (realization.correspondence corr).correspondenceTarget ∧
        sourceObject.realizationDefinedTarget ∧
        targetObject.realizationDefinedTarget ∧
        sourceComparison.grothendieckComparisonTarget ∧
        targetComparison.grothendieckComparisonTarget
  compositionFunctorialityTarget : Prop
  identityFunctorialityTarget : Prop

/-- Trace-native envelope operations under which already-certified packets can be replayed. -/
inductive EnvReplayOperation where
  | whisker
  | compose
  | tensor
  | shift
  | structuralAdmin

/-- Certified replay transformer for formal envelope closure. -/
structure EnvReplayTransformerTarget where
  ReplayWitness : Type w
  replayWitness : ReplayWitness
  operation : EnvReplayOperation
  certifiedInputPacketTarget : Prop
  transformedPacketTarget : Prop
  boundaryTransportTarget : Prop
  dependencyTransportTarget : Prop
  replayTransformerTarget : Prop
  normalizationTarget : Prop

namespace EnvReplayTransformerTarget

def envWhisker_from_certifiedReplay
    (transformer : EnvReplayTransformerTarget) : EnvReplayTransformerTarget :=
  { transformer with operation := .whisker }

def envCompose_from_certifiedReplay
    (transformer : EnvReplayTransformerTarget) : EnvReplayTransformerTarget :=
  { transformer with operation := .compose }

def envTensor_from_certifiedReplay
    (transformer : EnvReplayTransformerTarget) : EnvReplayTransformerTarget :=
  { transformer with operation := .tensor }

def envShift_from_certifiedReplay
    (transformer : EnvReplayTransformerTarget) : EnvReplayTransformerTarget :=
  { transformer with operation := .shift }

def envStructuralAdmin_from_certifiedReplay
    (transformer : EnvReplayTransformerTarget) : EnvReplayTransformerTarget :=
  { transformer with operation := .structuralAdmin }

end EnvReplayTransformerTarget

/-- Trace-native replay package intended to be the primitive source of Env closure soundness. -/
structure CertifiedEnvReplayData
    (ctx : ClassicalComparisonContext.{u, v})
  (comparisonAgreementTarget formalClosureTarget : Sort _) where
  replayTransformerTarget : EnvReplayTransformerTarget
  ambientBettiReplayTarget : Prop
  envelopeBettiReplayTarget : Prop
  ambientDeRhamReplayTarget : Prop
  envelopeDeRhamReplayTarget : Prop
  boundaryComparisonNaturalityTarget : Prop
  dependencyComparisonNaturalityTarget : Prop
  comparisonAgreement_holds : comparisonAgreementTarget
  formalClosure_holds : formalClosureTarget

/-- Theorem-target interface for envelope exactness on geometric realizations. -/
structure GeometricEnvelopeExactnessTarget
    (ctx : ClassicalComparisonContext.{u, v})
    (realization : GeometricRealizationFunctorData ctx) where
  EnvelopeIndex : Type w
  ambientIndex : EnvelopeIndex → realization.ObjectIndex
  envelopeIndex : EnvelopeIndex → realization.ObjectIndex
  envelopeCorrespondence :
    (env : EnvelopeIndex) →
      GeometricCorrespondence
        (realization.geometricObject (envelopeIndex env))
        (realization.geometricObject (ambientIndex env))
  exactnessInputTarget :
    ∀ env : EnvelopeIndex,
      let ambientComparison := realization.comparisonData (ambientIndex env)
      let envelopeComparison := realization.comparisonData (envelopeIndex env)
      (envelopeCorrespondence env).correspondenceTarget ∧
        ambientComparison.grothendieckComparisonTarget ∧
        envelopeComparison.grothendieckComparisonTarget
  comparisonExactnessTarget :
    ∀ env : EnvelopeIndex,
      let ambientComparison := realization.comparisonData (ambientIndex env)
      let envelopeComparison := realization.comparisonData (envelopeIndex env)
      ambientComparison.periodCompatibilityTarget ∧
        envelopeComparison.periodCompatibilityTarget
  formalClosureTarget : Prop
  traceNativeEnvReplayData :
    CertifiedEnvReplayData ctx
      (∀ env : EnvelopeIndex,
        let ambientComparison := realization.comparisonData (ambientIndex env)
        let envelopeComparison := realization.comparisonData (envelopeIndex env)
        (envelopeCorrespondence env).correspondenceTarget ∧
          ambientComparison.grothendieckComparisonTarget ∧
          envelopeComparison.grothendieckComparisonTarget ∧
          ambientComparison.periodCompatibilityTarget ∧
          envelopeComparison.periodCompatibilityTarget)
      formalClosureTarget

namespace GeometricEnvelopeExactnessTarget

theorem envComparisonAgreement_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (target : GeometricEnvelopeExactnessTarget ctx realization) :
    ∀ env : target.EnvelopeIndex,
      let ambientComparison := realization.comparisonData (target.ambientIndex env)
      let envelopeComparison := realization.comparisonData (target.envelopeIndex env)
      (target.envelopeCorrespondence env).correspondenceTarget ∧
        ambientComparison.grothendieckComparisonTarget ∧
        envelopeComparison.grothendieckComparisonTarget ∧
        ambientComparison.periodCompatibilityTarget ∧
        envelopeComparison.periodCompatibilityTarget :=
  target.traceNativeEnvReplayData.comparisonAgreement_holds

def envReplayTransformer_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (target : GeometricEnvelopeExactnessTarget ctx realization) :
    EnvReplayTransformerTarget :=
  target.traceNativeEnvReplayData.replayTransformerTarget

def envWhisker_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (target : GeometricEnvelopeExactnessTarget ctx realization) :
    EnvReplayTransformerTarget :=
  EnvReplayTransformerTarget.envWhisker_from_certifiedReplay
    target.traceNativeEnvReplayData.replayTransformerTarget

def envCompose_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (target : GeometricEnvelopeExactnessTarget ctx realization) :
    EnvReplayTransformerTarget :=
  EnvReplayTransformerTarget.envCompose_from_certifiedReplay
    target.traceNativeEnvReplayData.replayTransformerTarget

def envTensor_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (target : GeometricEnvelopeExactnessTarget ctx realization) :
    EnvReplayTransformerTarget :=
  EnvReplayTransformerTarget.envTensor_from_certifiedReplay
    target.traceNativeEnvReplayData.replayTransformerTarget

def envShift_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (target : GeometricEnvelopeExactnessTarget ctx realization) :
    EnvReplayTransformerTarget :=
  EnvReplayTransformerTarget.envShift_from_certifiedReplay
    target.traceNativeEnvReplayData.replayTransformerTarget

def envStructuralAdmin_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (target : GeometricEnvelopeExactnessTarget ctx realization) :
    EnvReplayTransformerTarget :=
  EnvReplayTransformerTarget.envStructuralAdmin_from_certifiedReplay
    target.traceNativeEnvReplayData.replayTransformerTarget

theorem envFormalClosureSoundness_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (target : GeometricEnvelopeExactnessTarget ctx realization) :
    target.formalClosureTarget :=
  target.traceNativeEnvReplayData.formalClosure_holds

theorem envFormalClosureSoundnessShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (target : GeometricEnvelopeExactnessTarget ctx realization) :
    target.formalClosureTarget :=
  target.envFormalClosureSoundness_from_certifiedReplay

end GeometricEnvelopeExactnessTarget

/-- Package collecting the first localization/descent theorem targets for geometric objects.

This is the theorem-target layer that later geometric and motivic recognition code will consume,
but it does not yet prove any of the listed properties. -/
structure GeometricLocalizationPackage
    (ctx : ClassicalComparisonContext.{u, v}) where
  realization : GeometricRealizationFunctorData ctx
  a1Invariance : GeometricA1InvarianceTarget ctx realization
  nisnevichDescent : GeometricNisnevichDescentTarget ctx realization
  openClosedLocalization : GeometricOpenClosedLocalizationTarget ctx realization
  correspondenceFunctoriality : GeometricCorrespondenceFunctorialityTarget ctx realization
  envelopeExactness : GeometricEnvelopeExactnessTarget ctx realization
  realizationCompatibilityTarget : Prop
  motivicRecognitionInterfaceTarget : Prop

/-- Readiness target asserting that the geometric localization package and the geometric
realization/tomography layer are aligned strongly enough to feed later motivic recognition. -/
structure ClassicalMotivicRealizationReadiness
    (ctx : ClassicalComparisonContext.{u, v})
    (structuredEq : StructuredComparisonEquality ctx) where
  localizationPackage : GeometricLocalizationPackage ctx
  tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq
  sharedRealizationTarget :
    localizationPackage.realization = tomographySoundness.geometricRealizationFunctor
  localizationFeedsTomographyTarget : Prop
  localizationFeedsMotivicRecognitionTarget : Prop

namespace GeometricLocalizationPackage

/-- Bridge target from geometric localization/descent plus geometric realization tomography to the
future motivic-recognition readiness package. -/
def toClassicalMotivicRealizationReadiness
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (localization : GeometricLocalizationPackage ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : localization.realization = tomography.geometricRealizationFunctor) :
    ClassicalMotivicRealizationReadiness ctx structuredEq where
  localizationPackage := localization
  tomographySoundness := tomography
  sharedRealizationTarget := hrealization
  localizationFeedsTomographyTarget :=
    localization.realizationCompatibilityTarget ∧
      localization.motivicRecognitionInterfaceTarget
  localizationFeedsMotivicRecognitionTarget :=
    localization.realizationCompatibilityTarget ∧
      localization.motivicRecognitionInterfaceTarget

/-! ### Projection lemmas for the readiness bridge. -/

@[simp] theorem toClassicalMotivicRealizationReadiness_localizationPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (localization : GeometricLocalizationPackage ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : localization.realization = tomography.geometricRealizationFunctor) :
    (localization.toClassicalMotivicRealizationReadiness tomography hrealization).localizationPackage =
      localization := rfl

@[simp] theorem toClassicalMotivicRealizationReadiness_tomographySoundness
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (localization : GeometricLocalizationPackage ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : localization.realization = tomography.geometricRealizationFunctor) :
    (localization.toClassicalMotivicRealizationReadiness tomography hrealization).tomographySoundness =
      tomography := rfl

@[simp] theorem toClassicalMotivicRealizationReadiness_sharedRealizationTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (localization : GeometricLocalizationPackage ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : localization.realization = tomography.geometricRealizationFunctor) :
    (localization.toClassicalMotivicRealizationReadiness tomography hrealization).sharedRealizationTarget =
      hrealization := rfl

end GeometricLocalizationPackage

end ClassicalPeriods
end TraceCalc