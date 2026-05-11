import TraceCalc.LayerD.ConcretePeriodFaithfulness
import TraceCalc.ClassicalPeriods.PeriodConjectureTarget
import TraceCalc.ClassicalBridge.PeriodTargetBridge
import TraceCalc.ClassicalBridge.RecognizedMMQPeriodBridgeTheorems
import TraceCalc.MotivicRecognition.ManuscriptSpineTargets

universe u v w x y z

namespace TraceCalc
namespace PeriodConjectureProblemSeal

open ClassicalPeriods
open MotivicRecognition
open LayerB.RealObjects

/-!
# Period Conjecture Problem Seal

This module is an audit-only seal exposing the exact theorem surfaces used for
classical period-faithfulness conclusions.

It adds no assumptions, no new axioms, and no wrapper relations. Its role is to
make theorem types visibly checkable for mathematical audit.

## Theorem shape invariants

- Left side hypotheses are scalar/basis-free period equalities (`f.basisFreePeriodMap = g.basisFreePeriodMap`).
- Right side conclusion is literal morphism equality (`f = g`) when using the combined theorem.
- No `EqMorph` wrapper is used in the concrete theorem aliases here.
- No `PeriodFaithfulnessContext` hypothesis is used in these aliases.
- No `PLift True` or `EqMorph := True` context is involved in this seal.

## Grep audit instructions (run from repository root)

Check for vacuous wrappers and forbidden patterns:
```
rg -n "EqMorph.*True|PLift True|ScalarShadow.*True|StructuredRealization.*True|sorry|admit|axiom|by trivial" \
  Lean/TraceCalc --glob '!**/LayerG/Mock*'
```

Check for spurious period-quotient equality:
```
rg -n "Setoid|Quotient|Equiv|Eq" Lean/TraceCalc | rg "period|Period|basisFree"
```

Check that ScalarShadow does not carry witnesses, traces, or reconstruction certificates:
```
rg -n "ScalarShadow|scalar.*witness|scalar.*certificate|scalar.*trace|scalar.*reconstruction|scalar.*comparisonIso" \
  Lean/TraceCalc
```
-/

/-! ## Theorem aliases

These are direct theorem-shape aliases for the concrete period-faithfulness results,
restated without any extra wrapper relation or audit-only structure layer. -/

/-- Alias to the concrete over-scalar reflection theorem.
This restates the exact theorem surface of
`LayerD.scalar_period_faithfulness_classical`. -/
theorem scalar_period_faithfulness_classical_sealed :
    {ctx : ClassicalComparisonContext} →
    (source target : ClassicalStructuredComparisonObject ctx) →
    (f g : ClassicalStructuredComparisonMorphism source target) →
    f.basisFreePeriodMap = g.basisFreePeriodMap →
      f.deRhamMapOverScalar = g.deRhamMapOverScalar ∧
      f.bettiMapOverScalar = g.bettiMapOverScalar :=
  fun source target f g h =>
    LayerD.scalar_period_faithfulness_classical source target f g h

/-- Alias to the concrete literal-equality theorem.
This restates the exact theorem surface of
`LayerD.full_morphism_eq_of_basisFreePeriodMap_eq`. -/
theorem full_morphism_eq_of_basisFreePeriodMap_eq_sealed :
    {ctx : ClassicalComparisonContext} →
    {source target : ClassicalStructuredComparisonObject ctx} →
    (f g : ClassicalStructuredComparisonMorphism source target) →
    f.bettiMap = g.bettiMap →
    f.deRhamMap = g.deRhamMap →
    f.basisFreePeriodMap = g.basisFreePeriodMap →
    f = g :=
  fun f g hBetti hDeRham hBasis =>
    LayerD.full_morphism_eq_of_basisFreePeriodMap_eq f g hBetti hDeRham hBasis

/-- Final period-conjecture theorem endpoint currently exposed in production.
This takes a `BaseFaithfulnessTarget` package and returns its `faithfulnessStatement`. -/
theorem baseFaithfulness_of_reflection_sealed
    (target : PeriodConjectureTargetIndex.BaseFaithfulnessTarget.{u, v, w}) :
    target.faithfulnessStatement :=
  PeriodConjectureTargetIndex.baseFaithfulness_of_reflection target

/-- Final framed period-conjecture theorem endpoint currently exposed in production.
This takes a `FramedFaithfulnessTarget` package and returns its `faithfulnessStatement`. -/
theorem framedFaithfulness_of_reflection_sealed
    (target : PeriodConjectureTargetIndex.FramedFaithfulnessTarget.{u, v, w}) :
    target.faithfulnessStatement :=
  PeriodConjectureTargetIndex.framedFaithfulness_of_reflection target

/-! ## Recognized `MM(Q)` bridge seals

These aliases make the accepted recognized-`MM(Q)` bridge part of the audited theorem spine.
They do not strengthen the mathematics; they force the bridge file's object-level scalar-extension,
injectivity, and reconstruction route onto a downstream seal surface that is exercised by the main
`TraceCalc` build. -/

section RecognizedMMQBridgeSeal

variable
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
  {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
  {P : LayerB.RealObjects.RewriteCalculusSetup.SyntacticBoundaryPresentation setup}
    {α : Type v}
  {comparison : LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α}
  {C : LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {normalization : NormalizationPackageTarget internal}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    {comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical}
    {canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence}
    {normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence}
    {transportedNormalization :
      TransportedNormalizationIsMotivicTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence normalizationTransport}
    {normTStructure : NormTStructureTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization}
    {heartRecognition : HeartRecognitionTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization normTStructure}

/-- Audit seal for the recognized-image faithful scalar-extension package exported by the accepted
recognized `MM(Q)` bridge. -/
def recognizedMMQ_faithfulScalarExtension_sealed
    (target : ClassicalBridge.RecognizedMMQPeriodTargetSkeleton
      spine internal normalization classical comparisonEquivalence canonicalEquivalence
      normalizationTransport transportedNormalization normTStructure heartRecognition) :
    ClassicalBridge.RecognizedMMQFaithfulScalarExtensionOnImage target :=
  ClassicalBridge.recognizedMMQFaithfulScalarExtensionOnImage_of_objectComparisonTensorData
    (ctx := ctx)
    target

/-- Audit seal for the recognized-image scalar-extension injectivity witness exported by the
accepted recognized `MM(Q)` bridge. -/
def recognizedMMQ_scalarExtensionInjectivity_sealed
    (target : ClassicalBridge.RecognizedMMQPeriodTargetSkeleton
      spine internal normalization classical comparisonEquivalence canonicalEquivalence
      normalizationTransport transportedNormalization normTStructure heartRecognition) :
    ClassicalBridge.RecognizedMMQScalarExtensionInjectivityWitnessOnImage target :=
  ClassicalBridge.recognizedMMQScalarExtensionInjectivityWitnessOnImage_of_objectComparisonTensorData
    (ctx := ctx)
    target

/-- Audit seal for the recognized-image reconstruction obligation discharged by the accepted
recognized `MM(Q)` bridge. -/
theorem recognizedMMQ_reconstructionObligation_sealed
    (target : ClassicalBridge.RecognizedMMQPeriodTargetSkeleton
      spine internal normalization classical comparisonEquivalence canonicalEquivalence
      normalizationTransport transportedNormalization normTStructure heartRecognition) :
    ClassicalBridge.RecognizedMMQPeriodTargetSkeleton.RecognizedMMQReconstructionObligation
      (ctx := ctx) target :=
  ClassicalBridge.recognizedMMQReconstructionObligation_of_objectComparisonTensorData
    (ctx := ctx)
    target

end RecognizedMMQBridgeSeal

section RecognizedMMQLiteralPackedEqualitySeal

variable
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : LayerB.RealObjects.RewriteCalculusSetup.SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α}
    {C : LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {normalization : NormalizationPackageTarget internal}
    {ctx : ClassicalComparisonContext.{u, v}}
    {classical :
      ClassicalManuscriptSpineTarget ctx (LayerD.literalPackedStructuredComparisonEquality ctx)}
    {comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical}
    {canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence}
    {normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence}
    {transportedNormalization :
      TransportedNormalizationIsMotivicTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence normalizationTransport}
    {normTStructure : NormTStructureTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization}
    {heartRecognition : HeartRecognitionTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization normTStructure}

abbrev RecognizedCanonicalTarget
    (coordinates : ClassicalBridge.RecognizedMMQFramedPeriodSystem.ComparisonPeriodCoordinatePackage
      spine internal normalization classical comparisonEquivalence canonicalEquivalence
      normalizationTransport transportedNormalization normTStructure heartRecognition) :=
  ClassicalBridge.RecognizedMMQPeriodTargetSkeleton.ofFramedSystem
    coordinates.system

/-- Audit seal for the exact remaining conservativity theorem on the concrete classical comparison
layer already used by Layer D: literal packed comparison equality reflects packed comparison
equality on recognized `MM(Q)` morphisms. -/
def recognizedMMQ_literalPackedComparisonExtensionality_sealed
    (target : ClassicalBridge.RecognizedMMQPeriodTargetSkeleton
      spine internal normalization classical comparisonEquivalence canonicalEquivalence
      normalizationTransport transportedNormalization normTStructure heartRecognition) :
    ClassicalBridge.RecognizedMMQPackedComparisonExtensionalityOnRecognizedImage target :=
  ClassicalBridge.RecognizedMMQPackedComparisonExtensionalityOnRecognizedImage.ofLiteralPackedEquality
    (ctx := ctx)
    target
    rfl

/-- Owner-level scalar bridge theorem slot for the concrete literal-packed comparison layer.

This is the exact recognized-image theorem surface needed to derive the scalar public theorem
through the explicit literal-packed route. -/
def recognizedMMQ_scalarShadowExtensionality_sealed
    (coordinates : ClassicalBridge.RecognizedMMQFramedPeriodSystem.ComparisonPeriodCoordinatePackage
      spine internal normalization classical comparisonEquivalence canonicalEquivalence
      normalizationTransport transportedNormalization normTStructure heartRecognition) :
    ClassicalBridge.RecognizedMMQScalarShadowExtensionalityOnImage
      (RecognizedCanonicalTarget coordinates) := by
  exact
    { scalarShadow := coordinates.scalarCodec.scalarShadow
      scalarShadowEquality := coordinates.scalarCodec.scalarShadowEquality
      packedComparison_eq_of_scalarShadow_eq :=
        ClassicalBridge.RecognizedMMQFramedPeriodSystem.scalarSeparationTarget_of_scalarEncodingCompleteness
          coordinates.system coordinates.scalarCodec coordinates.framedSeparation }

/-- Owner-level framed bridge theorem slot for the concrete literal-packed comparison layer.

This is the exact recognized-image theorem surface needed to derive the framed public theorem
through the explicit literal-packed route. -/
theorem recognizedMMQ_framedShadowExtensionality_sealed
    (coordinates : ClassicalBridge.RecognizedMMQFramedPeriodSystem.ComparisonPeriodCoordinatePackage
      spine internal normalization classical comparisonEquivalence canonicalEquivalence
      normalizationTransport transportedNormalization normTStructure heartRecognition) :
    ClassicalBridge.RecognizedMMQFramedShadowExtensionalityOnImage
      (RecognizedCanonicalTarget coordinates) := by
  exact
    { packedComparison_eq_of_framedShadow_eq := coordinates.framedSeparation }

/-- Owner-level morphism-reconstruction theorem slot for the concrete literal-packed comparison
layer.

This is the exact recognized-image conservativity theorem surface needed to turn literal packed
comparison equality into equality of recognized `MM(Q)` morphisms. -/
theorem recognizedMMQ_morphismReconstructionFromPackedComparison_sealed
    (coordinates : ClassicalBridge.RecognizedMMQFramedPeriodSystem.ComparisonPeriodCoordinatePackage
      spine internal normalization classical comparisonEquivalence canonicalEquivalence
      normalizationTransport transportedNormalization normTStructure heartRecognition) :
    ClassicalBridge.RecognizedMMQLiteralPackedComparisonReflectsMorphismEqualityOnImage
      (RecognizedCanonicalTarget coordinates) := by
  exact
    { theoremTarget := coordinates.homFaithfulnessTarget }

end RecognizedMMQLiteralPackedEqualitySeal

section LiteralPackedBridgeConstructionSeal

variable
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
  {aux : LayerB.RealObjects.RewriteCalculusSetup.FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}

/-- Audit seal: the final scalar exported theorem can be routed through the explicitly
literal-packed target constructor instead of an opaque packaged `classicalTarget`. -/
theorem bridge_baseFaithfulness_of_literalPackedConstruction_sealed
    (bridge : ClassicalBridge.InternalProgramRealizesClassicalPeriodTarget presentation aux)
    (scalarShadowReflectsLiteralPackedComparison :
      ∀ {X Y : bridge.classicalTarget.MotiveCategory} (f g : X ⟶ Y),
        bridge.classicalTarget.scalarShadow.equalityRelation
          (bridge.classicalTarget.scalarShadowOf f)
          (bridge.classicalTarget.scalarShadowOf g) →
        bridge.classicalTarget.packedMorphismComparison f =
          bridge.classicalTarget.packedMorphismComparison g)
    (packedComparisonReflectsMorphismEquality :
      ∀ {X Y : bridge.classicalTarget.MotiveCategory} (f g : X ⟶ Y),
        bridge.classicalTarget.packedMorphismComparison f =
          bridge.classicalTarget.packedMorphismComparison g →
        f = g) :
    ClassicalGrothendieckPeriodFaithfulnessStatement
      (bridge.classicalTargetOfLiteralPackedComparison
        scalarShadowReflectsLiteralPackedComparison
        packedComparisonReflectsMorphismEquality) :=
  ClassicalBridge.InternalProgramRealizesClassicalPeriodTarget.classicalFaithfulnessStatement_ofLiteralPackedComparison
    bridge
    scalarShadowReflectsLiteralPackedComparison
    packedComparisonReflectsMorphismEquality

/-- Audit seal: the final framed exported theorem can be routed through the explicitly
literal-packed target constructor instead of an opaque packaged `classicalTarget`. -/
theorem bridge_framedFaithfulness_of_literalPackedConstruction_sealed
    (bridge : ClassicalBridge.InternalProgramRealizesClassicalPeriodTarget presentation aux)
    (scalarShadowReflectsLiteralPackedComparison :
      ∀ {X Y : bridge.classicalTarget.MotiveCategory} (f g : X ⟶ Y),
        bridge.classicalTarget.scalarShadow.equalityRelation
          (bridge.classicalTarget.scalarShadowOf f)
          (bridge.classicalTarget.scalarShadowOf g) →
        bridge.classicalTarget.packedMorphismComparison f =
          bridge.classicalTarget.packedMorphismComparison g)
    (packedComparisonReflectsMorphismEquality :
      ∀ {X Y : bridge.classicalTarget.MotiveCategory} (f g : X ⟶ Y),
        bridge.classicalTarget.packedMorphismComparison f =
          bridge.classicalTarget.packedMorphismComparison g →
        f = g)
    (framedShadowReflectsLiteralPackedComparison :
      ∀ {X Y : bridge.classicalTarget.MotiveCategory} (f g : X ⟶ Y),
        bridge.framedPeriodShadow.equalityRelation
          (bridge.framedPeriodShadow.shadowOf (bridge.framedPeriodOf f))
          (bridge.framedPeriodShadow.shadowOf (bridge.framedPeriodOf g)) →
        bridge.classicalTarget.packedMorphismComparison f =
          bridge.classicalTarget.packedMorphismComparison g) :
    ClassicalFramedPeriodConjectureStatement
      (bridge.framedTargetOfLiteralPackedComparison
        scalarShadowReflectsLiteralPackedComparison
        packedComparisonReflectsMorphismEquality
        framedShadowReflectsLiteralPackedComparison) :=
  ClassicalBridge.InternalProgramRealizesClassicalPeriodTarget.framedFaithfulnessStatement_ofLiteralPackedComparison
    bridge
    scalarShadowReflectsLiteralPackedComparison
    packedComparisonReflectsMorphismEquality
    framedShadowReflectsLiteralPackedComparison

end LiteralPackedBridgeConstructionSeal

/-! ## #check probes

These expose the precise Lean-elaborated type of each theorem for human inspection. -/

#check LayerD.scalar_period_faithfulness_classical
#check LayerD.full_morphism_eq_of_basisFreePeriodMap_eq
#check PeriodConjectureTargetIndex.baseFaithfulness_of_reflection
#check PeriodConjectureTargetIndex.framedFaithfulness_of_reflection
#check MotivicRecognition.ProofRelevantPeriodTheoremTarget
#check ClassicalBridge.recognizedMMQFaithfulScalarExtensionOnImage_of_objectComparisonTensorData
#check ClassicalBridge.recognizedMMQReconstructionObligation_of_objectComparisonTensorData
#check recognizedMMQ_faithfulScalarExtension_sealed
#check recognizedMMQ_reconstructionObligation_sealed
#check recognizedMMQ_literalPackedComparisonExtensionality_sealed
#check recognizedMMQ_scalarShadowExtensionality_sealed
#check recognizedMMQ_framedShadowExtensionality_sealed
#check recognizedMMQ_morphismReconstructionFromPackedComparison_sealed
#check bridge_baseFaithfulness_of_literalPackedConstruction_sealed
#check bridge_framedFaithfulness_of_literalPackedConstruction_sealed

/-! ## #print axioms

Confirms that the two concrete theorems depend only on `propext` and `Quot.sound`,
with no `sorry`, no `Classical.choice` escape, and no custom axioms. -/

#print axioms LayerD.scalar_period_faithfulness_classical
#print axioms LayerD.full_morphism_eq_of_basisFreePeriodMap_eq
#print axioms TraceCalc.PeriodConjectureProblemSeal.recognizedMMQ_framedShadowExtensionality_sealed
#print axioms TraceCalc.PeriodConjectureProblemSeal.recognizedMMQ_morphismReconstructionFromPackedComparison_sealed

end PeriodConjectureProblemSeal
end TraceCalc
