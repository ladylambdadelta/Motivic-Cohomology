import TraceCalc.PeriodConjectureProblemSeal

universe u v w x y z

namespace TraceCalc
namespace PeriodConjectureAssumptionBoundary

open ClassicalPeriods
open MotivicRecognition
open LayerB.RealObjects

/-!
# Period Conjecture Assumption Boundary

This module fixes the public conjecture surface on the canonical recognized
comparison package.

An assumption-free theorem cannot quantify over arbitrary comparison maps or
arbitrary shadows: constant shadows give immediate countermodels. The public
statements below therefore specialize to the recognized `MM(Q)` target and use
only the canonical shadow data exported by the sealed recognized bridge.
-/

section RecognizedStatements

variable
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {setup : RewriteCalculusSetup.{u}}
    {P : RewriteCalculusSetup.SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : RewriteCalculusSetup.CompletedReconstructionRecord setup → α}
    {C : RewriteCalculusSetup.CanNF setup}
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

/-- Canonical recognized scalar form of Grothendieck period faithfulness. -/
def ScalarGrothendieckPeriodConjectureStatement
  (coordinates : ClassicalBridge.RecognizedMMQFramedPeriodSystem.ComparisonPeriodCoordinatePackage
    spine internal normalization classical comparisonEquivalence canonicalEquivalence
    normalizationTransport transportedNormalization normTStructure heartRecognition) : Prop :=
  let target := PeriodConjectureProblemSeal.RecognizedCanonicalTarget coordinates
  let scalarExtensionality :=
    PeriodConjectureProblemSeal.recognizedMMQ_scalarShadowExtensionality_sealed
      (spine := spine) (internal := internal) (normalization := normalization)
      (classical := classical) (comparisonEquivalence := comparisonEquivalence)
      (canonicalEquivalence := canonicalEquivalence)
      (normalizationTransport := normalizationTransport)
      (transportedNormalization := transportedNormalization)
      (normTStructure := normTStructure) (heartRecognition := heartRecognition)
      coordinates
  ∀ {M N : target.MixedMotivesQ} (f g : target.MixedMotivesQHom M N),
    scalarExtensionality.scalarShadow.equalityRelation
      (scalarExtensionality.scalarShadow.shadowOf (target.packedMorphismComparisonOf f))
      (scalarExtensionality.scalarShadow.shadowOf (target.packedMorphismComparisonOf g)) →
    f = g

/-- Canonical recognized framed form of Grothendieck period faithfulness.

This is the exact full-family theorem surface exported by the recognized
bridge: agreement of all canonical framed shadows across the admissible frame
family forces equality of the underlying motivic morphisms.
-/
def FramedGrothendieckPeriodConjectureStatement
    (coordinates : ClassicalBridge.RecognizedMMQFramedPeriodSystem.ComparisonPeriodCoordinatePackage
      spine internal normalization classical comparisonEquivalence canonicalEquivalence
      normalizationTransport transportedNormalization normTStructure heartRecognition) : Prop :=
  let target := PeriodConjectureProblemSeal.RecognizedCanonicalTarget coordinates
  ∀ {M N : target.MixedMotivesQ}
    (f g : target.MixedMotivesQHom M N),
      (∀ probe : target.ProbeIndex,
          ClassicalBridge.RecognizedMMQPeriodTargetSkeleton.framedCoordinateFamilyOf
              target f probe =
            ClassicalBridge.RecognizedMMQPeriodTargetSkeleton.framedCoordinateFamilyOf
              target g probe) →
    f = g

/-- Canonical scalar conjecture theorem on the recognized image.

Its proof is purely compositional at the public boundary: scalar-shadow
separation yields packed-comparison equality, and recognized Hom-faithfulness
reconstructs the motivic morphism. -/
theorem scalar_grothendieck_period_conjecture_from_sealed_trace_calculus
    (coordinates : ClassicalBridge.RecognizedMMQFramedPeriodSystem.ComparisonPeriodCoordinatePackage
      spine internal normalization classical comparisonEquivalence canonicalEquivalence
      normalizationTransport transportedNormalization normTStructure heartRecognition) :
    ScalarGrothendieckPeriodConjectureStatement coordinates := by
  let target := PeriodConjectureProblemSeal.RecognizedCanonicalTarget coordinates
  intro M N f g hShadow
  let scalarExtensionality :=
    PeriodConjectureProblemSeal.recognizedMMQ_scalarShadowExtensionality_sealed
      (spine := spine) (internal := internal) (normalization := normalization)
      (classical := classical) (comparisonEquivalence := comparisonEquivalence)
      (canonicalEquivalence := canonicalEquivalence)
      (normalizationTransport := normalizationTransport)
      (transportedNormalization := transportedNormalization)
      (normTStructure := normTStructure) (heartRecognition := heartRecognition)
      coordinates
  have hPacked :=
    scalarExtensionality.packedComparison_eq_of_scalarShadow_eq f g hShadow
  exact
    (PeriodConjectureProblemSeal.recognizedMMQ_morphismReconstructionFromPackedComparison_sealed
      coordinates).theoremTarget f g hPacked

/-- Canonical framed conjecture theorem on the recognized image. -/
theorem framed_grothendieck_period_conjecture_from_sealed_trace_calculus
    (coordinates : ClassicalBridge.RecognizedMMQFramedPeriodSystem.ComparisonPeriodCoordinatePackage
      spine internal normalization classical comparisonEquivalence canonicalEquivalence
      normalizationTransport transportedNormalization normTStructure heartRecognition) :
    FramedGrothendieckPeriodConjectureStatement coordinates := by
  let target := PeriodConjectureProblemSeal.RecognizedCanonicalTarget coordinates
  intro M N f g hShadowFamily
  have hPacked :=
    (PeriodConjectureProblemSeal.recognizedMMQ_framedShadowExtensionality_sealed
      (spine := spine) (internal := internal) (normalization := normalization)
      (classical := classical) (comparisonEquivalence := comparisonEquivalence)
      (canonicalEquivalence := canonicalEquivalence)
      (normalizationTransport := normalizationTransport)
      (transportedNormalization := transportedNormalization)
      (normTStructure := normTStructure) (heartRecognition := heartRecognition)
      coordinates).packedComparison_eq_of_framedShadow_eq f g hShadowFamily
  exact
    (PeriodConjectureProblemSeal.recognizedMMQ_morphismReconstructionFromPackedComparison_sealed
      coordinates).theoremTarget f g hPacked

end RecognizedStatements

/-! ## Checked public surface -/

#check TraceCalc.PeriodConjectureAssumptionBoundary.scalar_grothendieck_period_conjecture_from_sealed_trace_calculus
#check TraceCalc.PeriodConjectureAssumptionBoundary.framed_grothendieck_period_conjecture_from_sealed_trace_calculus

#check TraceCalc.PeriodConjectureAssumptionBoundary.ScalarGrothendieckPeriodConjectureStatement
#check TraceCalc.PeriodConjectureAssumptionBoundary.FramedGrothendieckPeriodConjectureStatement

/-! ## Axiom audit -/

#print axioms TraceCalc.PeriodConjectureAssumptionBoundary.scalar_grothendieck_period_conjecture_from_sealed_trace_calculus
#print axioms TraceCalc.PeriodConjectureAssumptionBoundary.framed_grothendieck_period_conjecture_from_sealed_trace_calculus

end PeriodConjectureAssumptionBoundary
end TraceCalc