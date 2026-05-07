import TraceCalc.ClassicalPeriods.LinearTomography
import TraceCalc.LayerD.PeriodFaithfulnessAssembly
import TraceCalc.LayerD.SourceTracePackage
import TraceCalc.LayerE.TargetComparisonPackage
import TraceCalc.LayerF.RealizationPackage

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

/-- Expected provider of a reverse-mathematics obligation. -/
inductive ClassicalPeriodInputProvider where
  | layerB
  | layerE
  | layerF
  | layerD
  | classicalBridge
  | middleware
  deriving DecidableEq, Repr

/-- Classical motivic-category recognition theorem target. -/
structure ClassicalMotivicCategoryObligation where
  MotivicCategoryRecognitionData : Type u
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Betti realization theorem target. -/
structure BettiRealizationObligation where
  BettiRealizationData : Type v
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- de Rham realization theorem target. -/
structure DeRhamRealizationObligation where
  DeRhamRealizationData : Type w
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Comparison-isomorphism theorem target. -/
structure ComparisonIsomorphismObligation where
  ComparisonIsomorphismData : Type x
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Framed-period extraction theorem target. -/
structure FramedPeriodExtractionObligation where
  FramedPeriodExtractionData : Type y
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Scalar-shadow extraction theorem target. -/
structure ScalarShadowExtractionObligation where
  ScalarShadowExtractionData : Type z
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Packed structured-comparison assignment theorem target. -/
structure PackedStructuredComparisonAssignmentObligation where
  PackedAssignmentData : Type (max u v)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Pointwise soundness of the scalar shadow on packed structured comparison morphisms. -/
structure ScalarShadowSoundnessObligation where
  ShadowSoundnessData : Type (max u v w)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Pointwise soundness of the framed shadow on framed witnesses. -/
structure FramedShadowSoundnessObligation where
  ShadowSoundnessData : Type (max u v x)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Compatibility between the framed shadow and the scalar shadow of the packed comparison datum. -/
structure FramedToScalarCompatibilityObligation where
  CompatibilityData : Type (max u v y)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Probe family data for tomography. -/
structure ProbeFamilyObligation where
  ProbeFamilyData : Type (max u v w)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Probe soundness target: framed equality or equivalent witness equality is reflected by all
probe evaluations. -/
structure ProbeSoundnessObligation where
  ProbeSoundnessData : Type (max u v x)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Phase 7 theorem target: an honest separating probe family for the tomography step. -/
structure TomographicProbeSeparationObligation where
  ProbeSeparationData : Type (max u v w)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Phase 7 theorem target: vector/covector or framed probes determine the basis-free period
map. -/
structure BasisFreeExtensionalityObligation where
  ExtensionalityData : Type (max u v x)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Probe extensionality target: equality on all probes determines the basis-free period map. -/
structure ProbeExtensionalityObligation where
  ProbeExtensionalityData : Type (max u v y)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Phase 7 theorem target: packed structured comparison data can be reconstructed from the
basis-free period map. -/
structure PackedComparisonReconstructionObligation where
  ReconstructionData : Type (max u v y)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Phase 8 theorem target: for fixed source and target comparison objects, the basis-free period
map already reconstructs the scalar-extended realization maps. -/
structure OverScalarBasisFreeReconstructionObligation where
  ReconstructionData : Type (max u v y)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Phase 8 theorem target: descend from scalar-extended realization-map equality to equality of
the underlying Betti/de Rham realization maps. -/
structure BaseRealizationReconstructionObligation where
  ReconstructionData : Type (max u v z)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Phase 8 theorem target: for a fixed source/target pair, basis-free period-map equality gives
literal equality of the packed structured comparison package. -/
structure FixedObjectPackedComparisonReconstructionObligation where
  ReconstructionData : Type (max u v z)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Reconstruction target from the basis-free period map back to the packed structured comparison
package. -/
structure BasisFreeToPackedReconstructionObligation where
  ReconstructionData : Type (max u v z)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Phase 7 assembly target: the probe-separation and reconstruction ingredients assemble a real
tomography core. -/
structure TomographyCoreObligation where
  TomographyCoreData : Type (max u v w x y z)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Assembly target sending tomography plus shadow compatibility into the reflection core. -/
structure TomographyToReflectionObligation where
  TomographyAssemblyData : Type (max u v w x y z)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Scalar-shadow equality reflects structured comparison theorem target. -/
structure ScalarReflectsStructuredObligation where
  ScalarReflectionData : Type (max u v)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Framed equality reflection target: framed-period equality should recover the underlying
structured comparison package. This is the first honest reflection step in the framed lane. -/
structure FramedEqualityReflectsStructuredComparisonObligation where
  ReflectionData : Type (max u v w)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Coarse scalar shadow reflection target: equality of extracted scalar shadows should recover the
framed-period witness, not just the final scalar. -/
structure ScalarShadowReflectsFramedEqualityObligation where
  ReflectionData : Type (max u v x)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Derived reflection target collapsing the previous two layers. -/
structure ScalarShadowReflectsStructuredComparisonObligation where
  ReflectionData : Type (max u v w x)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Structured comparison equality reflects motive-morphism equality theorem target. -/
structure StructuredFaithfulnessObligation where
  StructuredFaithfulnessData : Type (max w x)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Final assembly theorem target from the minimal reverse-math package. -/
structure FinalAssemblyTheoremObligation where
  FinalAssemblyData : Type (max u v w x y z)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Trace-program to classical-period bridge theorem target. -/
structure TraceToClassicalBridgeObligation where
  TraceBridgeData : Type (max u v w x y z)
  theoremTarget : Prop
  expectedProvider : ClassicalPeriodInputProvider

/-- Full reverse-mathematics obligation list for the classical period target. -/
structure ClassicalPeriodReflectionObligations where
  framedReflectsStructured : FramedEqualityReflectsStructuredComparisonObligation
  scalarReflectsFramed : ScalarShadowReflectsFramedEqualityObligation
  scalarReflectsStructured : ScalarReflectsStructuredObligation
  scalarShadowReflectsStructured : ScalarShadowReflectsStructuredComparisonObligation

/-- Faithfulness-side obligations above the reflection core. -/
structure ClassicalPeriodFaithfulnessObligations where
  structuredFaithfulness : StructuredFaithfulnessObligation
  traceToClassicalBridge : TraceToClassicalBridgeObligation

/-- Full reverse-mathematics obligation list for the classical period target. -/
structure ClassicalPeriodReverseMathObligations where
  classicalMotivicCategory : ClassicalMotivicCategoryObligation
  bettiRealization : BettiRealizationObligation
  deRhamRealization : DeRhamRealizationObligation
  comparisonIsomorphism : ComparisonIsomorphismObligation
  packedStructuredComparisonAssignment : PackedStructuredComparisonAssignmentObligation
  probeFamily : ProbeFamilyObligation
  framedPeriodExtraction : FramedPeriodExtractionObligation
  scalarShadowExtraction : ScalarShadowExtractionObligation
  scalarShadowSoundness : ScalarShadowSoundnessObligation
  framedShadowSoundness : FramedShadowSoundnessObligation
  framedToScalarCompatibility : FramedToScalarCompatibilityObligation
  probeSoundness : ProbeSoundnessObligation
  tomographicProbeSeparation : TomographicProbeSeparationObligation
  basisFreeExtensionality : BasisFreeExtensionalityObligation
  probeExtensionality : ProbeExtensionalityObligation
  overScalarBasisFreeReconstruction : OverScalarBasisFreeReconstructionObligation
  baseRealizationReconstruction : BaseRealizationReconstructionObligation
  fixedObjectPackedComparisonReconstruction : FixedObjectPackedComparisonReconstructionObligation
  packedComparisonReconstruction : PackedComparisonReconstructionObligation
  basisFreeToPackedReconstruction : BasisFreeToPackedReconstructionObligation
  tomographyCore : TomographyCoreObligation
  tomographyToReflection : TomographyToReflectionObligation
  reflectionCore : ClassicalPeriodReflectionObligations
  faithfulnessLayer : ClassicalPeriodFaithfulnessObligations
  framedReflectsStructured : FramedEqualityReflectsStructuredComparisonObligation
  scalarReflectsFramed : ScalarShadowReflectsFramedEqualityObligation
  scalarReflectsStructured : ScalarReflectsStructuredObligation
  scalarShadowReflectsStructured : ScalarShadowReflectsStructuredComparisonObligation
  structuredFaithfulness : StructuredFaithfulnessObligation
  traceToClassicalBridge : TraceToClassicalBridgeObligation
  finalAssembly : FinalAssemblyTheoremObligation

/-- Minimal reverse-math package sufficient for the final classical target. -/
structure ClassicalPeriodMinimalReverseMathPackage where
  motivicCategoryTarget : ClassicalMotivicCategoryObligation
  packedStructuredComparisonAssignment : PackedStructuredComparisonAssignmentObligation
  motiveMorphismEqualityTarget : StructuredFaithfulnessObligation
  probeFamily : ProbeFamilyObligation
  scalarShadowExtraction : ScalarShadowExtractionObligation
  framedPeriodExtraction : FramedPeriodExtractionObligation
  scalarShadowSoundness : ScalarShadowSoundnessObligation
  framedShadowSoundness : FramedShadowSoundnessObligation
  framedToScalarCompatibility : FramedToScalarCompatibilityObligation
  probeSoundness : ProbeSoundnessObligation
  tomographicProbeSeparation : TomographicProbeSeparationObligation
  basisFreeExtensionality : BasisFreeExtensionalityObligation
  probeExtensionality : ProbeExtensionalityObligation
  overScalarBasisFreeReconstruction : OverScalarBasisFreeReconstructionObligation
  baseRealizationReconstruction : BaseRealizationReconstructionObligation
  fixedObjectPackedComparisonReconstruction : FixedObjectPackedComparisonReconstructionObligation
  packedComparisonReconstruction : PackedComparisonReconstructionObligation
  basisFreeToPackedReconstruction : BasisFreeToPackedReconstructionObligation
  tomographyCore : TomographyCoreObligation
  tomographyToReflection : TomographyToReflectionObligation
  reflectionCore : ClassicalPeriodReflectionObligations
  structuredFaithfulness : StructuredFaithfulnessObligation
  finalAssembly : FinalAssemblyTheoremObligation

/-- Tomography-specific reverse-math package refining the Phase 5 minimal package. -/
structure ClassicalPeriodTomographyObligations where
  probeFamily : ProbeFamilyObligation
  probeSoundness : ProbeSoundnessObligation
  tomographicProbeSeparation : TomographicProbeSeparationObligation
  basisFreeExtensionality : BasisFreeExtensionalityObligation
  probeExtensionality : ProbeExtensionalityObligation
  overScalarBasisFreeReconstruction : OverScalarBasisFreeReconstructionObligation
  baseRealizationReconstruction : BaseRealizationReconstructionObligation
  fixedObjectPackedComparisonReconstruction : FixedObjectPackedComparisonReconstructionObligation
  packedComparisonReconstruction : PackedComparisonReconstructionObligation
  basisFreeToPackedReconstruction : BasisFreeToPackedReconstructionObligation
  tomographyCore : TomographyCoreObligation
  tomographyToReflection : TomographyToReflectionObligation

/-- Reverse-mathematics dependency DAG for the classical period target.

The node fields are theorem targets. The implication fields record how those targets compose into
the final classical-faithfulness theorem without requiring the actual proofs in this file. -/
structure ClassicalPeriodProofSpine where
  packedStructuredComparisonTarget : Prop
  structuredComparisonDatumTarget : Prop
  basisFreePeriodMapTarget : Prop
  framedPeriodDatumTarget : Prop
  scalarShadowTarget : Prop
  probeFamilyTarget : Prop
  probeEqualityTarget : Prop
  tomographicProbeSeparationTarget : Prop
  basisFreeExtensionalityTarget : Prop
  overScalarBasisFreeReconstructionTarget : Prop
  baseRealizationReconstructionTarget : Prop
  fixedObjectPackedComparisonReconstructionTarget : Prop
  packedComparisonReconstructionTarget : Prop
  tomographyTarget : Prop
  tomographyCoreAssemblyTarget : Prop
  scalarShadowSoundnessTarget : Prop
  framedShadowSoundnessTarget : Prop
  framedToScalarCompatibilityTarget : Prop
  basisFreeReflectsStructuredTarget : Prop
  framedEqualityReflectsStructuredTarget : Prop
  scalarShadowReflectsFramedTarget : Prop
  scalarShadowReflectsStructuredTarget : Prop
  structuredFaithfulnessTarget : Prop
  classicalPeriodFaithfulnessTarget : Prop
  finalAssemblyTarget : Prop
  structuredFromPackedAssignmentTarget :
    packedStructuredComparisonTarget → structuredComparisonDatumTarget
  probesFromScalarShadowTarget :
    probeFamilyTarget → scalarShadowTarget → probeEqualityTarget
  tomographyCoreFromPhase7Target :
    probeFamilyTarget →
      tomographicProbeSeparationTarget →
        basisFreeExtensionalityTarget →
          packedComparisonReconstructionTarget →
            tomographyCoreAssemblyTarget
  fixedObjectPackedComparisonFromPhase8Target :
    overScalarBasisFreeReconstructionTarget →
      baseRealizationReconstructionTarget →
        fixedObjectPackedComparisonReconstructionTarget
  basisFreeFromProbesTarget :
    probeEqualityTarget → basisFreePeriodMapTarget
  packedFromBasisFreeTarget :
    basisFreePeriodMapTarget → structuredComparisonDatumTarget
  reflectionFromTomographyTarget :
    tomographyTarget → scalarShadowReflectsStructuredTarget
  basisFreeFromStructuredTarget :
    structuredComparisonDatumTarget → basisFreePeriodMapTarget
  framedFromBasisFreeTarget :
    basisFreePeriodMapTarget → framedPeriodDatumTarget
  scalarFromFramedTarget :
    framedPeriodDatumTarget → scalarShadowTarget
  structuredFromBasisFreeReflectionTarget :
    basisFreeReflectsStructuredTarget →
      basisFreePeriodMapTarget → structuredComparisonDatumTarget
  scalarStructuredFromTwoStepReflectionTarget :
    scalarShadowReflectsFramedTarget →
      framedEqualityReflectsStructuredTarget →
        scalarShadowReflectsStructuredTarget
  classicalFaithfulnessFromCoreTarget :
    scalarShadowReflectsStructuredTarget →
      structuredFaithfulnessTarget →
        classicalPeriodFaithfulnessTarget
  finalAssemblyFromMinimalPackageTarget :
    scalarShadowSoundnessTarget →
      framedShadowSoundnessTarget →
        framedToScalarCompatibilityTarget →
          scalarShadowReflectsStructuredTarget →
            structuredFaithfulnessTarget →
              finalAssemblyTarget

/-- Stable exported name for the reverse-math DAG consumed later by bridge code. -/
abbrev ClassicalPeriodReverseMathDAG := ClassicalPeriodProofSpine

/-- Symbolic slot naming the current internal package surfaces expected to discharge the classical
period target obligations. This is deliberately bridge-shaped rather than a theorem. -/
structure ClassicalPeriodTargetInputsFromTraceProgram where
  sourceTracePackage : LayerD.SourceTracePackage
  LayerBSourcePresentationSlot : Type u
  layerBPresentationBridgeTarget : Prop
  targetTheoremPackage : LayerE.MotivicTargetTheoremPackage
  structuredScalarTheoremPackage : LayerF.StructuredScalarTheoremPackage
  targetRecognitionPackage : LayerD.TargetMotivicRecognitionPackage
  comparisonPackage : LayerD.InfinityComparisonPackage
  structuredPackage : LayerD.StructuredRealizationPackage
  scalarPackage : LayerD.ScalarShadowExtractionPackage
  faithfulnessContext : LayerD.PeriodFaithfulnessContext
  proofSpine : ClassicalPeriodProofSpine
  reverseMathObligations : ClassicalPeriodReverseMathObligations
  ClassicalBridgeAdapterSlot : Type v
  classicalBridgeAdapterTarget : Prop

/-- Stable exported name for middleware consumption of the bridge input package. -/
abbrev TargetReverseMathObligationObject := ClassicalPeriodReverseMathObligations

end ClassicalPeriods
end TraceCalc
