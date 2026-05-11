import TraceCalc.ClassicalPeriods.SymbolicGeneratorExamples
import TraceCalc.ClassicalPeriods.CertifiedTraceClosureSurface

set_option maxHeartbeats 800000

/- This module is a transport-lemma layer for certified trace tomography.  It is consumed by
classical-facing `DM_gm(Q)_Q` / `MM(Q)` recognition bridges rather than serving as a standalone
period-faithfulness endpoint. -/

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

structure CertifiedTraceTomographyTransport
  {ctx : ClassicalComparisonContext}
    (structuredEq : StructuredComparisonEquality ctx) where
  primitiveTable : PrimitiveFamilyPeriodTomographyTable structuredEq
  trace : CertifiedTraceClosure ctx
  primitiveTomographyTarget : Prop
  primitiveTomography_holds : primitiveTomographyTarget
  traceSoundnessTarget : Prop
  traceSoundness_holds : traceSoundnessTarget
  replayOrderCompatibilityTarget : Prop
  packetCutCompatibilityTarget : Prop
  canNFNormalizationCompatibilityTarget : Prop
  boundaryReconstructionCompatibilityTarget : Prop
  coherenceWitnessCompatibilityTarget : Prop
  closureTransportTarget : Prop
  closureTransport_holds : closureTransportTarget
  tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq

namespace TracePeriodTomographyFromPrimitiveFamilies

end TracePeriodTomographyFromPrimitiveFamilies

end ClassicalPeriods
end TraceCalc
