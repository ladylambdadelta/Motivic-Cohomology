import TraceCalc.ClassicalPeriods.PrimitiveTraceTomography

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

structure CertifiedTraceTomographyTransportCore
  {ctx : ClassicalComparisonContext} where
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

namespace CertifiedTraceTomographyTransport

def ofCore
  {ctx : ClassicalComparisonContext}
    {structuredEq : StructuredComparisonEquality ctx}
    (primitiveTable : PrimitiveFamilyPeriodTomographyTable structuredEq)
    (tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq)
  (core : CertifiedTraceTomographyTransportCore (ctx := ctx)) :
    CertifiedTraceTomographyTransport structuredEq where
  primitiveTable := primitiveTable
  trace := core.trace
  primitiveTomographyTarget := core.primitiveTomographyTarget
  primitiveTomography_holds := core.primitiveTomography_holds
  traceSoundnessTarget := core.traceSoundnessTarget
  traceSoundness_holds := core.traceSoundness_holds
  replayOrderCompatibilityTarget := core.replayOrderCompatibilityTarget
  packetCutCompatibilityTarget := core.packetCutCompatibilityTarget
  canNFNormalizationCompatibilityTarget := core.canNFNormalizationCompatibilityTarget
  boundaryReconstructionCompatibilityTarget := core.boundaryReconstructionCompatibilityTarget
  coherenceWitnessCompatibilityTarget := core.coherenceWitnessCompatibilityTarget
  closureTransportTarget := core.closureTransportTarget
  closureTransport_holds := core.closureTransport_holds
  tomographySoundness := tomographySoundness

end CertifiedTraceTomographyTransport

structure CertifiedTraceTomographyClosureAlgebra
  {ctx : ClassicalComparisonContext}
    (structuredEq : StructuredComparisonEquality ctx) where
  primitiveTable : PrimitiveFamilyPeriodTomographyTable structuredEq
  tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq
  primitiveWitnessesStep :
    (witnesses : PrimitiveAdmissibleGeneratorWitnesses ctx) →
      CertifiedTraceTomographyTransportCore (ctx := ctx)
  seedStep :
    (generator : CertifiedTraceClosureGenerator ctx) →
      CertifiedTraceTomographyTransportCore (ctx := ctx)
  composeStep :
    (left right : CertifiedTraceClosure ctx) →
      CertifiedTraceTomographyTransportCore (ctx := ctx) →
      CertifiedTraceTomographyTransportCore (ctx := ctx) →
      (witness : CertifiedComposeClosureWitness ctx) →
      CertifiedTraceTomographyTransportCore (ctx := ctx)
  tensorStep :
    (left right : CertifiedTraceClosure ctx) →
      CertifiedTraceTomographyTransportCore (ctx := ctx) →
      CertifiedTraceTomographyTransportCore (ctx := ctx) →
      (witness : CertifiedTensorClosureWitness ctx) →
      CertifiedTraceTomographyTransportCore (ctx := ctx)
  whiskerStep :
    (source : CertifiedTraceClosure ctx) →
      CertifiedTraceTomographyTransportCore (ctx := ctx) →
      (witness : CertifiedWhiskerClosureWitness ctx) →
      CertifiedTraceTomographyTransportCore (ctx := ctx)
  adminStep :
    (source : CertifiedTraceClosure ctx) →
      CertifiedTraceTomographyTransportCore (ctx := ctx) →
      (witness : CertifiedStructuralAdminClosureWitness ctx) →
      CertifiedTraceTomographyTransportCore (ctx := ctx)
  shiftStep :
    (source : CertifiedTraceClosure ctx) →
      CertifiedTraceTomographyTransportCore (ctx := ctx) →
      (witness : CertifiedShiftClosureWitness ctx) →
      CertifiedTraceTomographyTransportCore (ctx := ctx)
  coneStep :
    (source : CertifiedTraceClosure ctx) →
      CertifiedTraceTomographyTransportCore (ctx := ctx) →
      (witness : CertifiedConeClosureWitness ctx) →
      CertifiedTraceTomographyTransportCore (ctx := ctx)
  cofiberStep :
    (source : CertifiedTraceClosure ctx) →
      CertifiedTraceTomographyTransportCore (ctx := ctx) →
      (witness : CertifiedCofiberClosureWitness ctx) →
      CertifiedTraceTomographyTransportCore (ctx := ctx)
  retractStep :
    (source : CertifiedTraceClosure ctx) →
      CertifiedTraceTomographyTransportCore (ctx := ctx) →
      (witness : CertifiedRetractClosureWitness ctx) →
      CertifiedTraceTomographyTransportCore (ctx := ctx)

namespace CertifiedTraceTomographyClosureAlgebraOps

noncomputable opaque ofClosureAlgebraCore
  {ctx : ClassicalComparisonContext}
  {structuredEq : StructuredComparisonEquality ctx}
  (algebra : CertifiedTraceTomographyClosureAlgebra structuredEq) :
    CertifiedTraceClosure ctx → CertifiedTraceTomographyTransportCore (ctx := ctx) :=
  CertifiedTraceClosure.rec
    (motive := fun _ => CertifiedTraceTomographyTransportCore (ctx := ctx))
    (fun witnesses => algebra.primitiveWitnessesStep witnesses)
    (fun generator => algebra.seedStep generator)
    (fun left right leftCore rightCore witness =>
      algebra.composeStep left right leftCore rightCore witness)
    (fun left right leftCore rightCore witness =>
      algebra.tensorStep left right leftCore rightCore witness)
    (fun source sourceCore witness =>
      algebra.whiskerStep source sourceCore witness)
    (fun source sourceCore witness =>
      algebra.adminStep source sourceCore witness)
    (fun source sourceCore witness =>
      algebra.shiftStep source sourceCore witness)
    (fun source sourceCore witness =>
      algebra.coneStep source sourceCore witness)
    (fun source sourceCore witness =>
      algebra.cofiberStep source sourceCore witness)
    (fun source sourceCore witness =>
      algebra.retractStep source sourceCore witness)

end CertifiedTraceTomographyClosureAlgebraOps

namespace CertifiedTraceTomographyTransport

noncomputable opaque ofClosureAlgebra
  {ctx : ClassicalComparisonContext}
    {structuredEq : StructuredComparisonEquality ctx}
  (algebra : _root_.TraceCalc.ClassicalPeriods.CertifiedTraceTomographyClosureAlgebra structuredEq) :
    CertifiedTraceClosure ctx → CertifiedTraceTomographyTransport structuredEq
  | trace => ofCore algebra.primitiveTable algebra.tomographySoundness
    (_root_.TraceCalc.ClassicalPeriods.CertifiedTraceTomographyClosureAlgebraOps.ofClosureAlgebraCore
      algebra trace)

noncomputable opaque ofClosureAlgebraAt
  {ctx : ClassicalComparisonContext}
    {structuredEq : StructuredComparisonEquality ctx}
  (algebra : _root_.TraceCalc.ClassicalPeriods.CertifiedTraceTomographyClosureAlgebra structuredEq)
    (trace : CertifiedTraceClosure ctx) :
  CertifiedTraceTomographyTransport structuredEq :=
  ofClosureAlgebra algebra trace

opaque toCertifiedTracePeriodTomographyTarget
  {ctx : ClassicalComparisonContext}
    {structuredEq : StructuredComparisonEquality ctx}
    (transport : CertifiedTraceTomographyTransport structuredEq) :
    CertifiedTracePeriodTomographyTarget
      structuredEq
      transport.primitiveTable
      (CertifiedTraceClosure ctx) :=
  CertifiedTracePeriodTomographyTarget.fromClosureTransport
    transport.primitiveTable
    (CertifiedTraceClosure ctx)
    transport.trace
    transport.primitiveTomographyTarget
    transport.primitiveTomography_holds
    transport.traceSoundnessTarget
    transport.traceSoundness_holds
    transport.replayOrderCompatibilityTarget
    transport.packetCutCompatibilityTarget
    transport.canNFNormalizationCompatibilityTarget
    transport.boundaryReconstructionCompatibilityTarget
    transport.coherenceWitnessCompatibilityTarget
    transport.closureTransportTarget
    transport.closureTransport_holds
    transport.tomographySoundness

end CertifiedTraceTomographyTransport

end ClassicalPeriods
end TraceCalc