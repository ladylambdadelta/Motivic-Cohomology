import TraceCalc.ClassicalPeriods.PeriodConjectureTarget
import TraceCalc.ClassicalPeriods.PrimitiveTraceTomography
import TraceCalc.ClassicalBridge.PeriodTargetBridge

/-!
# Status

Experimental helper only.

This file supports the primitive-tomography scaffold in `TraceCalc/Experiments`
and is not part of the public period-conjecture proof route.
-/

universe u v w

namespace TraceCalc

open ClassicalPeriods
open ClassicalBridge

/-- Auxiliary comparison proposition from the bridge's classical framed equality to the primitive
probe equality carried by the repaired bridge data. This remains auxiliary: it is not the framed
equality of the final target. -/
def BridgeFramedPeriodEqualityToPrimitiveProbeEquality
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : LayerB.RealObjects.RewriteCalculusSetup.FoundationsBoundaryBridgeAuxiliaryData
      presentation.toDoctrine}
    (bridge : InternalProgramRealizesClassicalPeriodTarget presentation aux)
    (_certifiedTraceTransport :
      CertifiedTraceTomographyTransport
        bridge.toFramedPeriodConjectureTarget.baseTarget.structuredComparisonEquality) : Prop :=
  ∀ {X Y : bridge.classicalTarget.MotiveCategory} (f g : X ⟶ Y),
    bridge.framedPeriodEquality.relates
      (bridge.framedPeriodOf f)
      (bridge.framedPeriodOf g) →
    ProbeEquality bridge.primitiveFramedProbeFamily
      (bridge.classicalTarget.packedMorphismComparison f)
      (bridge.classicalTarget.packedMorphismComparison g)

/-- The auxiliary classical-framed-to-primitive comparison is derived from the concrete
framed-period/probe realization data on the bridge. -/
def bridgeFramedPeriodEqualityToPrimitiveProbeEquality
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : LayerB.RealObjects.RewriteCalculusSetup.FoundationsBoundaryBridgeAuxiliaryData
      presentation.toDoctrine}
    (bridge : InternalProgramRealizesClassicalPeriodTarget presentation aux)
    (certifiedTraceTransport :
      CertifiedTraceTomographyTransport
        bridge.toFramedPeriodConjectureTarget.baseTarget.structuredComparisonEquality) :
    BridgeFramedPeriodEqualityToPrimitiveProbeEquality bridge certifiedTraceTransport := by
  intro X Y f g hFramed
  exact bridge.classicalFramedEqualityInducesPrimitiveProbeEquality f g hFramed

/-- Bridge-level framed period conjecture. The theorem target is the classical framed-period
target exposed by the bridge; primitive probe data and certified tomography are auxiliary explicit
inputs, not replacements for the framed equality. -/
theorem primitive_headline_framed_period_conjecture
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : LayerB.RealObjects.RewriteCalculusSetup.FoundationsBoundaryBridgeAuxiliaryData
      presentation.toDoctrine}
    (bridge : InternalProgramRealizesClassicalPeriodTarget presentation aux)
    (_certifiedTraceTransport :
      CertifiedTraceTomographyTransport
        bridge.toFramedPeriodConjectureTarget.baseTarget.structuredComparisonEquality) :
    ClassicalPeriods.FramedPeriodConjectureTarget.faithfulnessStatement
      bridge.toFramedPeriodConjectureTarget := by
  exact ClassicalPeriods.FramedPeriodConjectureTarget.faithfulnessStatement_of_reflection
    bridge.toFramedPeriodConjectureTarget

end TraceCalc
