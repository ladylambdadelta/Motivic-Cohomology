import TraceCalc.ProbeTheory.Spheres
import TraceCalc.ProbeTheory.Reconstruction
import TraceCalc.ClassicalPeriods.ClassicalManuscriptTargets

universe u v w x y

namespace TraceCalc
namespace ProbeTheory

/-- Bridge from Tate-sphere probes to the already sealed period/tomography package.
The fields expose the connection without reproving or replacing Package 8. -/
structure PeriodTomographyProbeBridge
    (C : CategoryLike.{u, v})
    (sphereProbes : TateSphereData C)
    (Obs : ProbeObservation.{u, v, 0, x} C (TateSphereProbeFamily C sphereProbes))
    (ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v})
    (structuredEq : ClassicalPeriods.StructuredComparisonEquality ctx) where
  framedObservationIndex : Type y
  framedObservationProbe : framedObservationIndex -> MotivicSphereIndex
  FramedPeriodObservationTarget : framedObservationIndex -> C.Obj -> Prop
  framedPeriodsAsObservations :
    (j : framedObservationIndex) -> (X : C.Obj) ->
      FramedPeriodObservationTarget j X
  sealedTomography :
    ClassicalPeriods.GeometricRealizationTomographySoundness ctx structuredEq
  tomographyMatchesProbeExtensionality :
    ClassicalPeriods.GeometricRealizationTomographySoundness.faithfulFramedProbeTarget
      sealedTomography

namespace PeriodTomographyProbeBridge

variable {C : CategoryLike.{u, v}}
variable {sphereProbes : TateSphereData C}
variable {Obs : ProbeObservation.{u, v, 0, x} C (TateSphereProbeFamily C sphereProbes)}
variable {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
variable {structuredEq : ClassicalPeriods.StructuredComparisonEquality ctx}
variable (bridge : PeriodTomographyProbeBridge.{u, v, x, y} C sphereProbes Obs ctx structuredEq)

/-- Framed periods are presented as probe observations through the bridge. -/
theorem framed_periods_are_probe_observations
    (j : bridge.framedObservationIndex) (X : C.Obj) :
  bridge.FramedPeriodObservationTarget j X :=
  bridge.framedPeriodsAsObservations j X

/-- The abstract sphere-probe bridge consumes the sealed Package 8 tomography
soundness target.  This is a connector theorem, not a replacement proof of P8. -/
theorem period_tomography_from_sphere_probe_extensionality :
    ClassicalPeriods.GeometricRealizationTomographySoundness.faithfulFramedProbeTarget
      bridge.sealedTomography :=
  bridge.tomographyMatchesProbeExtensionality

end PeriodTomographyProbeBridge

end ProbeTheory
end TraceCalc
