import TraceCalc.ClassicalBridge.ClassicalBridgeAnchors
import TraceCalc.LayerD.MotivicRecognition.LocalizationAxioms
import TraceCalc.LayerD.MotivicRecognition.TracePresentation

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

/-- Typed classical/geometric presentation expected downstream of trace recognition. -/
structure ClassicalMotivicPresentation
    (trace : TracePresentation.{u, v, w, x, y}) where
  bridgePresentation : ClassicalBridge.ClassicalMotivicPresentation
  bridgePresentationAgreementTarget :
    bridgePresentation = trace.sourceRealization.classicalPresentation
  motivicCategory : MotivicCategoryCandidate.{u, v, z, z} trace.base
  traceLocalizationReadiness : TraceLocalizationReadiness trace motivicCategory
  admissibleLocalizationAxioms : AdmissibleLocalizationAxioms trace motivicCategory
  classicalContext : ClassicalBridge.ClassicalComparisonContext.{u, v}
  structuredComparisonEquality : ClassicalBridge.StructuredComparisonEquality classicalContext
  geometricObjectInterpretationTarget : Prop
  correspondenceInterpretationTarget : Prop
  realizationFunctorCompatibilityTarget : Prop
  classicalPeriodsComparisonTarget : Prop
  periodTomographyCompatibilityTarget : Prop
  internalHolographyFeedsComparisonTarget : Prop

/-- Named classical theorem boundary for the Corr/Loc/Nis/A1/Env facts used by
the `DM_gm(Q)_Q` recognition path. -/
structure ClassicalDMgmQPresentationTheorems
    {trace : TracePresentation.{u, v, w, x, y}}
    (presentation : ClassicalMotivicPresentation trace) where
  corr_holds : presentation.admissibleLocalizationAxioms.Corr.theoremTarget
  loc_holds : presentation.admissibleLocalizationAxioms.Loc.theoremTarget
  nis_holds : presentation.admissibleLocalizationAxioms.Nis.theoremTarget
  a1_holds : presentation.admissibleLocalizationAxioms.A1.theoremTarget
  env_holds : presentation.admissibleLocalizationAxioms.Env.theoremTarget
  env_exactness_holds : presentation.admissibleLocalizationAxioms.Env.exactnessTarget

end MotivicRecognition
end TraceCalc
