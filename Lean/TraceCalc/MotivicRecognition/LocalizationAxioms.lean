import TraceCalc.MotivicRecognition.TracePresentation

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

/-- Theorem target for correspondence functoriality on the trace-to-motive interface. -/
structure CorrFunctorialityTarget
    (trace : TracePresentation.{u, v, w, x, y})
    (motivic : MotivicCategoryCandidate trace.base) where
  Corr : Type z
  correspondenceIdentityTarget : Prop
  correspondenceCompositionTarget : Prop
  theoremTarget : Prop

/-- Theorem target for open/closed localization triangles in the candidate motivic category. -/
structure OpenClosedLocalizationTarget
    (trace : TracePresentation.{u, v, w, x, y})
    (motivic : MotivicCategoryCandidate trace.base) where
  OpenPiece : Type z
  ClosedPiece : Type z
  localizationTriangleTarget : Prop
  gluingCompatibilityTarget : Prop
  theoremTarget : Prop

/-- Theorem target for Nisnevich descent on the candidate motivic category. -/
structure NisnevichDescentTarget
    (trace : TracePresentation.{u, v, w, x, y})
    (motivic : MotivicCategoryCandidate trace.base) where
  Nis : Type z
  coverDescentTarget : Prop
  hyperdescentTarget : Prop
  theoremTarget : Prop

/-- Theorem target for A¹-invariance. -/
structure A1InvarianceTarget
    (trace : TracePresentation.{u, v, w, x, y})
    (motivic : MotivicCategoryCandidate trace.base) where
  A1 : Type z
  intervalObjectTarget : Prop
  homotopyInvarianceTarget : Prop
  theoremTarget : Prop

/-- Theorem target for the exactness of the envelope/localization interface. -/
structure EnvelopeExactnessTarget
    (trace : TracePresentation.{u, v, w, x, y})
    (motivic : MotivicCategoryCandidate trace.base) where
  Env : Type z
  envelopeFunctorialityTarget : Prop
  exactnessTarget : Prop
  theoremTarget : Prop

/-- Package of localization/descent axioms that a trace presentation must satisfy before it can be
recognized as a motivic category candidate. -/
structure AdmissibleLocalizationAxioms
    (trace : TracePresentation.{u, v, w, x, y})
    (motivic : MotivicCategoryCandidate trace.base) where
  Corr : CorrFunctorialityTarget trace motivic
  Loc : OpenClosedLocalizationTarget trace motivic
  Nis : NisnevichDescentTarget trace motivic
  A1 : A1InvarianceTarget trace motivic
  Env : EnvelopeExactnessTarget trace motivic
  localizationFeedsRecognitionTarget : Prop

end MotivicRecognition
end TraceCalc
