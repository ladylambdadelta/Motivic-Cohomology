import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Foundations.Owner

/-!
# Projections from the foundational stable certificate

This file exposes the individual foundational fields of the concrete analytic
stable-infinity owner object from the bundled foundational certificate.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The presented category is the analytic stable motive Verdier quotient. -/
theorem traceAnalyticStableInfinityCategory_foundational_presentedCategory :
    StableInfinityOwner.PresentedCategory =
      TraceAnalyticStableMotiveCategory :=
  traceAnalyticStableInfinityCategory_foundational_certificate.left

/-- The stable quasicategory is the nerve of the analytic stable motive
Verdier quotient. -/
theorem traceAnalyticStableInfinityCategory_foundational_nerve :
    TraceAnalyticStableMotiveQuasicategory =
      CategoryTheory.nerve TraceAnalyticStableMotiveCategory :=
  traceAnalyticStableInfinityCategory_foundational_certificate.right.left

/-- The owner package carries the analytic stable motive quasicategory field. -/
theorem traceAnalyticStableInfinityCategory_foundational_quasicategory :
    traceAnalyticStableInfinityCategory.quasicategory =
      TraceAnalyticStableMotiveQuasicategory.quasicategory :=
  traceAnalyticStableInfinityCategory_foundational_certificate.right.right.left

/-- The owner package carries the analytic Verdier localization field. -/
theorem traceAnalyticStableInfinityCategory_foundational_localization :
    traceAnalyticStableInfinityCategory.localization =
      TraceAnalyticStableMotiveQuasicategory.isLocalization :=
  traceAnalyticStableInfinityCategory_foundational_certificate
    .right
    .right
    .right
    .left

/-- The owner package carries the analytic stable preadditive structure. -/
theorem traceAnalyticStableInfinityCategory_foundational_preadditive :
    traceAnalyticStableInfinityCategory.preadditive =
      TraceAnalyticStableMotiveCategory.preadditiveStructure :=
  traceAnalyticStableInfinityCategory_foundational_certificate
    .right
    .right
    .right
    .right
    .left

/-- The owner package carries the pointed structure. -/
theorem traceAnalyticStableInfinityCategory_foundational_zeroObject :
    traceAnalyticStableInfinityCategory.zeroObject =
      traceAnalyticStableInfinityCategory_isPointed :=
  traceAnalyticStableInfinityCategory_foundational_certificate
    .right
    .right
    .right
    .right
    .right
    .left

/-- The owner package carries the integer shift structure. -/
theorem traceAnalyticStableInfinityCategory_foundational_shift :
    traceAnalyticStableInfinityCategory.shift =
      TraceAnalyticStableMotiveQuasicategory.hasShiftStructure :=
  traceAnalyticStableInfinityCategory_foundational_certificate
    .right
    .right
    .right
    .right
    .right
    .right
    .left

/-- The owner package carries quotient-shift compatibility. -/
theorem traceAnalyticStableInfinityCategory_foundational_quotientCommShift :
    traceAnalyticStableInfinityCategory.quotientCommShift =
      TraceAnalyticStableMotiveCategory.quotientFunctorCommShift :=
  traceAnalyticStableInfinityCategory_foundational_certificate
    .right
    .right
    .right
    .right
    .right
    .right
    .right
    .left

/-- The owner package carries the pretriangulated structure. -/
theorem traceAnalyticStableInfinityCategory_foundational_pretriangulated :
    traceAnalyticStableInfinityCategory.pretriangulated =
      TraceAnalyticStableMotiveQuasicategory.pretriangulatedStructure :=
  traceAnalyticStableInfinityCategory_foundational_certificate
    .right
    .right
    .right
    .right
    .right
    .right
    .right
    .right
    .left

/-- The owner package carries the triangulated structure. -/
theorem traceAnalyticStableInfinityCategory_foundational_triangulated :
    traceAnalyticStableInfinityCategory.triangulated =
      TraceAnalyticStableMotiveQuasicategory.triangulatedStructure :=
  traceAnalyticStableInfinityCategory_foundational_certificate
    .right
    .right
    .right
    .right
    .right
    .right
    .right
    .right
    .right
    .left

/-- The owner package carries the stable distinguished triangles. -/
theorem traceAnalyticStableInfinityCategory_foundational_distinguishedTriangles :
    traceAnalyticStableInfinityCategory.distinguishedTriangles =
      TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory_foundational_certificate
    .right
    .right
    .right
    .right
    .right
    .right
    .right
    .right
    .right
    .right

end AnalyticMotives
end LFunctions
end Boundary
