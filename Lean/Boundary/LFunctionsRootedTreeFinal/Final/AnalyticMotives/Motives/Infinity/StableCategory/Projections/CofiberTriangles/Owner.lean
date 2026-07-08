import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.HomotopyCategory.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.StableInfinityStructure.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Geometry.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Preadditive.Owner

/-!
# Cofiber-triangle projections for the analytic stable infinity category

This file owns the chosen cofiber triangle projections formerly exposed
directly from the stable-category aggregate owner.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The owner-level stable infinity category records the chosen cofiber
object construction. -/
theorem traceAnalyticStableInfinityCategory_cofiberObject
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.cofiberObject morphism =
      TraceAnalyticStableMotiveQuasicategory.cofiberObject morphism :=
  rfl

/-- The owner-level stable infinity category records the chosen map from the
target to the cofiber object. -/
theorem traceAnalyticStableInfinityCategory_cofiberCoconeMap
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism =
      TraceAnalyticStableMotiveQuasicategory.cofiberCoconeMap morphism :=
  rfl

/-- The owner-level stable infinity category records the chosen cofiber
boundary map. -/
theorem traceAnalyticStableInfinityCategory_cofiberBoundary
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.cofiberBoundary morphism =
      TraceAnalyticStableMotiveQuasicategory.cofiberBoundary morphism :=
  rfl

/-- The owner-level stable infinity category records the chosen cofiber
triangle. -/
theorem traceAnalyticStableInfinityCategory_cofiberTriangle
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.cofiberTriangle morphism =
      TraceAnalyticStableMotiveQuasicategory.cofiberTriangle morphism :=
  rfl

/-- The owner-level stable infinity category records that the chosen cofiber
triangle is distinguished. -/
theorem traceAnalyticStableInfinityCategory_cofiberTriangle_distinguished
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.cofiberTriangle morphism ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory.cofiberTriangle_distinguished morphism

/-- The owner-level stable infinity category records the rotated chosen
cofiber triangle. -/
theorem traceAnalyticStableInfinityCategory_rotatedCofiberTriangle
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.rotatedCofiberTriangle morphism =
      TraceAnalyticStableMotiveQuasicategory.rotatedCofiberTriangle
        morphism :=
  rfl

/-- The owner-level stable infinity category records that the rotated chosen
cofiber triangle is distinguished. -/
theorem
    traceAnalyticStableInfinityCategory_rotatedCofiberTriangle_distinguished
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.rotatedCofiberTriangle morphism ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory
    .rotatedCofiberTriangle_distinguished
    morphism

/-- The owner-level stable infinity category records the inverse-rotated
chosen cofiber triangle. -/
theorem traceAnalyticStableInfinityCategory_invRotatedCofiberTriangle
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.invRotatedCofiberTriangle
        morphism =
      TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberTriangle
        morphism :=
  rfl

/-- The owner-level stable infinity category records that the inverse-rotated
chosen cofiber triangle is distinguished. -/
theorem
    traceAnalyticStableInfinityCategory_invRotatedCofiberTriangle_distinguished
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.invRotatedCofiberTriangle morphism ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory
    .invRotatedCofiberTriangle_distinguished
    morphism

end AnalyticMotives
end LFunctions
end Boundary
