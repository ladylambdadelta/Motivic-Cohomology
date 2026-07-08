import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Owner

/-!
# Isomorphism invariance of distinguished analytic stable triangles

This owner file exposes the fact that distinguished analytic stable triangles
are invariant under isomorphism in the triangle category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Distinguishedness of analytic stable motive triangles is invariant under
triangle isomorphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.distinguished_iff_of_triangleIso
    {first second : StableInfinityOwner.PresentedTriangle}
    (iso : first ≅ second) :
    first ∈ TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles ↔
      second ∈ TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles :=
  Pretriangulated.distinguished_iff_of_iso iso

/-- A distinguished analytic stable motive triangle transports forward across
a triangle isomorphism. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.distinguished_of_triangleIso
    {first second : StableInfinityOwner.PresentedTriangle}
    (iso : first ≅ second)
    (first_distinguished :
      first ∈ TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles) :
    second ∈ TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles :=
  (TraceAnalyticStableMotiveQuasicategory
    .distinguished_iff_of_triangleIso iso).1
    first_distinguished

/-- A distinguished analytic stable motive triangle transports backward
across a triangle isomorphism. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.distinguished_of_triangleIso_symm
    {first second : StableInfinityOwner.PresentedTriangle}
    (iso : first ≅ second)
    (second_distinguished :
      second ∈ TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles) :
    first ∈ TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles :=
  (TraceAnalyticStableMotiveQuasicategory
    .distinguished_iff_of_triangleIso iso).2
    second_distinguished

end AnalyticMotives
end LFunctions
end Boundary
