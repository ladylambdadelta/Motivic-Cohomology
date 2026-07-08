import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Package-level isomorphism invariance of distinguished triangles

This owner file exposes forward and backward transport of distinguishedness
across triangle isomorphisms through the assembled analytic stable-infinity
package.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Package-level distinguishedness of analytic stable motive triangles is
invariant under triangle isomorphism. -/
theorem traceAnalyticStableInfinityCategory_distinguished_iff_of_triangleIso'
    {first second : StableInfinityOwner.PresentedTriangle}
    (iso : first ≅ second) :
    first ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles ↔
      second ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory.distinguished_iff_of_triangleIso iso

/-- Package-level distinguishedness transports forward across a triangle
isomorphism. -/
theorem traceAnalyticStableInfinityCategory_distinguished_of_triangleIso
    {first second : StableInfinityOwner.PresentedTriangle}
    (iso : first ≅ second)
    (first_distinguished :
      first ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    second ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  (traceAnalyticStableInfinityCategory
    .distinguished_iff_of_triangleIso iso).1
    first_distinguished

/-- Package-level distinguishedness transports backward across a triangle
isomorphism. -/
theorem traceAnalyticStableInfinityCategory_distinguished_of_triangleIso_symm
    {first second : StableInfinityOwner.PresentedTriangle}
    (iso : first ≅ second)
    (second_distinguished :
      second ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    first ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  (traceAnalyticStableInfinityCategory
    .distinguished_iff_of_triangleIso iso).2
    second_distinguished

end AnalyticMotives
end LFunctions
end Boundary
