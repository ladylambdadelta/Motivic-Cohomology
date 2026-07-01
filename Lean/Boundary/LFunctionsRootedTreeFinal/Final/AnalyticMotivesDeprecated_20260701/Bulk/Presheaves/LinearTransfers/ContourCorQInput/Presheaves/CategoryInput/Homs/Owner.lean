import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Presheaves.CategoryInput.Objects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Presheaves.Morphisms.Linear.Owner

/-!
# Homs for the linear presheaf category input

This owner names the hom surface for rational-linear presheaves on
`ContourCor_Q`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Homs in the linear presheaf category input. -/
abbrev ContourCorQLinearPresheafHom
    (F G : ContourCorQLinearPresheafObject) :=
  ContourCorQLinearPresheafMorphism F G

/-- The component of a linear presheaf hom at an object of `ContourCor_Q`. -/
def ContourCorQLinearPresheafHom.componentAt
    {F G : ContourCorQLinearPresheafObject}
    (η : ContourCorQLinearPresheafHom F G)
    (X : ContourCorQPresheafObject) :
    F.valueAt X → G.valueAt X :=
  η.componentAt X

end AnalyticMotives
end LFunctions
end Boundary
