import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Presheaves.Linear.Owner

/-!
# Objects for the linear presheaf category input

This owner names the object surface for the category of rational-linear
presheaves on the balanced `ContourCor_Q` transfer input.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Objects in the linear presheaf category input. -/
abbrev ContourCorQLinearPresheafObject :=
  ContourCorQLinearPresheaf

/-- The underlying linear presheaf carried by an input object. -/
def ContourCorQLinearPresheafObject.toLinearPresheaf
    (F : ContourCorQLinearPresheafObject) :
    ContourCorQLinearPresheaf :=
  F

end AnalyticMotives
end LFunctions
end Boundary
