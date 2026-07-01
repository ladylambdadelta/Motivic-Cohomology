import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Objects.Owner

/-!
# Homs for the `ContourCor_Q` presheaf input

This owner exposes the transfer hom type consumed by presheaves: the balanced
rational linear span of raw contour-compatible correspondences.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Homs in the transfer input for contour presheaves. -/
abbrev ContourCorQPresheafHom
    (X Y : ContourCorQPresheafObject) : Type :=
  ContourCorQHom X Y

/-- A raw contour-compatible correspondence as a presheaf-input hom. -/
def ContourCorQPresheafHom.single
    {X Y : ContourCorQPresheafObject}
    (f : ContourCorQRawHom X Y) :
    ContourCorQPresheafHom X Y :=
  ContourCorQHom.single f

/-- A rationally weighted raw contour-compatible correspondence as a presheaf-input hom. -/
def ContourCorQPresheafHom.term
    {X Y : ContourCorQPresheafObject}
    (q : Rat) (f : ContourCorQRawHom X Y) :
    ContourCorQPresheafHom X Y :=
  ContourCorQHom.term q f

end AnalyticMotives
end LFunctions
end Boundary
