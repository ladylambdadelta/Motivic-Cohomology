import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Homs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Presheaves.Values.Owner

/-!
# Pullbacks for presheaves on `ContourCor_Q`

This owner records contravariant pullback along balanced rational contour
transfer homs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pullback data along `ContourCor_Q` transfer-input homs. -/
structure ContourCorQPresheafPullback
    (V : ContourCorQPresheafValues) where
  pullback :
    {X Y : ContourCorQPresheafObject} →
      ContourCorQPresheafHom X Y → V.valueAt Y → V.valueAt X

namespace ContourCorQPresheafPullback

/-- Pullback along one presheaf-input contour hom. -/
def along {V : ContourCorQPresheafValues}
    (P : ContourCorQPresheafPullback V)
    {X Y : ContourCorQPresheafObject}
    (f : ContourCorQPresheafHom X Y) :
    V.valueAt Y → V.valueAt X :=
  P.pullback f

end ContourCorQPresheafPullback

end AnalyticMotives
end LFunctions
end Boundary
