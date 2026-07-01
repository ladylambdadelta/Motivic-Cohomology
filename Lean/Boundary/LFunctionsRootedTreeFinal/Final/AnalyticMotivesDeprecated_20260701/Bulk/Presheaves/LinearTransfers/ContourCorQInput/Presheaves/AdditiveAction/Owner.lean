import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Presheaves.Accessors.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Laws.Owner

/-!
# Pullback consequences of hom equalities

This owner records presheaf-level consequences that follow from equalities of
balanced rational contour transfer homs.  It does not add additive structure to
the target values.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQPresheaf

/-- Equal transfer homs induce equal pullback maps. -/
theorem pullback_eq_of_hom_eq
    (F : ContourCorQPresheaf)
    {X Y : ContourCorQPresheafObject}
    {f g : ContourCorQPresheafHom X Y}
    (h : f = g) :
    F.pullbackAlong f = F.pullbackAlong g :=
  congrArg (fun u => F.pullbackAlong u) h

/-- Zero coefficient terms induce the same pullback as the zero hom. -/
theorem pullback_zero_term_eq
    (F : ContourCorQPresheaf)
    {X Y : ContourCorQPresheafObject}
    (f : ContourCorQRawHom X Y) :
    F.pullbackAlong (ContourCorQPresheafHom.term 0 f) =
      F.pullbackAlong (ContourCorQPresheafHom.zero X Y) :=
  pullback_eq_of_hom_eq F
    (ContourCorQPresheafHom.term_zero_coeff f)

/-- Coefficient collection of equal raw correspondences is respected by pullback. -/
theorem pullback_term_collect_eq
    (F : ContourCorQPresheaf)
    {X Y : ContourCorQPresheafObject}
    (q r : Rat)
    (f : ContourCorQRawHom X Y) :
    F.pullbackAlong
        (ContourCorQPresheafHom.add
          (ContourCorQPresheafHom.term q f)
          (ContourCorQPresheafHom.term r f)) =
      F.pullbackAlong (ContourCorQPresheafHom.term (q + r) f) :=
  pullback_eq_of_hom_eq F
    (ContourCorQPresheafHom.term_collect q r f)

end ContourCorQPresheaf

end AnalyticMotives
end LFunctions
end Boundary
