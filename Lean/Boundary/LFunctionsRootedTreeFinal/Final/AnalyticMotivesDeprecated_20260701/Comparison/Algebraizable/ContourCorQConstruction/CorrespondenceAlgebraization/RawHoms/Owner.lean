import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.FormalSums.Operations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.PrimeSupports.TransportImages.Owner

/-!
# Algebraization systems for raw contour homs

For fixed smooth algebraizations of two contour objects, this file packages the
choice of an actual parent prime finite-correspondence support for every raw
contour correspondence between them.  This is the input needed to compare the
balanced quotient of contour formal sums with parent rational finite
correspondences.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

/--
A raw-hom algebraization system for fixed algebraized source and target bulks.

The field is a constructive assignment into the parent prime finite
correspondence support type; it is not a proposition or a deferred theorem.
-/
structure ContourCorQRawHomAlgebraizationSystem
    {X Y : ContourCorQObject}
    (sourceBulk : SmoothAlgebraization G X)
    (targetBulk : SmoothAlgebraization G Y) where
  algebraize :
    (f : ContourCorQRawHom X Y) →
      AlgebraizedContourPrimeSupport sourceBulk targetBulk f
  parentPrimeGeom_eq_of_eq :
    {f g : ContourCorQRawHom X Y} →
      (h : f = g) →
        (AlgebraizedContourPrimeSupport.transportCorrespondence
          h (algebraize f)).parentPrimeGeom =
            (algebraize g).parentPrimeGeom

namespace ContourCorQRawHomAlgebraizationSystem

/-- Algebraize one raw contour hom through the system. -/
def at
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    (f : ContourCorQRawHom X Y) :
    AlgebraizedContourPrimeSupport sourceBulk targetBulk f :=
  H.algebraize f

/-- Equal raw contour homs have equal parent prime classes under the system. -/
theorem parentPrimeGeom_eq_of_eq
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    {f g : ContourCorQRawHom X Y}
    (h : f = g) :
    (AlgebraizedContourPrimeSupport.transportCorrespondence h (H.at f)).parentPrimeGeom =
      (H.at g).parentPrimeGeom :=
  H.parentPrimeGeom_eq_of_eq h

/-- Algebraize a formal sum term-by-term through a raw-hom algebraization system. -/
def formalSum
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    (S : ContourCorQFormalSum X Y) :
    AlgebraizedContourFormalSum sourceBulk targetBulk S where
  termAlgebraization := fun i => H.at (S.correspondenceAt i)

/-- The system algebraization of an empty formal sum is the canonical empty algebraization. -/
theorem formalSum_zero
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (_H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk) :
    formalSum _H (ContourCorQFormalSum.zero X Y) =
      AlgebraizedContourFormalSum.zero sourceBulk targetBulk :=
  rfl

/-- The system algebraization of a term is the canonical one-term algebraization. -/
theorem formalSum_term
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    (q : Rat)
    (f : ContourCorQRawHom X Y) :
    formalSum H (ContourCorQFormalSum.term q f) =
      AlgebraizedContourFormalSum.term q (H.at f) :=
  rfl

/-- The system algebraization of a scaled formal sum is the canonical scaled algebraization. -/
theorem formalSum_scale
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    (q : Rat)
    (S : ContourCorQFormalSum X Y) :
    formalSum H (ContourCorQFormalSum.scale q S) =
      AlgebraizedContourFormalSum.scale q (formalSum H S) :=
  rfl

/-- The system algebraization of a sum is the canonical sum algebraization. -/
theorem formalSum_add
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    (S T : ContourCorQFormalSum X Y) :
    formalSum H (ContourCorQFormalSum.add S T) =
      AlgebraizedContourFormalSum.add (formalSum H S) (formalSum H T) :=
  rfl

end ContourCorQRawHomAlgebraizationSystem

end

end AnalyticMotives
end LFunctions
end Boundary
