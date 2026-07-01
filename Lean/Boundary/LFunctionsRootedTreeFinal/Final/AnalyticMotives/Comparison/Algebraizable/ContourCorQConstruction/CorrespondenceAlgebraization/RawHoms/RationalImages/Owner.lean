import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.RawHoms.Owner

/-!
# Rational parent images of raw contour homs

This file owns the composition-ready parent image system for raw contour
correspondences.  Unlike the prime-support algebraization system, its codomain
is the full parent rational finite-correspondence group, so images may be
finite rational sums of geometric prime correspondences.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

/--
A rational parent image system for raw contour homs between fixed algebraized
source and target bulks.
-/
structure ContourCorQRawHomRationalImageSystem
    {X Y : ContourCorQObject}
    (sourceBulk : SmoothAlgebraization G X)
    (targetBulk : SmoothAlgebraization G Y) where
  image :
    ContourCorQRawHom X Y →
      RationalFiniteCorrespondence sourceBulk.scheme targetBulk.scheme

namespace ContourCorQRawHomRationalImageSystem

/-- The parent rational image assigned to one raw contour hom. -/
def at
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (f : ContourCorQRawHom X Y) :
    RationalFiniteCorrespondence sourceBulk.scheme targetBulk.scheme :=
  H.image f

/-- Equal raw contour homs have equal rational parent images. -/
theorem at_eq_of_eq
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    {f g : ContourCorQRawHom X Y}
    (h : f = g) :
    H.at f = H.at g :=
  congrArg H.at h

/-- The rational image system induced by a prime-support algebraization system. -/
def ofPrimeAlgebraizationSystem
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk) :
    ContourCorQRawHomRationalImageSystem sourceBulk targetBulk where
  image := fun f => (H.at f).parentRationalCorrespondence

/-- The rational image induced from a prime-support system is the singleton parent image. -/
theorem ofPrimeAlgebraizationSystem_at
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    (f : ContourCorQRawHom X Y) :
    (ofPrimeAlgebraizationSystem H).at f =
      (H.at f).parentRationalCorrespondence :=
  rfl

end ContourCorQRawHomRationalImageSystem

end

end AnalyticMotives
end LFunctions
end Boundary
