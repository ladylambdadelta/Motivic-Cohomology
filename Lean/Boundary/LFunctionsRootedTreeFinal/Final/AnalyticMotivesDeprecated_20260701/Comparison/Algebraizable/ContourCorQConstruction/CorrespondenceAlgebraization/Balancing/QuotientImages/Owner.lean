import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.TransferReady.Homs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.Balancing.ClosureImages.Owner

/-!
# Parent images of balanced quotient homs

This file descends the parent rational finite-correspondence image from formal
contour sums to transfer-ready balanced quotient homs.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

namespace ContourCorQRawHomAlgebraizationSystem

/-- The parent rational finite correspondence induced by a balanced quotient class. -/
def balancedQuotientParentRationalCorrespondence
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk) :
    ContourCorQFormalSum.BalancedQuotientHom X Y →
      RationalFiniteCorrespondence sourceBulk.scheme targetBulk.scheme :=
  Quotient.lift
    (fun S : ContourCorQFormalSum X Y =>
      (H.formalSum S).parentRationalCorrespondence)
    (fun S T h =>
      H.balancedRel_parentRationalCorrespondence h)

/-- The quotient parent image of a represented formal sum is its formal-sum parent image. -/
theorem balancedQuotientParentRationalCorrespondence_balancedClass
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    (S : ContourCorQFormalSum X Y) :
    H.balancedQuotientParentRationalCorrespondence
        (ContourCorQFormalSum.balancedClass S) =
      (H.formalSum S).parentRationalCorrespondence :=
  rfl

end ContourCorQRawHomAlgebraizationSystem

namespace ContourCorQHom

/-- The parent rational finite correspondence attached to a transfer-ready contour hom. -/
def parentRationalCorrespondence
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    (F : ContourCorQHom X Y) :
    RationalFiniteCorrespondence sourceBulk.scheme targetBulk.scheme :=
  H.balancedQuotientParentRationalCorrespondence F

/-- A represented formal sum maps to its parent rational finite correspondence. -/
theorem parentRationalCorrespondence_balancedClass
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    (S : ContourCorQFormalSum X Y) :
    parentRationalCorrespondence H (ContourCorQFormalSum.balancedClass S) =
      (H.formalSum S).parentRationalCorrespondence :=
  rfl

end ContourCorQHom

end

end AnalyticMotives
end LFunctions
end Boundary
