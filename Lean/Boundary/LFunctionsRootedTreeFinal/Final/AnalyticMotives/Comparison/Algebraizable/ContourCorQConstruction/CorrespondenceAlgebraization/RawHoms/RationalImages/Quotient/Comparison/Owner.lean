import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.Balancing.QuotientImages.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.RawHoms.RationalImages.Quotient.Owner

/-!
# Comparison between prime and broad quotient images

This file proves that the broad rational quotient image induced by a
prime-support algebraization system agrees with the earlier singleton-prime
quotient image.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

namespace ContourCorQRawHomRationalImageSystem

/--
For a formal sum, the broad rational image induced by a prime-support
algebraization system agrees with the termwise parent finite-correspondence
image already attached to the algebraized formal sum.
-/
theorem ofPrimeAlgebraizationSystem_formalSumImage
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    (S : ContourCorQFormalSum X Y) :
    (ContourCorQRawHomRationalImageSystem.ofPrimeAlgebraizationSystem H).formalSumImage S =
      (H.formalSum S).parentRationalCorrespondence :=
  Finset.sum_congr
    rfl
    (fun i _ =>
      Eq.trans
        (Finsupp.smul_single'
          (S.coeffAt i)
          ((H.formalSum S).parentPrimeGeomAt i)
          (1 : Rat))
        (congrArg
          (fun q : Rat =>
            Finsupp.single ((H.formalSum S).parentPrimeGeomAt i) q)
          (mul_one (S.coeffAt i))))

/--
On balanced quotient contour homs, the broad rational image induced by a
prime-support system agrees with the singleton-prime quotient image.
-/
theorem ofPrimeAlgebraizationSystem_quotientImage
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    (F : ContourCorQHom X Y) :
    (ContourCorQRawHomRationalImageSystem.ofPrimeAlgebraizationSystem H).quotientImage F =
      ContourCorQHom.parentRationalCorrespondence H F :=
  Quotient.inductionOn F
    (fun S =>
      Eq.trans
        ((ContourCorQRawHomRationalImageSystem.ofPrimeAlgebraizationSystem H).quotientImage_balancedClass S)
        (Eq.trans
          (ofPrimeAlgebraizationSystem_formalSumImage H S)
          (Eq.symm
            (ContourCorQHom.parentRationalCorrespondence_balancedClass H S))))

end ContourCorQRawHomRationalImageSystem

end

end AnalyticMotives
end LFunctions
end Boundary
