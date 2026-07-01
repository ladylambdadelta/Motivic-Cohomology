import Boundary.EffectiveMotiveFunctor
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.ParentMotives.SmoothAlgebraization.Owner

/-!
# Parent effective motive image of an algebraized analytic bulk

This file applies the existing Boundary effective-motive constructor to the
smooth algebraization carried by a contour-admissible analytic bulk.
-/

universe u

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround}
variable (composition : Boundary.CanonicalCompositionData (k := G.carrier))
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable [(canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]

/-- The parent effective motive attached to a smooth algebraized analytic bulk. -/
def SmoothAlgebraization.parentEffectiveMotive
    {X : ContourAdmissibleBulk}
    (A : SmoothAlgebraization G X) :
    canonicalEffectiveMotives composition :=
  canonicalEffectiveMotive composition A.scheme

/-- The parent effective image is exactly the canonical motive of the smooth scheme. -/
theorem SmoothAlgebraization.parentEffectiveMotive_eq
    {X : ContourAdmissibleBulk}
    (A : SmoothAlgebraization G X) :
    A.parentEffectiveMotive composition =
      canonicalEffectiveMotive composition A.scheme :=
  rfl

end

end AnalyticMotives
end LFunctions
end Boundary
