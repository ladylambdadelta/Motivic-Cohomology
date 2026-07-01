import Boundary.DMgm
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.ParentMotives.Effective.Owner

/-!
# Parent stabilized motive image of an algebraized analytic bulk

This file embeds the parent effective motive associated to an algebraized
contour bulk into the existing Boundary `DMgm(Q)_Q` stabilization surface.
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

/-- The stabilized parent `DMgm` image of a smooth algebraized analytic bulk. -/
def SmoothAlgebraization.parentStableMotive
    {X : ContourAdmissibleBulk}
    (A : SmoothAlgebraization G X) :
    VoevodskyDMgmQ_Q (composition := composition) :=
  (VoevodskyDMgmEffectiveEmbedding (composition := composition)).obj
    (A.parentEffectiveMotive composition)

/-- The stable image is the effective image embedded at Tate degree zero. -/
theorem SmoothAlgebraization.parentStableMotive_eq
    {X : ContourAdmissibleBulk}
    (A : SmoothAlgebraization G X) :
    A.parentStableMotive composition =
      (VoevodskyDMgmEffectiveEmbedding (composition := composition)).obj
        (A.parentEffectiveMotive composition) :=
  rfl

end

end AnalyticMotives
end LFunctions
end Boundary
