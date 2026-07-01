import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.DMgmQQ.Tate.Owner

/-!
# Stable-package coherence for comparison with `DM_gm(ℚ)_ℚ`

This file owns the compatibility between the analytic stable package and the
analytic object used by the downstream comparison with `DM_gm(ℚ)_ℚ`.
It prevents the comparison layer from using a Tate-stabilized analytic
presheaf disconnected from the stable package being compared.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Coherence between a stable analytic motive package and the Tate comparison
object used in the `DM_gm(ℚ)_ℚ` comparison layer.
-/
structure DMgmQQStableCoherenceComparison
    {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (C : DMgmQQTateComparison M) where
  stablePackage : StableAnalyticMotivePackage
  tateStabilization_eq :
    C.analyticStabilization =
      stablePackage.stabilizedLayer.stabilizedPresheaf

namespace DMgmQQStableCoherenceComparison

/-- The stable analytic motive package used by the comparison. -/
def package {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    {C : DMgmQQTateComparison M}
    (S : DMgmQQStableCoherenceComparison C) :
    StableAnalyticMotivePackage :=
  S.stablePackage

/-- The stable package's stabilized analytic motive. -/
def stabilizedLayer {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    {C : DMgmQQTateComparison M}
    (S : DMgmQQStableCoherenceComparison C) :
    StabilizedAnalyticMotive :=
  S.stablePackage.stabilizedLayer

/--
The analytic Tate stabilization used in the comparison agrees with the
stabilized presheaf of the stable package.
-/
theorem tateStabilization_compatibility
    {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    {C : DMgmQQTateComparison M}
    (S : DMgmQQStableCoherenceComparison C) :
    C.analyticStabilization =
      S.stablePackage.stabilizedLayer.stabilizedPresheaf :=
  S.tateStabilization_eq

/--
The stable package's compact-geometric closed object agrees with the analytic
Tate stabilization used in the comparison.
-/
theorem compactGeometric_closedObject_compatibility
    {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    {C : DMgmQQTateComparison M}
    (S : DMgmQQStableCoherenceComparison C) :
    S.stablePackage.compactLayer.compactGeometric.thickClosure.closedObject =
      C.analyticStabilization :=
  Eq.trans
    (StableAnalyticMotivePackage.compactGeometric_closedObject_compatibility
      S.stablePackage)
    (Eq.symm S.tateStabilization_eq)

end DMgmQQStableCoherenceComparison

end AnalyticMotives
end LFunctions
end Boundary
