import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ChannelRectangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ResidueRectangle.Owner

/-!
# Forgetful reflection for completed-zeta finite-rectangle compact adapters

This file records concrete equality reflection through the forgetful functor
from completed-zeta finite-rectangle compact generators to trace
correspondences.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Equality after forgetting residue rectangle compact morphisms reflects equality. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_eq_of_forgetfulFunctor_map_eq
    (R : ℝ)
    {left right :
      (completedZetaZeroPoleResidueRectangleSourceGenerator R) ⟶
        completedZetaZeroPoleResidueRectangleTargetGenerator}
    (map_eq :
      TraceAnalyticGeometricGenerator.forgetfulFunctor.map left =
        TraceAnalyticGeometricGenerator.forgetfulFunctor.map right) :
    left = right :=
  map_eq

/-- Equality after forgetting scheduled-channel compact morphisms reflects equality. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_eq_of_forgetfulFunctor_map_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    {left right :
      (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u) ⟶
        completedZetaZeroPoleChannelRectangleTargetGenerator}
    (map_eq :
      TraceAnalyticGeometricGenerator.forgetfulFunctor.map left =
        TraceAnalyticGeometricGenerator.forgetfulFunctor.map right) :
    left = right :=
  map_eq

end AnalyticMotives
end LFunctions
end Boundary
