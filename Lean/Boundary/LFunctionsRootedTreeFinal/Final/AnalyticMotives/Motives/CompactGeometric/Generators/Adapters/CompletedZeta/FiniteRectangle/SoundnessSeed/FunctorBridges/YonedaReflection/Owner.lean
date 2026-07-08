import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ChannelRectangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ResidueRectangle.Owner

/-!
# Yoneda reflection for completed-zeta finite-rectangle compact adapters

This file records concrete equality reflection through lifted representable
objects for the completed-zeta finite-rectangle compact-generator adapters.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Equality of residue rectangle lifted representable maps reflects equality of compact morphisms. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_eq_of_representableObjectMap_eq
    (R : ℝ)
    {left right :
      (completedZetaZeroPoleResidueRectangleSourceGenerator R) ⟶
        completedZetaZeroPoleResidueRectangleTargetGenerator}
    (map_eq :
      left.representableObjectMap =
        right.representableObjectMap) :
    left = right :=
  Eq.trans
    (Eq.symm
      (TraceAnalyticGeometricGenerator.yonedaPreimage_representableObjectMap
        left))
    (Eq.trans
      (congrArg
        (fun morphism =>
          TraceAnalyticGeometricGenerator.yonedaPreimage morphism)
        map_eq)
      (TraceAnalyticGeometricGenerator.yonedaPreimage_representableObjectMap
        right))

/-- Equality of scheduled-channel lifted representable maps reflects equality of compact morphisms. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_eq_of_representableObjectMap_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    {left right :
      (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u) ⟶
        completedZetaZeroPoleChannelRectangleTargetGenerator}
    (map_eq :
      left.representableObjectMap =
        right.representableObjectMap) :
    left = right :=
  Eq.trans
    (Eq.symm
      (TraceAnalyticGeometricGenerator.yonedaPreimage_representableObjectMap
        left))
    (Eq.trans
      (congrArg
        (fun morphism =>
          TraceAnalyticGeometricGenerator.yonedaPreimage morphism)
        map_eq)
      (TraceAnalyticGeometricGenerator.yonedaPreimage_representableObjectMap
        right))

end AnalyticMotives
end LFunctions
end Boundary
