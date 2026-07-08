import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.FunctorBridges.CategoryCompatibility.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.FunctorBridges.ForgetfulReflection.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.FunctorBridges.YonedaReflection.Owner

/-!
# Functor bridges for completed-zeta finite-rectangle compact adapters

This directory collects concrete functorial consequences for the completed-zeta
finite-rectangle compact-generator adapters.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The residue adapter bridge preserves representable maps under composition. -/
theorem completedZetaFiniteRectangleFunctorBridge_residue_comp_representableMap
    (R : ℝ)
    {middle : TraceAnalyticGeometricGenerator}
    (left :
      (completedZetaZeroPoleResidueRectangleSourceGenerator R) ⟶ middle)
    (right :
      middle ⟶ completedZetaZeroPoleResidueRectangleTargetGenerator) :
    (left ≫ right).representableMap =
      left.representableMap ≫ right.representableMap :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_comp_representableMap
    R
    left
    right

/-- The residue adapter bridge reflects equality through the forgetful functor. -/
theorem completedZetaFiniteRectangleFunctorBridge_residue_eq_of_forgetfulFunctor_map_eq
    (R : ℝ)
    {left right :
      (completedZetaZeroPoleResidueRectangleSourceGenerator R) ⟶
        completedZetaZeroPoleResidueRectangleTargetGenerator}
    (map_eq :
      TraceAnalyticGeometricGenerator.forgetfulFunctor.map left =
        TraceAnalyticGeometricGenerator.forgetfulFunctor.map right) :
    left = right :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_eq_of_forgetfulFunctor_map_eq
    R
    map_eq

/-- The residue adapter bridge reflects equality through lifted representable maps. -/
theorem completedZetaFiniteRectangleFunctorBridge_residue_eq_of_representableObjectMap_eq
    (R : ℝ)
    {left right :
      (completedZetaZeroPoleResidueRectangleSourceGenerator R) ⟶
        completedZetaZeroPoleResidueRectangleTargetGenerator}
    (map_eq :
      left.representableObjectMap =
        right.representableObjectMap) :
    left = right :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_eq_of_representableObjectMap_eq
    R
    map_eq

/-- The scheduled-channel adapter bridge preserves representable maps under composition. -/
theorem completedZetaFiniteRectangleFunctorBridge_channel_comp_representableMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    {middle : TraceAnalyticGeometricGenerator}
    (left :
      (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u) ⟶ middle)
    (right :
      middle ⟶ completedZetaZeroPoleChannelRectangleTargetGenerator) :
    (left ≫ right).representableMap =
      left.representableMap ≫ right.representableMap :=
  completedZetaZeroPoleChannelRectangleGeneratorHom_comp_representableMap
    f
    F
    h
    u
    left
    right

/-- The scheduled-channel adapter bridge reflects equality through the forgetful functor. -/
theorem completedZetaFiniteRectangleFunctorBridge_channel_eq_of_forgetfulFunctor_map_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    {left right :
      (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u) ⟶
        completedZetaZeroPoleChannelRectangleTargetGenerator}
    (map_eq :
      TraceAnalyticGeometricGenerator.forgetfulFunctor.map left =
        TraceAnalyticGeometricGenerator.forgetfulFunctor.map right) :
    left = right :=
  completedZetaZeroPoleChannelRectangleGeneratorHom_eq_of_forgetfulFunctor_map_eq
    f
    F
    h
    u
    map_eq

/-- The scheduled-channel adapter bridge reflects equality through lifted representable maps. -/
theorem completedZetaFiniteRectangleFunctorBridge_channel_eq_of_representableObjectMap_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    {left right :
      (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u) ⟶
        completedZetaZeroPoleChannelRectangleTargetGenerator}
    (map_eq :
      left.representableObjectMap =
        right.representableObjectMap) :
    left = right :=
  completedZetaZeroPoleChannelRectangleGeneratorHom_eq_of_representableObjectMap_eq
    f
    F
    h
    u
    map_eq

end AnalyticMotives
end LFunctions
end Boundary
