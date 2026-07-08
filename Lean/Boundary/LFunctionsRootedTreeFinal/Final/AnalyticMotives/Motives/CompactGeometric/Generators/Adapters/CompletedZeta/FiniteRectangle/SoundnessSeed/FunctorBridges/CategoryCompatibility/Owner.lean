import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ChannelRectangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ResidueRectangle.Owner

/-!
# Category compatibility for completed-zeta finite-rectangle compact adapters

This file specializes compact-generator identity and composition facts to the
completed-zeta finite-rectangle adapter endpoints.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The residue-rectangle source identity maps to the identity representable map. -/
theorem completedZetaZeroPoleResidueRectangleSourceGenerator_id_representableMap
    (R : ℝ) :
    (𝟙 (completedZetaZeroPoleResidueRectangleSourceGenerator R) :
        (completedZetaZeroPoleResidueRectangleSourceGenerator R) ⟶
          (completedZetaZeroPoleResidueRectangleSourceGenerator R)).representableMap =
      𝟙 (completedZetaZeroPoleResidueRectangleSourceGenerator R).presheaf :=
  TraceAnalyticGeometricGenerator.id_representableMap
    (completedZetaZeroPoleResidueRectangleSourceGenerator R)

/-- The residue-rectangle target identity maps to the identity representable map. -/
theorem completedZetaZeroPoleResidueRectangleTargetGenerator_id_representableMap :
    (𝟙 completedZetaZeroPoleResidueRectangleTargetGenerator :
        completedZetaZeroPoleResidueRectangleTargetGenerator ⟶
          completedZetaZeroPoleResidueRectangleTargetGenerator).representableMap =
      𝟙 completedZetaZeroPoleResidueRectangleTargetGenerator.presheaf :=
  TraceAnalyticGeometricGenerator.id_representableMap
    completedZetaZeroPoleResidueRectangleTargetGenerator

/-- Residue-rectangle compact morphism composition is preserved by representable maps. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_comp_representableMap
    (R : ℝ)
    {middle : TraceAnalyticGeometricGenerator}
    (left :
      (completedZetaZeroPoleResidueRectangleSourceGenerator R) ⟶ middle)
    (right :
      middle ⟶ completedZetaZeroPoleResidueRectangleTargetGenerator) :
    (left ≫ right).representableMap =
      left.representableMap ≫ right.representableMap :=
  TraceAnalyticGeometricGenerator.comp_representableMap
    left
    right

/-- Residue-rectangle compact morphism composition is preserved by the forgetful functor. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_forgetfulFunctor_map_comp
    (R : ℝ)
    {middle : TraceAnalyticGeometricGenerator}
    (left :
      (completedZetaZeroPoleResidueRectangleSourceGenerator R) ⟶ middle)
    (right :
      middle ⟶ completedZetaZeroPoleResidueRectangleTargetGenerator) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.map (left ≫ right) =
      left.traceHom ≫ right.traceHom :=
  TraceAnalyticGeometricGenerator.forgetfulFunctor_map_comp
    left
    right

/-- The scheduled-channel source identity maps to the identity representable map. -/
theorem completedZetaZeroPoleChannelRectangleSourceGenerator_id_representableMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (𝟙 (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u) :
        (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u) ⟶
          (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u)).representableMap =
      𝟙 (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).presheaf :=
  TraceAnalyticGeometricGenerator.id_representableMap
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u)

/-- The scheduled-channel target identity maps to the identity representable map. -/
theorem completedZetaZeroPoleChannelRectangleTargetGenerator_id_representableMap :
    (𝟙 completedZetaZeroPoleChannelRectangleTargetGenerator :
        completedZetaZeroPoleChannelRectangleTargetGenerator ⟶
          completedZetaZeroPoleChannelRectangleTargetGenerator).representableMap =
      𝟙 completedZetaZeroPoleChannelRectangleTargetGenerator.presheaf :=
  TraceAnalyticGeometricGenerator.id_representableMap
    completedZetaZeroPoleChannelRectangleTargetGenerator

/-- Scheduled-channel compact morphism composition is preserved by representable maps. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_comp_representableMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    {middle : TraceAnalyticGeometricGenerator}
    (left :
      (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u) ⟶ middle)
    (right :
      middle ⟶ completedZetaZeroPoleChannelRectangleTargetGenerator) :
    (left ≫ right).representableMap =
      left.representableMap ≫ right.representableMap :=
  TraceAnalyticGeometricGenerator.comp_representableMap
    left
    right

/-- Scheduled-channel compact morphism composition is preserved by the forgetful functor. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_forgetfulFunctor_map_comp
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    {middle : TraceAnalyticGeometricGenerator}
    (left :
      (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u) ⟶ middle)
    (right :
      middle ⟶ completedZetaZeroPoleChannelRectangleTargetGenerator) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.map (left ≫ right) =
      left.traceHom ≫ right.traceHom :=
  TraceAnalyticGeometricGenerator.forgetfulFunctor_map_comp
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
