import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.FullPackage.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.ShortComplex.Owner

/-!
# Comparison with the shifted-map short complex

The shifted full-package short complex and the earlier shifted-map short
complex are the same concrete short complex: the full bounded mapping-cone
short complex of the shifted bounded map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The shifted full-package short complex agrees with the shifted-map short complex. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex_eq_shiftedShortComplex
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex
        hom
        shift =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedShortComplex
        hom
        shift :=
  rfl

/-- The shifted-map short complex agrees with the shifted full-package short complex. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedShortComplex_eq_shiftedFullPackage_shortComplex
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedShortComplex
        hom
        shift =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex
        hom
        shift :=
  Eq.symm
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex_eq_shiftedShortComplex
      hom
      shift)

end AnalyticMotives
end LFunctions
end Boundary
