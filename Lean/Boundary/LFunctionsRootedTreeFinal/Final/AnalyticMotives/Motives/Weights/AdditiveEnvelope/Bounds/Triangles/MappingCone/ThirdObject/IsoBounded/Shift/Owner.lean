import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.IsoBounded.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.ThirdObject.IsoBounded.Owner

/-!
# Shifts of iso-bounded mapping-cone third representatives

The concrete mapping-cone complex representing the third vertex remains
degreewise iso-bounded after cochain shift.  The shifted witness in degree `i`
is the original cone witness in degree `i + n`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The shifted concrete mapping-cone third complex is degreewise iso-bounded. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedThirdObjectDegreewiseIsoBounded
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy
      ((CochainComplex.shiftFunctor TraceAnalyticAdditiveCategoryObject shift).obj
        (CochainComplex.mappingCone hom))
      bound :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegreewiseIsoBounded
    hom).shift
    shift

/-- The shifted cone witness is the original cone witness in the reindexed degree. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedThirdObjectDegreewiseIsoBounded_degreeObject
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift degree : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedThirdObjectDegreewiseIsoBounded
      hom
      shift).degreeObject degree =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegreewiseIsoBounded
        hom).degreeObject
        (degree + shift) :=
  rfl

/-- The shifted cone representative is the standard cone-degree representative in degree `i + n`. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedThirdObjectDegreewiseIsoBounded_representative
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift degree : ℤ) :
    ((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedThirdObjectDegreewiseIsoBounded
      hom
      shift).degreeObject degree).boundedRepresentative =
      hom.mappingConeDegreeObject (degree + shift) :=
  rfl

/-- Shifted cone representatives satisfy the same ambient weight bound. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedThirdObjectDegreewiseIsoBounded_weightLevel_le
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift degree : ℤ) :
    ((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedThirdObjectDegreewiseIsoBounded
      hom
      shift).degreeObject degree).boundedRepresentative.object.weightLevel ≤
      bound :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegreewiseIsoBounded
    hom).degreeObject_weightLevel_le
    (degree + shift)

end AnalyticMotives
end LFunctions
end Boundary
