import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Stabilization.BoundedCones.Rotation.Owner

/-!
# Motive-root bounded cone facade

This file exposes bounded analytic mapping-cone packages through the
motive-root stabilization namespace.  These are the concrete bounded cone
triangles and short complexes used by the weight-triangular comparison lane.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Motive-root facade: a bounded analytic map has a full iso-bounded mapping-cone package. -/
def TraceAnalyticMotive.rootStabilization_boundedConePackage
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
      bound :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded
    hom

/-- Motive-root facade: the bounded analytic cone package is distinguished. -/
theorem TraceAnalyticMotive.rootStabilization_boundedConePackage_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticMotive.rootStabilization_boundedConePackage
      hom).trianglePackage.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  (TraceAnalyticMotive.rootStabilization_boundedConePackage
    hom).trianglePackage.triangle_distinguished

/-- Motive-root facade: shifted bounded maps have full iso-bounded cone packages. -/
def TraceAnalyticMotive.rootStabilization_shiftedBoundedConePackage
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
      bound :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage
    hom
    shift

/-- Motive-root facade: shifted bounded cone packages are distinguished. -/
theorem TraceAnalyticMotive.rootStabilization_shiftedBoundedConePackage_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticMotive.rootStabilization_shiftedBoundedConePackage
      hom
      shift).trianglePackage.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_distinguished
    hom
    shift

/-- Motive-root facade: the shifted bounded cone short complex has zero composite. -/
theorem TraceAnalyticMotive.rootStabilization_shiftedBoundedConeShortComplex_zero
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex
      hom
      shift).f ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex
          hom
          shift).g =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex_zero
    hom
    shift

end AnalyticMotives
end LFunctions
end Boundary
