import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.IsoBounded.IsoClosure.Owner

/-!
# Source boundedness up to degreewise iso-closure

This file exposes, under comparison-source names, the predicate that every
degree object of a complex lies in the iso-closure of concrete bounded
additive-envelope objects.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotiveComparison

/-- Comparison-source complex boundedness up to degreewise iso-closure of
bounded additive-envelope objects. -/
def sourceComplexDegreewiseIsoClosureBoundedBy
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bound : Nat) :
    Prop :=
  TraceAnalyticAdditiveCochainComplex.DegreewiseIsoClosureBoundedBy
    complex
    bound

/-- The comparison-source degreewise iso-closure boundedness predicate is the
underlying additive-envelope predicate. -/
theorem sourceComplexDegreewiseIsoClosureBoundedBy_eq
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bound : Nat) :
    TraceAnalyticMotiveComparison
        .sourceComplexDegreewiseIsoClosureBoundedBy complex bound =
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoClosureBoundedBy
        complex
        bound :=
  rfl

/-- A comparison-source literally bounded complex is degreewise bounded up to
iso-closure. -/
theorem sourceComplexDegreewiseIsoClosureBoundedBy_of_weightBounded
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticMotiveComparison
      .sourceComplexDegreewiseIsoClosureBoundedBy
        complex.complex
        bound :=
  fun degree =>
    let boundedDegree :
        TraceAnalyticAdditiveObject.boundedObjectRepresentative
          bound
          (complex.complex.objectAt degree) :=
      Exists.intro
        (complex.degreeObject degree)
        (Eq.symm
          (TraceAnalyticMotiveComparison
            .SourceComplexWeightBoundedBy.degreeObject_object
              complex
              degree))
    CategoryTheory.le_isoClosure
      (TraceAnalyticAdditiveObject.boundedObjectRepresentative bound)
      (complex.complex.objectAt degree)
      boundedDegree

end TraceAnalyticMotiveComparison

end AnalyticMotives
end LFunctions
end Boundary
