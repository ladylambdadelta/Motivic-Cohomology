import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Objects.IsoBounded.IsoClosure.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.IsoBounded.Owner

/-!
# Iso-closure of bounded degree objects in iso-bounded complexes

Degreewise iso-bounded complexes have each degree object in the iso-closure of
the concrete bounded additive objects.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticAdditiveCochainComplex

/-- A cochain complex is degreewise in the iso-closure of concrete bounded
additive-envelope objects. -/
def DegreewiseIsoClosureBoundedBy
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bound : Nat) :
    Prop :=
  (degree : ℤ) →
    CategoryTheory.isoClosure
      (TraceAnalyticAdditiveObject.boundedObjectRepresentative bound)
      (complex.objectAt degree)

/-- A degree object of a degreewise iso-bounded complex belongs to the
iso-closure of concrete bounded additive objects. -/
theorem DegreewiseIsoBoundedBy.degreeObject_mem_isoClosure_boundedObject
    {complex : TraceAnalyticAdditiveCochainComplex}
    {bound : Nat}
    (isoBounded :
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy
        complex
        bound)
    (degree : ℤ) :
    CategoryTheory.isoClosure
      (TraceAnalyticAdditiveObject.boundedObjectRepresentative bound)
      (complex.objectAt degree) :=
  (isoBounded.degreeObject degree)
    .mem_isoClosure_boundedObjectRepresentative

/-- A degreewise iso-bounded complex is degreewise in the iso-closure of
concrete bounded additive objects. -/
theorem DegreewiseIsoBoundedBy.degreewiseIsoClosureBoundedBy
    {complex : TraceAnalyticAdditiveCochainComplex}
    {bound : Nat}
    (isoBounded :
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy
        complex
        bound) :
    TraceAnalyticAdditiveCochainComplex.DegreewiseIsoClosureBoundedBy
      complex
      bound :=
  fun degree =>
    isoBounded.degreeObject_mem_isoClosure_boundedObject degree

end TraceAnalyticAdditiveCochainComplex

end AnalyticMotives
end LFunctions
end Boundary
