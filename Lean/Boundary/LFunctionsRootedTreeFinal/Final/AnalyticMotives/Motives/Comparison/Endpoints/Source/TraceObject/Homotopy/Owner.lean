import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.Source.TraceObject.Complex.Owner

/-!
# Homotopy trace objects at the comparison source endpoint

This file owns the third source-side passage from a certified trace object to
the comparison source: the degree-zero trace complex is projected to the
additive analytic homotopy category, and trace complex maps are projected to
homotopy maps.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The homotopy-category object represented by one certified trace object. -/
def TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
    (object : TraceCorQObject) :
    TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.objectOf
    (TraceAnalyticMotiveComparison.sourceTraceComplex object)

/-- The endpoint trace homotopy object is the homotopy image of the endpoint
trace complex. -/
theorem TraceAnalyticMotiveComparison.sourceTraceHomotopyObject_eq_objectOf
    (object : TraceCorQObject) :
    TraceAnalyticMotiveComparison.sourceTraceHomotopyObject object =
      TraceAnalyticAdditiveHomotopyCategory.objectOf
        (TraceAnalyticMotiveComparison.sourceTraceComplex object) :=
  rfl

/-- The homotopy-category morphism represented by one trace correspondence. -/
def TraceAnalyticMotiveComparison.sourceTraceHomotopyMap
    {source target : TraceCorQObject}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.sourceTraceHomotopyObject source ⟶
      TraceAnalyticMotiveComparison.sourceTraceHomotopyObject target :=
  TraceAnalyticAdditiveHomotopyCategory.mapOf
    (TraceAnalyticMotiveComparison.sourceTraceComplexMap hom)

/-- The endpoint trace homotopy map is the homotopy image of the endpoint
trace-complex map. -/
theorem TraceAnalyticMotiveComparison.sourceTraceHomotopyMap_eq_mapOf
    {source target : TraceCorQObject}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.sourceTraceHomotopyMap hom =
      TraceAnalyticAdditiveHomotopyCategory.mapOf
        (TraceAnalyticMotiveComparison.sourceTraceComplexMap hom) :=
  rfl

/-- The additive-homotopy trace functor represented by certified trace
objects. -/
def TraceAnalyticMotiveComparison.sourceTraceHomotopyFunctor :
    TraceCorQObject ⥤ TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotiveComparison.sourceTraceComplexFunctor ⋙
    TraceAnalyticAdditiveHomotopyCategory.quotientFunctor

/-- The additive-homotopy trace functor is the degree-zero trace-complex functor
followed by the additive homotopy quotient. -/
theorem TraceAnalyticMotiveComparison.sourceTraceHomotopyFunctor_eq_complex_comp_quotient :
    TraceAnalyticMotiveComparison.sourceTraceHomotopyFunctor =
      TraceAnalyticMotiveComparison.sourceTraceComplexFunctor ⋙
        TraceAnalyticAdditiveHomotopyCategory.quotientFunctor :=
  rfl

/-- Object formula for the additive-homotopy trace functor. -/
theorem TraceAnalyticMotiveComparison.sourceTraceHomotopyFunctor_obj
    (object : TraceCorQObject) :
    TraceAnalyticMotiveComparison.sourceTraceHomotopyFunctor.obj object =
      TraceAnalyticMotiveComparison.sourceTraceHomotopyObject object :=
  rfl

/-- Map formula for the additive-homotopy trace functor. -/
theorem TraceAnalyticMotiveComparison.sourceTraceHomotopyFunctor_map
    {source target : TraceCorQObject}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.sourceTraceHomotopyFunctor.map hom =
      TraceAnalyticMotiveComparison.sourceTraceHomotopyMap hom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
