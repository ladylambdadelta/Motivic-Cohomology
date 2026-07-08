import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.Source.Represented.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.Source.TraceObject.Homotopy.Owner

/-!
# Trace-object formulas for the comparison source endpoint

This file exposes the concrete source-side path from a certified trace object
to the analytic comparison source.  A trace object is first viewed as a
singleton additive object, then as a degree-zero cochain complex, then as a
homotopy object, and finally as an object of the stable comparison source.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The stable comparison-source object represented by one certified trace
object. -/
def TraceAnalyticMotiveComparison.sourceTraceObject
    (object : TraceCorQObject) :
    TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticMotiveComparison.sourceObjectOf
    (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject object)

/-- The endpoint trace object is the comparison-source image of the endpoint
trace homotopy object. -/
theorem TraceAnalyticMotiveComparison.sourceTraceObject_eq_sourceObjectOf
    (object : TraceCorQObject) :
    TraceAnalyticMotiveComparison.sourceTraceObject object =
      TraceAnalyticMotiveComparison.sourceObjectOf
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject object) :=
  rfl

/-- The endpoint trace object is the stable analytic quotient image of the
endpoint trace homotopy object. -/
theorem TraceAnalyticMotiveComparison.sourceTraceObject_eq_stable
    (object : TraceCorQObject) :
    TraceAnalyticMotiveComparison.sourceTraceObject object =
      TraceAnalyticStableMotiveCategory.objectOf
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject object) :=
  TraceAnalyticMotiveComparison.sourceObjectOf_eq_stable
    (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject object)

/-- The endpoint trace object is the Verdier quotient-functor image of the
endpoint trace homotopy object. -/
theorem TraceAnalyticMotiveComparison.sourceTraceObject_eq_quotientFunctor_obj
    (object : TraceCorQObject) :
    TraceAnalyticMotiveComparison.sourceTraceObject object =
      TraceAnalyticStableMotiveCategory.quotientFunctor.obj
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject object) :=
  Eq.trans
    (TraceAnalyticMotiveComparison.sourceTraceObject_eq_stable object)
    (TraceAnalyticStableMotiveCategory.objectOf_eq
      (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject object))

/-- The stable comparison-source morphism represented by one trace
correspondence. -/
def TraceAnalyticMotiveComparison.sourceTraceMap
    {source target : TraceCorQObject}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.sourceTraceObject source ⟶
      TraceAnalyticMotiveComparison.sourceTraceObject target :=
  TraceAnalyticMotiveComparison.sourceMapOf
    (TraceAnalyticMotiveComparison.sourceTraceHomotopyMap hom)

/-- The endpoint trace map is the comparison-source image of the endpoint trace
homotopy map. -/
theorem TraceAnalyticMotiveComparison.sourceTraceMap_eq_sourceMapOf
    {source target : TraceCorQObject}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.sourceTraceMap hom =
      TraceAnalyticMotiveComparison.sourceMapOf
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyMap hom) :=
  rfl

/-- The endpoint trace map is the stable analytic quotient image of the
endpoint trace homotopy map. -/
theorem TraceAnalyticMotiveComparison.sourceTraceMap_eq_stable
    {source target : TraceCorQObject}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.sourceTraceMap hom =
      TraceAnalyticStableMotiveCategory.mapOf
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyMap hom) :=
  TraceAnalyticMotiveComparison.sourceMapOf_eq_stable
    (TraceAnalyticMotiveComparison.sourceTraceHomotopyMap hom)

/-- The endpoint trace map is the Verdier quotient-functor image of the endpoint
trace homotopy map. -/
theorem TraceAnalyticMotiveComparison.sourceTraceMap_eq_quotientFunctor_map
    {source target : TraceCorQObject}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.sourceTraceMap hom =
      TraceAnalyticStableMotiveCategory.quotientFunctor.map
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyMap hom) :=
  Eq.trans
    (TraceAnalyticMotiveComparison.sourceTraceMap_eq_stable hom)
    (TraceAnalyticStableMotiveCategory.mapOf_eq
      (TraceAnalyticMotiveComparison.sourceTraceHomotopyMap hom))

/-- The comparison-source functor represented by certified trace objects. -/
def TraceAnalyticMotiveComparison.sourceTraceFunctor :
    TraceCorQObject ⥤ TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticMotiveComparison.sourceTraceHomotopyFunctor ⋙
    TraceAnalyticDMgmComparisonSource.quotientFunctor

/-- The stable comparison-source trace functor is the homotopy trace functor
followed by the stable Verdier quotient. -/
theorem TraceAnalyticMotiveComparison.sourceTraceFunctor_eq_homotopy_comp_quotient :
    TraceAnalyticMotiveComparison.sourceTraceFunctor =
      TraceAnalyticMotiveComparison.sourceTraceHomotopyFunctor ⋙
        TraceAnalyticDMgmComparisonSource.quotientFunctor :=
  rfl

/-- The stable comparison-source trace functor is the full four-stage functor:
singleton additive envelope, degree-zero complexes, additive homotopy quotient,
and stable Verdier quotient. -/
theorem TraceAnalyticMotiveComparison.sourceTraceFunctor_eq_full_composite :
    TraceAnalyticMotiveComparison.sourceTraceFunctor =
      TraceAnalyticAdditiveObject.singletonFunctor ⋙
        CochainComplex.singleFunctor TraceAnalyticAdditiveCategoryObject
          (0 : ℤ) ⋙
          TraceAnalyticAdditiveHomotopyCategory.quotientFunctor ⋙
            TraceAnalyticDMgmComparisonSource.quotientFunctor :=
  rfl

/-- Object formula for the comparison-source trace functor. -/
theorem TraceAnalyticMotiveComparison.sourceTraceFunctor_obj
    (object : TraceCorQObject) :
    TraceAnalyticMotiveComparison.sourceTraceFunctor.obj object =
      TraceAnalyticMotiveComparison.sourceTraceObject object :=
  rfl

/-- Map formula for the comparison-source trace functor. -/
theorem TraceAnalyticMotiveComparison.sourceTraceFunctor_map
    {source target : TraceCorQObject}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.sourceTraceFunctor.map hom =
      TraceAnalyticMotiveComparison.sourceTraceMap hom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
