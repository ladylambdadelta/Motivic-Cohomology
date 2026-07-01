import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Presheaves.Representables.Subcategory.Owner

/-!
# Q-linear structure on trace presheaves

This file owns the inherited additive and Q-linear categorical structure on
trace presheaves and on the full subcategory of representable trace presheaves.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Trace presheaves are preadditive pointwise in Q-modules. -/
instance TraceCorQPresheaf.preadditive :
    CategoryTheory.Preadditive TraceCorQPresheaf :=
  inferInstance

/-- Trace presheaves are Q-linear pointwise in Q-modules. -/
instance TraceCorQPresheaf.linearRat :
    CategoryTheory.Linear Rat TraceCorQPresheaf :=
  inferInstance

/-- Evaluation of trace presheaves is additive. -/
instance TraceCorQPresheaf.evaluationAdditive
    (object : TraceCorQObject) :
    (TraceCorQPresheaf.evaluation object).Additive where
  map_add := fun {source target} {left right} => rfl

/-- Evaluation of trace presheaves is Q-linear. -/
instance TraceCorQPresheaf.evaluationLinearRat
    (object : TraceCorQObject) :
    (TraceCorQPresheaf.evaluation object).Linear Rat where
  map_smul := fun {source target} morphism coefficient => rfl

/-- Representable trace presheaves inherit preadditivity from the ambient presheaf category. -/
instance TraceCorQRepresentablePresheaf.preadditive :
    CategoryTheory.Preadditive TraceCorQRepresentablePresheaf :=
  inferInstance

/-- Representable trace presheaves inherit Q-linearity from the ambient presheaf category. -/
instance TraceCorQRepresentablePresheaf.linearRat :
    CategoryTheory.Linear Rat TraceCorQRepresentablePresheaf :=
  inferInstance

/-- The inclusion of representable trace presheaves is additive. -/
instance TraceCorQRepresentablePresheaf.inclusionAdditive :
    TraceCorQRepresentablePresheaf.inclusion.Additive where
  map_add := fun {source target} {left right} => rfl

/-- The inclusion of representable trace presheaves is Q-linear. -/
instance TraceCorQRepresentablePresheaf.inclusionLinearRat :
    TraceCorQRepresentablePresheaf.inclusion.Linear Rat where
  map_smul := fun {source target} morphism coefficient => rfl

/-- Inclusion preserves addition of representable-presheaf morphisms. -/
theorem TraceCorQRepresentablePresheaf.inclusion_map_add
    {source target : TraceCorQRepresentablePresheaf}
    (left right : source ⟶ target) :
    TraceCorQRepresentablePresheaf.inclusion.map (left + right) =
      TraceCorQRepresentablePresheaf.inclusion.map left +
        TraceCorQRepresentablePresheaf.inclusion.map right :=
  rfl

/-- Inclusion preserves rational scalar multiplication of representable-presheaf morphisms. -/
theorem TraceCorQRepresentablePresheaf.inclusion_map_smul
    {source target : TraceCorQRepresentablePresheaf}
    (coefficient : Rat)
    (morphism : source ⟶ target) :
    TraceCorQRepresentablePresheaf.inclusion.map (coefficient • morphism) =
      coefficient • TraceCorQRepresentablePresheaf.inclusion.map morphism :=
  rfl

/-- Evaluation maps addition of presheaf morphisms to addition on section maps. -/
theorem TraceCorQPresheaf.evaluation_map_add
    (object : TraceCorQObject)
    {source target : TraceCorQPresheaf}
    (left right : source ⟶ target) :
    (TraceCorQPresheaf.evaluation object).map (left + right) =
      (TraceCorQPresheaf.evaluation object).map left +
        (TraceCorQPresheaf.evaluation object).map right :=
  rfl

/-- Evaluation maps rational scalar multiplication to scalar multiplication on section maps. -/
theorem TraceCorQPresheaf.evaluation_map_smul
    (object : TraceCorQObject)
    {source target : TraceCorQPresheaf}
    (coefficient : Rat)
    (morphism : source ⟶ target) :
    (TraceCorQPresheaf.evaluation object).map (coefficient • morphism) =
      coefficient • (TraceCorQPresheaf.evaluation object).map morphism :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
