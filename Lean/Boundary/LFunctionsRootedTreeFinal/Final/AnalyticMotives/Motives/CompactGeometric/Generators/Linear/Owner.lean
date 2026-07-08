import Mathlib.CategoryTheory.Linear.Basic
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Category.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Linear.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Neg.Laws.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Laws.Derived.Owner

/-!
# Linear structure on compact geometric analytic generators

This file packages the inherited preadditive and rational-linear structure on
the category of compact analytic generators.  The hom algebra and bilinearity
are inherited from the underlying `TraceCorQ` homs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Compact analytic generator homs inherit their additive group from trace correspondences. -/
instance traceAnalyticGeometricGeneratorHomAddCommGroup
    {source target : TraceAnalyticGeometricGenerator} :
    AddCommGroup (source ⟶ target) :=
  traceCorQHomAddCommGroup

/-- Compact analytic generator homs inherit their rational module from trace correspondences. -/
instance traceAnalyticGeometricGeneratorHomRatModule
    {source target : TraceAnalyticGeometricGenerator} :
    Module Rat (source ⟶ target) :=
  traceCorQHomRatModule

/-- Compact geometric analytic generators form a preadditive category. -/
instance traceAnalyticGeometricGeneratorPreadditive :
    CategoryTheory.Preadditive TraceAnalyticGeometricGenerator where
  homGroup := fun source target =>
    traceAnalyticGeometricGeneratorHomAddCommGroup
  add_comp := fun source middle target left right tail =>
    TraceCorQHom.std_add_comp left right tail
  comp_add := fun source middle target left right tail =>
    TraceCorQHom.std_comp_add left right tail

/-- Compact geometric analytic generators form a rational-linear category. -/
instance traceAnalyticGeometricGeneratorLinearRat :
    CategoryTheory.Linear Rat TraceAnalyticGeometricGenerator where
  homModule := fun source target =>
    traceAnalyticGeometricGeneratorHomRatModule
  smul_comp := fun source middle target coefficient left right =>
    TraceCorQHom.std_smul_comp coefficient left right
  comp_smul := fun source middle target left coefficient right =>
    TraceCorQHom.std_comp_smul coefficient left right

/-- Addition of compact-generator morphisms is addition of underlying trace homs. -/
theorem TraceAnalyticGeometricGenerator.add_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (left right : source ⟶ target) :
    (left + right).traceHom =
      left.traceHom + right.traceHom :=
  rfl

/-- Rational scalar multiplication of compact-generator morphisms is inherited from trace homs. -/
theorem TraceAnalyticGeometricGenerator.smul_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (coefficient : Rat)
    (morphism : source ⟶ target) :
    (coefficient • morphism).traceHom =
      coefficient • morphism.traceHom :=
  rfl

/-- Zero compact-generator morphism is the zero underlying trace hom. -/
theorem TraceAnalyticGeometricGenerator.zero_traceHom
    {source target : TraceAnalyticGeometricGenerator} :
    (0 : source ⟶ target).traceHom =
      (0 : source.traceObject ⟶ target.traceObject) :=
  rfl

/-- Explicit trace-hom negation of a compact-generator morphism is typed trace negation. -/
theorem TraceAnalyticGeometricGenerator.traceNeg_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    (TraceCorQHom.neg morphism).traceHom =
      TraceCorQHom.neg morphism.traceHom :=
  rfl

/-- Explicit trace-hom subtraction of compact-generator morphisms is typed trace subtraction. -/
theorem TraceAnalyticGeometricGenerator.traceSub_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (left right : source ⟶ target) :
    (TraceCorQHom.sub left right).traceHom =
      TraceCorQHom.sub left.traceHom right.traceHom :=
  rfl

/-- Explicit trace-hom subtraction of a compact-generator morphism from itself is zero. -/
theorem TraceAnalyticGeometricGenerator.traceSub_self_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceCorQHom.sub morphism morphism =
      TraceCorQHom.zero source.traceObject target.traceObject :=
  TraceCorQHom.sub_lawsDerived_sub_self
    morphism

/-- Explicit trace-hom subtraction detects equality for compact-generator morphisms. -/
theorem TraceAnalyticGeometricGenerator.eq_of_traceSub_eq_zero
    {source target : TraceAnalyticGeometricGenerator}
    (left right : source ⟶ target)
    (left_sub_right_eq_zero :
      TraceCorQHom.sub left right =
        TraceCorQHom.zero source.traceObject target.traceObject) :
    left = right :=
  TraceCorQHom.sub_lawsDerived_eq_of_sub_eq_zero
    left
    right
    left_sub_right_eq_zero

/-- Explicit trace-hom scalar multiplication distributes over compact-generator subtraction. -/
theorem TraceAnalyticGeometricGenerator.traceSmul_sub
    {source target : TraceAnalyticGeometricGenerator}
    (coefficient : Rat)
    (left right : source ⟶ target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.sub left right) =
      TraceCorQHom.sub
        (TraceCorQHom.smul coefficient left)
        (TraceCorQHom.smul coefficient right) :=
  TraceCorQHom.sub_lawsDerived_smul_sub
    coefficient
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
