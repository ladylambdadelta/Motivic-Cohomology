import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.Quasicategory.Simplices.Owner

/-!
# Identity simplices in the analytic stable motive quasicategory

This owner file records the unit data visible in the nerve presentation of
analytic stable motives.  Identity one-simplices and left/right unit
two-simplices are concrete composable-arrow objects in the analytic stable
motive category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The identity one-simplex at an analytic stable motive object. -/
def TraceAnalyticStableMotiveQuasicategory.identityOneSimplex
    (object : TraceAnalyticStableMotiveCategory) :
    TraceAnalyticStableMotiveQuasicategory.obj
      (Opposite.op (SimplexCategory.mk 1)) :=
  ComposableArrows.mk₁ (𝟙 object)

/-- The edge of the identity one-simplex is the identity morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.identityOneSimplex_edge
    (object : TraceAnalyticStableMotiveCategory) :
    (TraceAnalyticStableMotiveQuasicategory
      .identityOneSimplex object).map' 0 1 =
      𝟙 object :=
  rfl

/-- The left-unit two-simplex attached to a morphism. -/
def TraceAnalyticStableMotiveQuasicategory.leftUnitTwoSimplex
    {source target : TraceAnalyticStableMotiveCategory}
    (morphism : source ⟶ target) :
    TraceAnalyticStableMotiveQuasicategory.obj
      (Opposite.op (SimplexCategory.mk 2)) :=
  ComposableArrows.mk₂ (𝟙 source) morphism

/-- The right-unit two-simplex attached to a morphism. -/
def TraceAnalyticStableMotiveQuasicategory.rightUnitTwoSimplex
    {source target : TraceAnalyticStableMotiveCategory}
    (morphism : source ⟶ target) :
    TraceAnalyticStableMotiveQuasicategory.obj
      (Opposite.op (SimplexCategory.mk 2)) :=
  ComposableArrows.mk₂ morphism (𝟙 target)

/-- The first edge of the left-unit two-simplex is the identity. -/
theorem TraceAnalyticStableMotiveQuasicategory.leftUnitTwoSimplex_firstEdge
    {source target : TraceAnalyticStableMotiveCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .leftUnitTwoSimplex morphism).map' 0 1 =
      𝟙 source :=
  rfl

/-- The second edge of the left-unit two-simplex is the original morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.leftUnitTwoSimplex_secondEdge
    {source target : TraceAnalyticStableMotiveCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .leftUnitTwoSimplex morphism).map' 1 2 =
      morphism :=
  rfl

/-- The first edge of the right-unit two-simplex is the original morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.rightUnitTwoSimplex_firstEdge
    {source target : TraceAnalyticStableMotiveCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .rightUnitTwoSimplex morphism).map' 0 1 =
      morphism :=
  rfl

/-- The second edge of the right-unit two-simplex is the identity. -/
theorem TraceAnalyticStableMotiveQuasicategory.rightUnitTwoSimplex_secondEdge
    {source target : TraceAnalyticStableMotiveCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .rightUnitTwoSimplex morphism).map' 1 2 =
      𝟙 target :=
  rfl

/-- The composite edge of the left-unit two-simplex is the original
morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.leftUnitTwoSimplex_composite
    {source target : TraceAnalyticStableMotiveCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .leftUnitTwoSimplex morphism).map' 0 2 =
      morphism :=
  Eq.trans
    (ComposableArrows.map'_comp
      (TraceAnalyticStableMotiveQuasicategory
        .leftUnitTwoSimplex morphism)
      0
      1
      2)
    (Eq.trans
      (congrArg
        (fun edge =>
          edge ≫
            (TraceAnalyticStableMotiveQuasicategory
              .leftUnitTwoSimplex morphism).map' 1 2)
        (TraceAnalyticStableMotiveQuasicategory
          .leftUnitTwoSimplex_firstEdge morphism))
      (Eq.trans
        (Category.id_comp
          ((TraceAnalyticStableMotiveQuasicategory
            .leftUnitTwoSimplex morphism).map' 1 2))
        (TraceAnalyticStableMotiveQuasicategory
          .leftUnitTwoSimplex_secondEdge morphism)))

/-- The composite edge of the right-unit two-simplex is the original
morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.rightUnitTwoSimplex_composite
    {source target : TraceAnalyticStableMotiveCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .rightUnitTwoSimplex morphism).map' 0 2 =
      morphism :=
  Eq.trans
    (ComposableArrows.map'_comp
      (TraceAnalyticStableMotiveQuasicategory
        .rightUnitTwoSimplex morphism)
      0
      1
      2)
    (Eq.trans
      (congrArg
        (fun edge =>
          (TraceAnalyticStableMotiveQuasicategory
            .rightUnitTwoSimplex morphism).map' 0 1 ≫
            edge)
        (TraceAnalyticStableMotiveQuasicategory
          .rightUnitTwoSimplex_secondEdge morphism))
      (Eq.trans
        (Category.comp_id
          ((TraceAnalyticStableMotiveQuasicategory
            .rightUnitTwoSimplex morphism).map' 0 1))
        (TraceAnalyticStableMotiveQuasicategory
          .rightUnitTwoSimplex_firstEdge morphism)))

end AnalyticMotives
end LFunctions
end Boundary
