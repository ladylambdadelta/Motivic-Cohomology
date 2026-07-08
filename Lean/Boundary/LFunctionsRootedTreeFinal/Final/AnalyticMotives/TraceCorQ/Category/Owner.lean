import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Owner

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Identity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Composition.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Instance.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Linear.Owner

/-!
# The Q-linear trace-correspondence category

This file owns the category structure on quotient trace correspondences.

Composition is induced by composition of certified trace transports and is
well-defined through the relation and coherence layers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The category root exposes the typed homs used by the category instance. -/
def TraceCorQCategory.hom
    (source target : TraceCorQObject) :=
  TraceCorQHom source target

/-- The category root exposes the identity morphism. -/
theorem TraceCorQCategory.id_eq
    (object : TraceCorQObject) :
    CategoryTheory.CategoryStruct.id object =
      TraceCorQHom.id object :=
  rfl

/-- The category root exposes composition of typed trace-correspondence homs. -/
theorem TraceCorQCategory.comp_eq
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    left.comp right =
      TraceCorQHom.comp left right :=
  rfl

/-- The category root exposes the category structure without registering a duplicate instance. -/
def TraceCorQCategory.categoryStructure :
    CategoryTheory.Category TraceCorQObject :=
  traceCorQCategory

/-- The category root exposes the preadditive structure without registering a duplicate instance. -/
def TraceCorQCategory.preadditiveStructure :
    CategoryTheory.Preadditive TraceCorQObject :=
  traceCorQPreadditive

/-- The category root exposes the rational linear structure without registering a duplicate instance. -/
def TraceCorQCategory.linearRatStructure :
    CategoryTheory.Linear Rat TraceCorQObject :=
  traceCorQLinearRat

/-- The category root exposes left identity for typed trace correspondences. -/
theorem TraceCorQCategory.left_id
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.comp (TraceCorQHom.id source) hom =
      hom :=
  TraceCorQCategoryLaws.left_id
    hom

/-- The category root exposes right identity for typed trace correspondences. -/
theorem TraceCorQCategory.right_id
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.comp hom (TraceCorQHom.id target) =
      hom :=
  TraceCorQCategoryLaws.right_id
    hom

/-- The category root exposes associativity for typed trace correspondences. -/
theorem TraceCorQCategory.assoc
    {first second third fourth : TraceCorQObject}
    (left : TraceCorQHom first second)
    (middle : TraceCorQHom second third)
    (right : TraceCorQHom third fourth) :
    TraceCorQHom.comp (TraceCorQHom.comp left middle) right =
      TraceCorQHom.comp left (TraceCorQHom.comp middle right) :=
  TraceCorQCategoryLaws.assoc
    left
    middle
    right

/-- The category root exposes zero on the left of composition. -/
theorem TraceCorQCategory.zero_comp
    {source middle target : TraceCorQObject}
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (0 : TraceCorQHom source middle)
      tail =
      (0 : TraceCorQHom source target) :=
  TraceCorQHom.std_zero_comp
    tail

/-- The category root exposes zero on the right of composition. -/
theorem TraceCorQCategory.comp_zero
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle) :
    TraceCorQHom.comp
      left
      (0 : TraceCorQHom middle target) =
      (0 : TraceCorQHom source target) :=
  TraceCorQHom.std_comp_zero
    left

/-- The category root exposes left additivity of typed composition. -/
theorem TraceCorQCategory.add_comp
    {source middle target : TraceCorQObject}
    (left right : TraceCorQHom source middle)
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp (left + right) tail =
      TraceCorQHom.comp left tail +
        TraceCorQHom.comp right tail :=
  TraceCorQHom.std_add_comp
    left
    right
    tail

/-- The category root exposes right additivity of typed composition. -/
theorem TraceCorQCategory.comp_add
    {source middle target : TraceCorQObject}
    (head : TraceCorQHom source middle)
    (left right : TraceCorQHom middle target) :
    TraceCorQHom.comp head (left + right) =
      TraceCorQHom.comp head left +
        TraceCorQHom.comp head right :=
  TraceCorQHom.std_comp_add
    head
    left
    right

/-- The category root exposes scalar compatibility on the left input. -/
theorem TraceCorQCategory.smul_comp
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp (coefficient • left) right =
      coefficient • TraceCorQHom.comp left right :=
  TraceCorQHom.std_smul_comp
    coefficient
    left
    right

/-- The category root exposes scalar compatibility on the right input. -/
theorem TraceCorQCategory.comp_smul
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp left (coefficient • right) =
      coefficient • TraceCorQHom.comp left right :=
  TraceCorQHom.std_comp_smul
    coefficient
    left
    right

/-- The category root exposes associativity coherence support cancellation. -/
theorem TraceCorQCategory.associativitySupport_eq_zero
    {source target : TraceCorQObject}
    (pathSource pathTarget : TraceRewritePath)
    (support : TraceCorQHomFormalSum source target) :
    TraceCorQHom.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.associativity
        pathSource
        pathTarget
        support.raw) =
      TraceCorQHom.zero source target :=
  TraceCorQHom.associativitySupport_eq_zero
    pathSource
    pathTarget
    support

end AnalyticMotives
end LFunctions
end Boundary
