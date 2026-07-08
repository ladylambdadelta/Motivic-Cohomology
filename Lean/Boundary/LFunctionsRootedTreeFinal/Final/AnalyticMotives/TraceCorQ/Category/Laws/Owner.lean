import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Identity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Associativity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Identity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.NamedCoherence.Owner

/-!
# Category laws for typed trace correspondences

This file owns the category-law wrappers after typed homs, identities, and
composition have been constructed.

Associativity is inherited from the quotient theorem.  Identity laws are
inherited from the singleton identity-support theorems after the typed hom
layer records common source and target data.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The laws root exposes left identity for typed trace correspondences. -/
theorem TraceCorQCategoryLaws.left_id
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.comp (TraceCorQHom.id source) hom =
      hom :=
  TraceCorQHom.left_id
    hom

/-- The laws root exposes right identity for typed trace correspondences. -/
theorem TraceCorQCategoryLaws.right_id
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.comp hom (TraceCorQHom.id target) =
      hom :=
  TraceCorQHom.right_id
    hom

/-- The laws root exposes associativity for typed trace correspondences. -/
theorem TraceCorQCategoryLaws.assoc
    {first second third fourth : TraceCorQObject}
    (left : TraceCorQHom first second)
    (middle : TraceCorQHom second third)
    (right : TraceCorQHom third fourth) :
    TraceCorQHom.comp (TraceCorQHom.comp left middle) right =
      TraceCorQHom.comp left (TraceCorQHom.comp middle right) :=
  TraceCorQHom.comp_assoc
    left
    middle
    right

/-- The laws root exposes left additivity of composition. -/
theorem TraceCorQCategoryLaws.add_comp
    {source middle target : TraceCorQObject}
    (left right : TraceCorQHom source middle)
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp (TraceCorQHom.add left right) tail =
      TraceCorQHom.add
        (TraceCorQHom.comp left tail)
        (TraceCorQHom.comp right tail) :=
  TraceCorQHom.add_comp
    left
    right
    tail

/-- The laws root exposes right additivity of composition. -/
theorem TraceCorQCategoryLaws.comp_add
    {source middle target : TraceCorQObject}
    (head : TraceCorQHom source middle)
    (left right : TraceCorQHom middle target) :
    TraceCorQHom.comp head (TraceCorQHom.add left right) =
      TraceCorQHom.add
        (TraceCorQHom.comp head left)
        (TraceCorQHom.comp head right) :=
  TraceCorQHom.comp_add
    head
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
