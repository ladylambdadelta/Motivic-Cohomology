import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Laws.Full.Owner

/-!
# Derived additive laws for typed trace-correspondence homs

This aggregate owns additive laws downstream from the base additive unit,
associativity, and commutativity theorems.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Derived typed-hom additive aggregate: zero is a left additive identity. -/
theorem TraceCorQHom.add_lawsDerived_zero_add
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.add
      (TraceCorQHom.zero source target)
      hom =
      hom :=
  TraceCorQHom.zero_add
    hom

/-- Derived typed-hom additive aggregate: zero is a right additive identity. -/
theorem TraceCorQHom.add_lawsDerived_add_zero
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.add
      hom
      (TraceCorQHom.zero source target) =
      hom :=
  TraceCorQHom.add_zero
    hom

/-- Derived typed-hom additive aggregate: typed hom addition is associative. -/
theorem TraceCorQHom.add_lawsDerived_add_assoc
    {source target : TraceCorQObject}
    (first second third : TraceCorQHom source target) :
    TraceCorQHom.add
      (TraceCorQHom.add first second)
      third =
      TraceCorQHom.add
        first
        (TraceCorQHom.add second third) :=
  TraceCorQHom.add_assoc
    first
    second
    third

/-- Derived typed-hom additive aggregate: typed hom addition is commutative. -/
theorem TraceCorQHom.add_lawsDerived_add_comm
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    TraceCorQHom.add left right =
      TraceCorQHom.add right left :=
  TraceCorQHom.add_comm
    left
    right

/-- Derived typed-hom additive aggregate: four summands can swap their middle terms. -/
theorem TraceCorQHom.add_lawsDerived_add_add_add_comm
    {source target : TraceCorQObject}
    (first second third fourth : TraceCorQHom source target) :
    TraceCorQHom.add
      (TraceCorQHom.add first second)
      (TraceCorQHom.add third fourth) =
      TraceCorQHom.add
        (TraceCorQHom.add first third)
        (TraceCorQHom.add second fourth) :=
  TraceCorQHom.add_add_add_comm
    first
    second
    third
    fourth

/-- Derived typed-hom additive aggregate: fully left-associated fourfold sums normalize. -/
theorem TraceCorQHom.add_lawsDerived_add_assoc_four_left
    {source target : TraceCorQObject}
    (first second third fourth : TraceCorQHom source target) :
    TraceCorQHom.add
      (TraceCorQHom.add
        (TraceCorQHom.add first second)
        third)
      fourth =
      TraceCorQHom.add
        first
        (TraceCorQHom.add
          second
          (TraceCorQHom.add third fourth)) :=
  TraceCorQHom.add_assoc_four_left
    first
    second
    third
    fourth

/-- Derived typed-hom additive aggregate: binary-split fourfold sums normalize. -/
theorem TraceCorQHom.add_lawsDerived_add_assoc_four_binary
    {source target : TraceCorQObject}
    (first second third fourth : TraceCorQHom source target) :
    TraceCorQHom.add
      (TraceCorQHom.add first second)
      (TraceCorQHom.add third fourth) =
      TraceCorQHom.add
        first
        (TraceCorQHom.add
          second
          (TraceCorQHom.add third fourth)) :=
  TraceCorQHom.add_assoc_four_binary
    first
    second
    third
    fourth

end AnalyticMotives
end LFunctions
end Boundary
