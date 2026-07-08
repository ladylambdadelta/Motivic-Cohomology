import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Laws.Full.Owner

/-!
# Longer additive distribution for typed composition

This file owns normal forms for composing three- and four-summand typed hom
sums on either side.  The target normal form is fully right-associated.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Compose a left-associated three-summand source sum on the right. -/
theorem TraceCorQHom.add_add_comp
    {source middle target : TraceCorQObject}
    (first second third : TraceCorQHom source middle)
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.add
        (TraceCorQHom.add first second)
        third)
      tail =
      TraceCorQHom.add
        (TraceCorQHom.comp first tail)
        (TraceCorQHom.add
          (TraceCorQHom.comp second tail)
          (TraceCorQHom.comp third tail)) :=
  Eq.trans
    (TraceCorQHom.add_comp
      (TraceCorQHom.add first second)
      third
      tail)
    (Eq.trans
      (congrArg
        (fun head =>
          TraceCorQHom.add head (TraceCorQHom.comp third tail))
        (TraceCorQHom.add_comp first second tail))
      (TraceCorQHom.add_assoc
        (TraceCorQHom.comp first tail)
        (TraceCorQHom.comp second tail)
        (TraceCorQHom.comp third tail)))

/-- Compose a right-associated three-summand source sum on the right. -/
theorem TraceCorQHom.add_add_comp_right
    {source middle target : TraceCorQObject}
    (first second third : TraceCorQHom source middle)
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.add
        first
        (TraceCorQHom.add second third))
      tail =
      TraceCorQHom.add
        (TraceCorQHom.comp first tail)
        (TraceCorQHom.add
          (TraceCorQHom.comp second tail)
          (TraceCorQHom.comp third tail)) :=
  Eq.trans
    (TraceCorQHom.add_comp
      first
      (TraceCorQHom.add second third)
      tail)
    (congrArg
      (TraceCorQHom.add (TraceCorQHom.comp first tail))
      (TraceCorQHom.add_comp second third tail))

/-- Compose a fully left-associated four-summand source sum on the right. -/
theorem TraceCorQHom.add_add_add_comp
    {source middle target : TraceCorQObject}
    (first second third fourth : TraceCorQHom source middle)
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.add
        (TraceCorQHom.add
          (TraceCorQHom.add first second)
          third)
        fourth)
      tail =
      TraceCorQHom.add
        (TraceCorQHom.comp first tail)
        (TraceCorQHom.add
          (TraceCorQHom.comp second tail)
          (TraceCorQHom.add
            (TraceCorQHom.comp third tail)
            (TraceCorQHom.comp fourth tail))) :=
  Eq.trans
    (TraceCorQHom.add_comp
      (TraceCorQHom.add
        (TraceCorQHom.add first second)
        third)
      fourth
      tail)
    (Eq.trans
      (congrArg
        (fun head =>
          TraceCorQHom.add head (TraceCorQHom.comp fourth tail))
        (TraceCorQHom.add_add_comp first second third tail))
      (TraceCorQHom.add_assoc_four_middle_left
        (TraceCorQHom.comp first tail)
        (TraceCorQHom.comp second tail)
        (TraceCorQHom.comp third tail)
        (TraceCorQHom.comp fourth tail)))

/-- Compose a fully right-associated four-summand source sum on the right. -/
theorem TraceCorQHom.add_add_add_comp_right
    {source middle target : TraceCorQObject}
    (first second third fourth : TraceCorQHom source middle)
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.add
        first
        (TraceCorQHom.add
          second
          (TraceCorQHom.add third fourth)))
      tail =
      TraceCorQHom.add
        (TraceCorQHom.comp first tail)
        (TraceCorQHom.add
          (TraceCorQHom.comp second tail)
          (TraceCorQHom.add
            (TraceCorQHom.comp third tail)
            (TraceCorQHom.comp fourth tail))) :=
  Eq.trans
    (TraceCorQHom.add_comp
      first
      (TraceCorQHom.add
        second
        (TraceCorQHom.add third fourth))
      tail)
    (congrArg
      (TraceCorQHom.add (TraceCorQHom.comp first tail))
      (TraceCorQHom.add_add_comp_right second third fourth tail))

/-- Compose on a left-associated three-summand target sum. -/
theorem TraceCorQHom.comp_add_add
    {source middle target : TraceCorQObject}
    (head : TraceCorQHom source middle)
    (first second third : TraceCorQHom middle target) :
    TraceCorQHom.comp
      head
      (TraceCorQHom.add
        (TraceCorQHom.add first second)
        third) =
      TraceCorQHom.add
        (TraceCorQHom.comp head first)
        (TraceCorQHom.add
          (TraceCorQHom.comp head second)
          (TraceCorQHom.comp head third)) :=
  Eq.trans
    (TraceCorQHom.comp_add
      head
      (TraceCorQHom.add first second)
      third)
    (Eq.trans
      (congrArg
        (fun headClass =>
          TraceCorQHom.add headClass (TraceCorQHom.comp head third))
        (TraceCorQHom.comp_add head first second))
      (TraceCorQHom.add_assoc
        (TraceCorQHom.comp head first)
        (TraceCorQHom.comp head second)
        (TraceCorQHom.comp head third)))

/-- Compose on a right-associated three-summand target sum. -/
theorem TraceCorQHom.comp_add_add_right
    {source middle target : TraceCorQObject}
    (head : TraceCorQHom source middle)
    (first second third : TraceCorQHom middle target) :
    TraceCorQHom.comp
      head
      (TraceCorQHom.add
        first
        (TraceCorQHom.add second third)) =
      TraceCorQHom.add
        (TraceCorQHom.comp head first)
        (TraceCorQHom.add
          (TraceCorQHom.comp head second)
          (TraceCorQHom.comp head third)) :=
  Eq.trans
    (TraceCorQHom.comp_add
      head
      first
      (TraceCorQHom.add second third))
    (congrArg
      (TraceCorQHom.add (TraceCorQHom.comp head first))
      (TraceCorQHom.comp_add head second third))

/-- Compose on a fully left-associated four-summand target sum. -/
theorem TraceCorQHom.comp_add_add_add
    {source middle target : TraceCorQObject}
    (head : TraceCorQHom source middle)
    (first second third fourth : TraceCorQHom middle target) :
    TraceCorQHom.comp
      head
      (TraceCorQHom.add
        (TraceCorQHom.add
          (TraceCorQHom.add first second)
          third)
        fourth) =
      TraceCorQHom.add
        (TraceCorQHom.comp head first)
        (TraceCorQHom.add
          (TraceCorQHom.comp head second)
          (TraceCorQHom.add
            (TraceCorQHom.comp head third)
            (TraceCorQHom.comp head fourth))) :=
  Eq.trans
    (TraceCorQHom.comp_add
      head
      (TraceCorQHom.add
        (TraceCorQHom.add first second)
        third)
      fourth)
    (Eq.trans
      (congrArg
        (fun headClass =>
          TraceCorQHom.add headClass (TraceCorQHom.comp head fourth))
        (TraceCorQHom.comp_add_add head first second third))
      (TraceCorQHom.add_assoc_four_middle_left
        (TraceCorQHom.comp head first)
        (TraceCorQHom.comp head second)
        (TraceCorQHom.comp head third)
        (TraceCorQHom.comp head fourth)))

/-- Compose on a fully right-associated four-summand target sum. -/
theorem TraceCorQHom.comp_add_add_add_right
    {source middle target : TraceCorQObject}
    (head : TraceCorQHom source middle)
    (first second third fourth : TraceCorQHom middle target) :
    TraceCorQHom.comp
      head
      (TraceCorQHom.add
        first
        (TraceCorQHom.add
          second
          (TraceCorQHom.add third fourth))) =
      TraceCorQHom.add
        (TraceCorQHom.comp head first)
        (TraceCorQHom.add
          (TraceCorQHom.comp head second)
          (TraceCorQHom.add
            (TraceCorQHom.comp head third)
            (TraceCorQHom.comp head fourth))) :=
  Eq.trans
    (TraceCorQHom.comp_add
      head
      first
      (TraceCorQHom.add
        second
        (TraceCorQHom.add third fourth)))
    (congrArg
      (TraceCorQHom.add (TraceCorQHom.comp head first))
      (TraceCorQHom.comp_add_add_right head second third fourth))

end AnalyticMotives
end LFunctions
end Boundary
