import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Smul.Sign.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Smul.Distribution.Owner

/-!
# Sign distribution through longer typed composites

This file owns negation normal forms for composites whose source or target
input is a longer additive sum.  These are the `-1` specializations of the
scalar distribution-through-composition theorems.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Negate a composite whose source input is a left-associated three-summand sum. -/
theorem TraceCorQHom.neg_add_add_comp
    {source middle target : TraceCorQObject}
    (first second third : TraceCorQHom source middle)
    (post : TraceCorQHom middle target) :
    TraceCorQHom.neg
      (TraceCorQHom.comp
        (TraceCorQHom.add
          (TraceCorQHom.add first second)
          third)
        post) =
      TraceCorQHom.add
        (TraceCorQHom.comp (TraceCorQHom.neg first) post)
        (TraceCorQHom.add
          (TraceCorQHom.comp (TraceCorQHom.neg second) post)
          (TraceCorQHom.comp (TraceCorQHom.neg third) post)) :=
  TraceCorQHom.smul_add_add_comp
    (-1)
    first
    second
    third
    post

/-- Negate a composite whose source input is a right-associated three-summand sum. -/
theorem TraceCorQHom.neg_add_add_comp_right
    {source middle target : TraceCorQObject}
    (first second third : TraceCorQHom source middle)
    (post : TraceCorQHom middle target) :
    TraceCorQHom.neg
      (TraceCorQHom.comp
        (TraceCorQHom.add
          first
          (TraceCorQHom.add second third))
        post) =
      TraceCorQHom.add
        (TraceCorQHom.comp (TraceCorQHom.neg first) post)
        (TraceCorQHom.add
          (TraceCorQHom.comp (TraceCorQHom.neg second) post)
          (TraceCorQHom.comp (TraceCorQHom.neg third) post)) :=
  TraceCorQHom.smul_add_add_comp_right
    (-1)
    first
    second
    third
    post

/-- Negate a composite whose source input is a left-associated four-summand sum. -/
theorem TraceCorQHom.neg_add_add_add_comp
    {source middle target : TraceCorQObject}
    (first second third fourth : TraceCorQHom source middle)
    (post : TraceCorQHom middle target) :
    TraceCorQHom.neg
      (TraceCorQHom.comp
        (TraceCorQHom.add
          (TraceCorQHom.add
            (TraceCorQHom.add first second)
            third)
          fourth)
        post) =
      TraceCorQHom.add
        (TraceCorQHom.comp (TraceCorQHom.neg first) post)
        (TraceCorQHom.add
          (TraceCorQHom.comp (TraceCorQHom.neg second) post)
          (TraceCorQHom.add
            (TraceCorQHom.comp (TraceCorQHom.neg third) post)
            (TraceCorQHom.comp (TraceCorQHom.neg fourth) post))) :=
  TraceCorQHom.smul_add_add_add_comp
    (-1)
    first
    second
    third
    fourth
    post

/-- Negate a composite whose source input is a right-associated four-summand sum. -/
theorem TraceCorQHom.neg_add_add_add_comp_right
    {source middle target : TraceCorQObject}
    (first second third fourth : TraceCorQHom source middle)
    (post : TraceCorQHom middle target) :
    TraceCorQHom.neg
      (TraceCorQHom.comp
        (TraceCorQHom.add
          first
          (TraceCorQHom.add
            second
            (TraceCorQHom.add third fourth)))
        post) =
      TraceCorQHom.add
        (TraceCorQHom.comp (TraceCorQHom.neg first) post)
        (TraceCorQHom.add
          (TraceCorQHom.comp (TraceCorQHom.neg second) post)
          (TraceCorQHom.add
            (TraceCorQHom.comp (TraceCorQHom.neg third) post)
            (TraceCorQHom.comp (TraceCorQHom.neg fourth) post))) :=
  TraceCorQHom.smul_add_add_add_comp_right
    (-1)
    first
    second
    third
    fourth
    post

/-- Negate a composite whose target input is a left-associated three-summand sum. -/
theorem TraceCorQHom.neg_comp_add_add
    {source middle target : TraceCorQObject}
    (pre : TraceCorQHom source middle)
    (first second third : TraceCorQHom middle target) :
    TraceCorQHom.neg
      (TraceCorQHom.comp
        pre
        (TraceCorQHom.add
          (TraceCorQHom.add first second)
          third)) =
      TraceCorQHom.add
        (TraceCorQHom.comp pre (TraceCorQHom.neg first))
        (TraceCorQHom.add
          (TraceCorQHom.comp pre (TraceCorQHom.neg second))
          (TraceCorQHom.comp pre (TraceCorQHom.neg third))) :=
  TraceCorQHom.smul_comp_add_add
    (-1)
    pre
    first
    second
    third

/-- Negate a composite whose target input is a right-associated three-summand sum. -/
theorem TraceCorQHom.neg_comp_add_add_right
    {source middle target : TraceCorQObject}
    (pre : TraceCorQHom source middle)
    (first second third : TraceCorQHom middle target) :
    TraceCorQHom.neg
      (TraceCorQHom.comp
        pre
        (TraceCorQHom.add
          first
          (TraceCorQHom.add second third))) =
      TraceCorQHom.add
        (TraceCorQHom.comp pre (TraceCorQHom.neg first))
        (TraceCorQHom.add
          (TraceCorQHom.comp pre (TraceCorQHom.neg second))
          (TraceCorQHom.comp pre (TraceCorQHom.neg third))) :=
  TraceCorQHom.smul_comp_add_add_right
    (-1)
    pre
    first
    second
    third

/-- Negate a composite whose target input is a left-associated four-summand sum. -/
theorem TraceCorQHom.neg_comp_add_add_add
    {source middle target : TraceCorQObject}
    (pre : TraceCorQHom source middle)
    (first second third fourth : TraceCorQHom middle target) :
    TraceCorQHom.neg
      (TraceCorQHom.comp
        pre
        (TraceCorQHom.add
          (TraceCorQHom.add
            (TraceCorQHom.add first second)
            third)
          fourth)) =
      TraceCorQHom.add
        (TraceCorQHom.comp pre (TraceCorQHom.neg first))
        (TraceCorQHom.add
          (TraceCorQHom.comp pre (TraceCorQHom.neg second))
          (TraceCorQHom.add
            (TraceCorQHom.comp pre (TraceCorQHom.neg third))
            (TraceCorQHom.comp pre (TraceCorQHom.neg fourth)))) :=
  TraceCorQHom.smul_comp_add_add_add
    (-1)
    pre
    first
    second
    third
    fourth

/-- Negate a composite whose target input is a right-associated four-summand sum. -/
theorem TraceCorQHom.neg_comp_add_add_add_right
    {source middle target : TraceCorQObject}
    (pre : TraceCorQHom source middle)
    (first second third fourth : TraceCorQHom middle target) :
    TraceCorQHom.neg
      (TraceCorQHom.comp
        pre
        (TraceCorQHom.add
          first
          (TraceCorQHom.add
            second
            (TraceCorQHom.add third fourth)))) =
      TraceCorQHom.add
        (TraceCorQHom.comp pre (TraceCorQHom.neg first))
        (TraceCorQHom.add
          (TraceCorQHom.comp pre (TraceCorQHom.neg second))
          (TraceCorQHom.add
            (TraceCorQHom.comp pre (TraceCorQHom.neg third))
            (TraceCorQHom.comp pre (TraceCorQHom.neg fourth)))) :=
  TraceCorQHom.smul_comp_add_add_add_right
    (-1)
    pre
    first
    second
    third
    fourth

end AnalyticMotives
end LFunctions
end Boundary
