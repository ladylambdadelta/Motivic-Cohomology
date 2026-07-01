import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.Distribution.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Add.Distribution.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Smul.Normalization.Owner

/-!
# Scalar distribution through longer typed composites

This file owns normal forms for scaling composites whose source or target input
is a longer additive sum.  The scalar is moved into the summed input, then
distributed across the sum before composition is distributed.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Scale a composite whose source input is a left-associated three-summand sum. -/
theorem TraceCorQHom.smul_add_add_comp
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (first second third : TraceCorQHom source middle)
    (post : TraceCorQHom middle target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.comp
        (TraceCorQHom.add
          (TraceCorQHom.add first second)
          third)
        post) =
      TraceCorQHom.add
        (TraceCorQHom.comp (TraceCorQHom.smul coefficient first) post)
        (TraceCorQHom.add
          (TraceCorQHom.comp (TraceCorQHom.smul coefficient second) post)
          (TraceCorQHom.comp (TraceCorQHom.smul coefficient third) post)) :=
  Eq.trans
    (TraceCorQHom.smul_comp_eq_comp_smul_left
      coefficient
      (TraceCorQHom.add (TraceCorQHom.add first second) third)
      post)
    (Eq.trans
      (congrArg
        (fun normalized =>
          TraceCorQHom.comp normalized post)
        (TraceCorQHom.smul_add_three_left coefficient first second third))
      (TraceCorQHom.add_add_comp_right
        (TraceCorQHom.smul coefficient first)
        (TraceCorQHom.smul coefficient second)
        (TraceCorQHom.smul coefficient third)
        post))

/-- Scale a composite whose source input is a right-associated three-summand sum. -/
theorem TraceCorQHom.smul_add_add_comp_right
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (first second third : TraceCorQHom source middle)
    (post : TraceCorQHom middle target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.comp
        (TraceCorQHom.add
          first
          (TraceCorQHom.add second third))
        post) =
      TraceCorQHom.add
        (TraceCorQHom.comp (TraceCorQHom.smul coefficient first) post)
        (TraceCorQHom.add
          (TraceCorQHom.comp (TraceCorQHom.smul coefficient second) post)
          (TraceCorQHom.comp (TraceCorQHom.smul coefficient third) post)) :=
  Eq.trans
    (TraceCorQHom.smul_comp_eq_comp_smul_left
      coefficient
      (TraceCorQHom.add first (TraceCorQHom.add second third))
      post)
    (Eq.trans
      (congrArg
        (fun normalized =>
          TraceCorQHom.comp normalized post)
        (TraceCorQHom.smul_add_three_right coefficient first second third))
      (TraceCorQHom.add_add_comp_right
        (TraceCorQHom.smul coefficient first)
        (TraceCorQHom.smul coefficient second)
        (TraceCorQHom.smul coefficient third)
        post))

/-- Scale a composite whose source input is a left-associated four-summand sum. -/
theorem TraceCorQHom.smul_add_add_add_comp
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (first second third fourth : TraceCorQHom source middle)
    (post : TraceCorQHom middle target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.comp
        (TraceCorQHom.add
          (TraceCorQHom.add
            (TraceCorQHom.add first second)
            third)
          fourth)
        post) =
      TraceCorQHom.add
        (TraceCorQHom.comp (TraceCorQHom.smul coefficient first) post)
        (TraceCorQHom.add
          (TraceCorQHom.comp (TraceCorQHom.smul coefficient second) post)
          (TraceCorQHom.add
            (TraceCorQHom.comp (TraceCorQHom.smul coefficient third) post)
            (TraceCorQHom.comp (TraceCorQHom.smul coefficient fourth) post))) :=
  Eq.trans
    (TraceCorQHom.smul_comp_eq_comp_smul_left
      coefficient
      (TraceCorQHom.add
        (TraceCorQHom.add (TraceCorQHom.add first second) third)
        fourth)
      post)
    (Eq.trans
      (congrArg
        (fun normalized =>
          TraceCorQHom.comp normalized post)
        (TraceCorQHom.smul_add_four_left coefficient first second third fourth))
      (TraceCorQHom.add_add_add_comp_right
        (TraceCorQHom.smul coefficient first)
        (TraceCorQHom.smul coefficient second)
        (TraceCorQHom.smul coefficient third)
        (TraceCorQHom.smul coefficient fourth)
        post))

/-- Scale a composite whose source input is a right-associated four-summand sum. -/
theorem TraceCorQHom.smul_add_add_add_comp_right
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (first second third fourth : TraceCorQHom source middle)
    (post : TraceCorQHom middle target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.comp
        (TraceCorQHom.add
          first
          (TraceCorQHom.add
            second
            (TraceCorQHom.add third fourth)))
        post) =
      TraceCorQHom.add
        (TraceCorQHom.comp (TraceCorQHom.smul coefficient first) post)
        (TraceCorQHom.add
          (TraceCorQHom.comp (TraceCorQHom.smul coefficient second) post)
          (TraceCorQHom.add
            (TraceCorQHom.comp (TraceCorQHom.smul coefficient third) post)
            (TraceCorQHom.comp (TraceCorQHom.smul coefficient fourth) post))) :=
  Eq.trans
    (TraceCorQHom.smul_comp_eq_comp_smul_left
      coefficient
      (TraceCorQHom.add
        first
        (TraceCorQHom.add second (TraceCorQHom.add third fourth)))
      post)
    (Eq.trans
      (congrArg
        (fun normalized =>
          TraceCorQHom.comp normalized post)
        (TraceCorQHom.smul_add_four_right coefficient first second third fourth))
      (TraceCorQHom.add_add_add_comp_right
        (TraceCorQHom.smul coefficient first)
        (TraceCorQHom.smul coefficient second)
        (TraceCorQHom.smul coefficient third)
        (TraceCorQHom.smul coefficient fourth)
        post))

/-- Scale a composite whose target input is a left-associated three-summand sum. -/
theorem TraceCorQHom.smul_comp_add_add
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (pre : TraceCorQHom source middle)
    (first second third : TraceCorQHom middle target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.comp
        pre
        (TraceCorQHom.add
          (TraceCorQHom.add first second)
          third)) =
      TraceCorQHom.add
        (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient first))
        (TraceCorQHom.add
          (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient second))
          (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient third))) :=
  Eq.trans
    (TraceCorQHom.smul_comp_eq_comp_smul_right
      coefficient
      pre
      (TraceCorQHom.add (TraceCorQHom.add first second) third))
    (Eq.trans
      (congrArg
        (TraceCorQHom.comp pre)
        (TraceCorQHom.smul_add_three_left coefficient first second third))
      (TraceCorQHom.comp_add_add_right
        pre
        (TraceCorQHom.smul coefficient first)
        (TraceCorQHom.smul coefficient second)
        (TraceCorQHom.smul coefficient third)))

/-- Scale a composite whose target input is a right-associated three-summand sum. -/
theorem TraceCorQHom.smul_comp_add_add_right
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (pre : TraceCorQHom source middle)
    (first second third : TraceCorQHom middle target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.comp
        pre
        (TraceCorQHom.add
          first
          (TraceCorQHom.add second third))) =
      TraceCorQHom.add
        (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient first))
        (TraceCorQHom.add
          (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient second))
          (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient third))) :=
  Eq.trans
    (TraceCorQHom.smul_comp_eq_comp_smul_right
      coefficient
      pre
      (TraceCorQHom.add first (TraceCorQHom.add second third)))
    (Eq.trans
      (congrArg
        (TraceCorQHom.comp pre)
        (TraceCorQHom.smul_add_three_right coefficient first second third))
      (TraceCorQHom.comp_add_add_right
        pre
        (TraceCorQHom.smul coefficient first)
        (TraceCorQHom.smul coefficient second)
        (TraceCorQHom.smul coefficient third)))

/-- Scale a composite whose target input is a left-associated four-summand sum. -/
theorem TraceCorQHom.smul_comp_add_add_add
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (pre : TraceCorQHom source middle)
    (first second third fourth : TraceCorQHom middle target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.comp
        pre
        (TraceCorQHom.add
          (TraceCorQHom.add
            (TraceCorQHom.add first second)
            third)
          fourth)) =
      TraceCorQHom.add
        (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient first))
        (TraceCorQHom.add
          (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient second))
          (TraceCorQHom.add
            (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient third))
            (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient fourth)))) :=
  Eq.trans
    (TraceCorQHom.smul_comp_eq_comp_smul_right
      coefficient
      pre
      (TraceCorQHom.add
        (TraceCorQHom.add (TraceCorQHom.add first second) third)
        fourth))
    (Eq.trans
      (congrArg
        (TraceCorQHom.comp pre)
        (TraceCorQHom.smul_add_four_left coefficient first second third fourth))
      (TraceCorQHom.comp_add_add_add_right
        pre
        (TraceCorQHom.smul coefficient first)
        (TraceCorQHom.smul coefficient second)
        (TraceCorQHom.smul coefficient third)
        (TraceCorQHom.smul coefficient fourth)))

/-- Scale a composite whose target input is a right-associated four-summand sum. -/
theorem TraceCorQHom.smul_comp_add_add_add_right
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (pre : TraceCorQHom source middle)
    (first second third fourth : TraceCorQHom middle target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.comp
        pre
        (TraceCorQHom.add
          first
          (TraceCorQHom.add
            second
            (TraceCorQHom.add third fourth)))) =
      TraceCorQHom.add
        (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient first))
        (TraceCorQHom.add
          (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient second))
          (TraceCorQHom.add
            (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient third))
            (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient fourth)))) :=
  Eq.trans
    (TraceCorQHom.smul_comp_eq_comp_smul_right
      coefficient
      pre
      (TraceCorQHom.add
        first
        (TraceCorQHom.add second (TraceCorQHom.add third fourth))))
    (Eq.trans
      (congrArg
        (TraceCorQHom.comp pre)
        (TraceCorQHom.smul_add_four_right coefficient first second third fourth))
      (TraceCorQHom.comp_add_add_add_right
        pre
        (TraceCorQHom.smul coefficient first)
        (TraceCorQHom.smul coefficient second)
        (TraceCorQHom.smul coefficient third)
        (TraceCorQHom.smul coefficient fourth)))

end AnalyticMotives
end LFunctions
end Boundary
