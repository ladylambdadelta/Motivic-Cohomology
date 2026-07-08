import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Smul.Sign.Distribution.Owner

/-!
# Public scalar and sign distribution through typed composition

This file exposes scalar and sign distribution normal forms for typed
trace-correspondence composites with longer additive inputs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: scale a composite whose source input is a left-associated three-summand sum. -/
theorem AnalyticMotivesRoot.traceCorQHom_smul_add_add_comp
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
  TraceCorQHom.smul_add_add_comp
    coefficient
    first
    second
    third
    post

/-- Public wrapper: scale a composite whose source input is a right-associated three-summand sum. -/
theorem AnalyticMotivesRoot.traceCorQHom_smul_add_add_comp_right
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (first second third : TraceCorQHom source middle)
    (post : TraceCorQHom middle target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.comp
        (TraceCorQHom.add first (TraceCorQHom.add second third))
        post) =
      TraceCorQHom.add
        (TraceCorQHom.comp (TraceCorQHom.smul coefficient first) post)
        (TraceCorQHom.add
          (TraceCorQHom.comp (TraceCorQHom.smul coefficient second) post)
          (TraceCorQHom.comp (TraceCorQHom.smul coefficient third) post)) :=
  TraceCorQHom.smul_add_add_comp_right
    coefficient
    first
    second
    third
    post

/-- Public wrapper: scale a composite whose source input is a left-associated four-summand sum. -/
theorem AnalyticMotivesRoot.traceCorQHom_smul_add_add_add_comp
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (first second third fourth : TraceCorQHom source middle)
    (post : TraceCorQHom middle target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.comp
        (TraceCorQHom.add
          (TraceCorQHom.add (TraceCorQHom.add first second) third)
          fourth)
        post) =
      TraceCorQHom.add
        (TraceCorQHom.comp (TraceCorQHom.smul coefficient first) post)
        (TraceCorQHom.add
          (TraceCorQHom.comp (TraceCorQHom.smul coefficient second) post)
          (TraceCorQHom.add
            (TraceCorQHom.comp (TraceCorQHom.smul coefficient third) post)
            (TraceCorQHom.comp (TraceCorQHom.smul coefficient fourth) post))) :=
  TraceCorQHom.smul_add_add_add_comp
    coefficient
    first
    second
    third
    fourth
    post

/-- Public wrapper: scale a composite whose source input is a right-associated four-summand sum. -/
theorem AnalyticMotivesRoot.traceCorQHom_smul_add_add_add_comp_right
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (first second third fourth : TraceCorQHom source middle)
    (post : TraceCorQHom middle target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.comp
        (TraceCorQHom.add
          first
          (TraceCorQHom.add second (TraceCorQHom.add third fourth)))
        post) =
      TraceCorQHom.add
        (TraceCorQHom.comp (TraceCorQHom.smul coefficient first) post)
        (TraceCorQHom.add
          (TraceCorQHom.comp (TraceCorQHom.smul coefficient second) post)
          (TraceCorQHom.add
            (TraceCorQHom.comp (TraceCorQHom.smul coefficient third) post)
            (TraceCorQHom.comp (TraceCorQHom.smul coefficient fourth) post))) :=
  TraceCorQHom.smul_add_add_add_comp_right
    coefficient
    first
    second
    third
    fourth
    post

/-- Public wrapper: scale a composite whose target input is a left-associated three-summand sum. -/
theorem AnalyticMotivesRoot.traceCorQHom_smul_comp_add_add
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
  TraceCorQHom.smul_comp_add_add
    coefficient
    pre
    first
    second
    third

/-- Public wrapper: scale a composite whose target input is a right-associated three-summand sum. -/
theorem AnalyticMotivesRoot.traceCorQHom_smul_comp_add_add_right
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (pre : TraceCorQHom source middle)
    (first second third : TraceCorQHom middle target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.comp
        pre
        (TraceCorQHom.add first (TraceCorQHom.add second third))) =
      TraceCorQHom.add
        (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient first))
        (TraceCorQHom.add
          (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient second))
          (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient third))) :=
  TraceCorQHom.smul_comp_add_add_right
    coefficient
    pre
    first
    second
    third

/-- Public wrapper: scale a composite whose target input is a left-associated four-summand sum. -/
theorem AnalyticMotivesRoot.traceCorQHom_smul_comp_add_add_add
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (pre : TraceCorQHom source middle)
    (first second third fourth : TraceCorQHom middle target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.comp
        pre
        (TraceCorQHom.add
          (TraceCorQHom.add (TraceCorQHom.add first second) third)
          fourth)) =
      TraceCorQHom.add
        (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient first))
        (TraceCorQHom.add
          (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient second))
          (TraceCorQHom.add
            (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient third))
            (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient fourth)))) :=
  TraceCorQHom.smul_comp_add_add_add
    coefficient
    pre
    first
    second
    third
    fourth

/-- Public wrapper: scale a composite whose target input is a right-associated four-summand sum. -/
theorem AnalyticMotivesRoot.traceCorQHom_smul_comp_add_add_add_right
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
          (TraceCorQHom.add second (TraceCorQHom.add third fourth)))) =
      TraceCorQHom.add
        (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient first))
        (TraceCorQHom.add
          (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient second))
          (TraceCorQHom.add
            (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient third))
            (TraceCorQHom.comp pre (TraceCorQHom.smul coefficient fourth)))) :=
  TraceCorQHom.smul_comp_add_add_add_right
    coefficient
    pre
    first
    second
    third
    fourth

/-- Public wrapper: negate a composite whose source input is a left-associated three-summand sum. -/
theorem AnalyticMotivesRoot.traceCorQHom_neg_add_add_comp
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
  TraceCorQHom.neg_add_add_comp
    first
    second
    third
    post

/-- Public wrapper: negate a composite whose source input is a right-associated three-summand sum. -/
theorem AnalyticMotivesRoot.traceCorQHom_neg_add_add_comp_right
    {source middle target : TraceCorQObject}
    (first second third : TraceCorQHom source middle)
    (post : TraceCorQHom middle target) :
    TraceCorQHom.neg
      (TraceCorQHom.comp
        (TraceCorQHom.add first (TraceCorQHom.add second third))
        post) =
      TraceCorQHom.add
        (TraceCorQHom.comp (TraceCorQHom.neg first) post)
        (TraceCorQHom.add
          (TraceCorQHom.comp (TraceCorQHom.neg second) post)
          (TraceCorQHom.comp (TraceCorQHom.neg third) post)) :=
  TraceCorQHom.neg_add_add_comp_right
    first
    second
    third
    post

/-- Public wrapper: negate a composite whose source input is a left-associated four-summand sum. -/
theorem AnalyticMotivesRoot.traceCorQHom_neg_add_add_add_comp
    {source middle target : TraceCorQObject}
    (first second third fourth : TraceCorQHom source middle)
    (post : TraceCorQHom middle target) :
    TraceCorQHom.neg
      (TraceCorQHom.comp
        (TraceCorQHom.add
          (TraceCorQHom.add (TraceCorQHom.add first second) third)
          fourth)
        post) =
      TraceCorQHom.add
        (TraceCorQHom.comp (TraceCorQHom.neg first) post)
        (TraceCorQHom.add
          (TraceCorQHom.comp (TraceCorQHom.neg second) post)
          (TraceCorQHom.add
            (TraceCorQHom.comp (TraceCorQHom.neg third) post)
            (TraceCorQHom.comp (TraceCorQHom.neg fourth) post))) :=
  TraceCorQHom.neg_add_add_add_comp
    first
    second
    third
    fourth
    post

/-- Public wrapper: negate a composite whose source input is a right-associated four-summand sum. -/
theorem AnalyticMotivesRoot.traceCorQHom_neg_add_add_add_comp_right
    {source middle target : TraceCorQObject}
    (first second third fourth : TraceCorQHom source middle)
    (post : TraceCorQHom middle target) :
    TraceCorQHom.neg
      (TraceCorQHom.comp
        (TraceCorQHom.add
          first
          (TraceCorQHom.add second (TraceCorQHom.add third fourth)))
        post) =
      TraceCorQHom.add
        (TraceCorQHom.comp (TraceCorQHom.neg first) post)
        (TraceCorQHom.add
          (TraceCorQHom.comp (TraceCorQHom.neg second) post)
          (TraceCorQHom.add
            (TraceCorQHom.comp (TraceCorQHom.neg third) post)
            (TraceCorQHom.comp (TraceCorQHom.neg fourth) post))) :=
  TraceCorQHom.neg_add_add_add_comp_right
    first
    second
    third
    fourth
    post

/-- Public wrapper: negate a composite whose target input is a left-associated three-summand sum. -/
theorem AnalyticMotivesRoot.traceCorQHom_neg_comp_add_add
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
  TraceCorQHom.neg_comp_add_add
    pre
    first
    second
    third

/-- Public wrapper: negate a composite whose target input is a right-associated three-summand sum. -/
theorem AnalyticMotivesRoot.traceCorQHom_neg_comp_add_add_right
    {source middle target : TraceCorQObject}
    (pre : TraceCorQHom source middle)
    (first second third : TraceCorQHom middle target) :
    TraceCorQHom.neg
      (TraceCorQHom.comp
        pre
        (TraceCorQHom.add first (TraceCorQHom.add second third))) =
      TraceCorQHom.add
        (TraceCorQHom.comp pre (TraceCorQHom.neg first))
        (TraceCorQHom.add
          (TraceCorQHom.comp pre (TraceCorQHom.neg second))
          (TraceCorQHom.comp pre (TraceCorQHom.neg third))) :=
  TraceCorQHom.neg_comp_add_add_right
    pre
    first
    second
    third

/-- Public wrapper: negate a composite whose target input is a left-associated four-summand sum. -/
theorem AnalyticMotivesRoot.traceCorQHom_neg_comp_add_add_add
    {source middle target : TraceCorQObject}
    (pre : TraceCorQHom source middle)
    (first second third fourth : TraceCorQHom middle target) :
    TraceCorQHom.neg
      (TraceCorQHom.comp
        pre
        (TraceCorQHom.add
          (TraceCorQHom.add (TraceCorQHom.add first second) third)
          fourth)) =
      TraceCorQHom.add
        (TraceCorQHom.comp pre (TraceCorQHom.neg first))
        (TraceCorQHom.add
          (TraceCorQHom.comp pre (TraceCorQHom.neg second))
          (TraceCorQHom.add
            (TraceCorQHom.comp pre (TraceCorQHom.neg third))
            (TraceCorQHom.comp pre (TraceCorQHom.neg fourth)))) :=
  TraceCorQHom.neg_comp_add_add_add
    pre
    first
    second
    third
    fourth

/-- Public wrapper: negate a composite whose target input is a right-associated four-summand sum. -/
theorem AnalyticMotivesRoot.traceCorQHom_neg_comp_add_add_add_right
    {source middle target : TraceCorQObject}
    (pre : TraceCorQHom source middle)
    (first second third fourth : TraceCorQHom middle target) :
    TraceCorQHom.neg
      (TraceCorQHom.comp
        pre
        (TraceCorQHom.add
          first
          (TraceCorQHom.add second (TraceCorQHom.add third fourth)))) =
      TraceCorQHom.add
        (TraceCorQHom.comp pre (TraceCorQHom.neg first))
        (TraceCorQHom.add
          (TraceCorQHom.comp pre (TraceCorQHom.neg second))
          (TraceCorQHom.add
            (TraceCorQHom.comp pre (TraceCorQHom.neg third))
            (TraceCorQHom.comp pre (TraceCorQHom.neg fourth)))) :=
  TraceCorQHom.neg_comp_add_add_add_right
    pre
    first
    second
    third
    fourth

end AnalyticMotives
end LFunctions
end Boundary
