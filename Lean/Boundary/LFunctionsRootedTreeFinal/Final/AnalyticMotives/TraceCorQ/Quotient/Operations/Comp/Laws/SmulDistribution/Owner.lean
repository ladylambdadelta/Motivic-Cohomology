import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Laws.Distribution.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.Distribution.Owner

/-!
# Scalar distribution through longer quotient composites

This file owns normal forms for scaling quotient composites whose source or
target input is a longer additive sum.  The scalar is moved into the summed
input, distributed across the sum, and then composition is distributed.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Scale a quotient composite whose source input is a left-associated three-summand sum. -/
theorem TraceCorQQuotient.smul_add_add_comp
    (coefficient : Rat)
    (first second third post : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add first second)
          third)
        post) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp (TraceCorQQuotient.smul coefficient first) post)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp (TraceCorQQuotient.smul coefficient second) post)
          (TraceCorQQuotient.comp (TraceCorQQuotient.smul coefficient third) post)) :=
  Eq.trans
    (Eq.symm
      (TraceCorQQuotient.smul_comp
        coefficient
        (TraceCorQQuotient.add (TraceCorQQuotient.add first second) third)
        post))
    (Eq.trans
      (congrArg
        (fun normalized =>
          TraceCorQQuotient.comp normalized post)
        (TraceCorQQuotient.smul_add_three_left coefficient first second third))
      (TraceCorQQuotient.add_add_comp_right
        (TraceCorQQuotient.smul coefficient first)
        (TraceCorQQuotient.smul coefficient second)
        (TraceCorQQuotient.smul coefficient third)
        post))

/-- Scale a quotient composite whose source input is a right-associated three-summand sum. -/
theorem TraceCorQQuotient.smul_add_add_comp_right
    (coefficient : Rat)
    (first second third post : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.add
          first
          (TraceCorQQuotient.add second third))
        post) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp (TraceCorQQuotient.smul coefficient first) post)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp (TraceCorQQuotient.smul coefficient second) post)
          (TraceCorQQuotient.comp (TraceCorQQuotient.smul coefficient third) post)) :=
  Eq.trans
    (Eq.symm
      (TraceCorQQuotient.smul_comp
        coefficient
        (TraceCorQQuotient.add first (TraceCorQQuotient.add second third))
        post))
    (Eq.trans
      (congrArg
        (fun normalized =>
          TraceCorQQuotient.comp normalized post)
        (TraceCorQQuotient.smul_add_three_right coefficient first second third))
      (TraceCorQQuotient.add_add_comp_right
        (TraceCorQQuotient.smul coefficient first)
        (TraceCorQQuotient.smul coefficient second)
        (TraceCorQQuotient.smul coefficient third)
        post))

/-- Scale a quotient composite whose source input is a left-associated four-summand sum. -/
theorem TraceCorQQuotient.smul_add_add_add_comp
    (coefficient : Rat)
    (first second third fourth post : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add
            (TraceCorQQuotient.add first second)
            third)
          fourth)
        post) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp (TraceCorQQuotient.smul coefficient first) post)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp (TraceCorQQuotient.smul coefficient second) post)
          (TraceCorQQuotient.add
            (TraceCorQQuotient.comp (TraceCorQQuotient.smul coefficient third) post)
            (TraceCorQQuotient.comp (TraceCorQQuotient.smul coefficient fourth) post))) :=
  Eq.trans
    (Eq.symm
      (TraceCorQQuotient.smul_comp
        coefficient
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add (TraceCorQQuotient.add first second) third)
          fourth)
        post))
    (Eq.trans
      (congrArg
        (fun normalized =>
          TraceCorQQuotient.comp normalized post)
        (TraceCorQQuotient.smul_add_four_left coefficient first second third fourth))
      (TraceCorQQuotient.add_add_add_comp_right
        (TraceCorQQuotient.smul coefficient first)
        (TraceCorQQuotient.smul coefficient second)
        (TraceCorQQuotient.smul coefficient third)
        (TraceCorQQuotient.smul coefficient fourth)
        post))

/-- Scale a quotient composite whose source input is a right-associated four-summand sum. -/
theorem TraceCorQQuotient.smul_add_add_add_comp_right
    (coefficient : Rat)
    (first second third fourth post : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.add
          first
          (TraceCorQQuotient.add
            second
            (TraceCorQQuotient.add third fourth)))
        post) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp (TraceCorQQuotient.smul coefficient first) post)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp (TraceCorQQuotient.smul coefficient second) post)
          (TraceCorQQuotient.add
            (TraceCorQQuotient.comp (TraceCorQQuotient.smul coefficient third) post)
            (TraceCorQQuotient.comp (TraceCorQQuotient.smul coefficient fourth) post))) :=
  Eq.trans
    (Eq.symm
      (TraceCorQQuotient.smul_comp
        coefficient
        (TraceCorQQuotient.add
          first
          (TraceCorQQuotient.add second (TraceCorQQuotient.add third fourth)))
        post))
    (Eq.trans
      (congrArg
        (fun normalized =>
          TraceCorQQuotient.comp normalized post)
        (TraceCorQQuotient.smul_add_four_right coefficient first second third fourth))
      (TraceCorQQuotient.add_add_add_comp_right
        (TraceCorQQuotient.smul coefficient first)
        (TraceCorQQuotient.smul coefficient second)
        (TraceCorQQuotient.smul coefficient third)
        (TraceCorQQuotient.smul coefficient fourth)
        post))

/-- Scale a quotient composite whose target input is a left-associated three-summand sum. -/
theorem TraceCorQQuotient.smul_comp_add_add
    (coefficient : Rat)
    (pre first second third : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.comp
        pre
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add first second)
          third)) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp pre (TraceCorQQuotient.smul coefficient first))
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp pre (TraceCorQQuotient.smul coefficient second))
          (TraceCorQQuotient.comp pre (TraceCorQQuotient.smul coefficient third))) :=
  Eq.trans
    (Eq.symm
      (TraceCorQQuotient.comp_smul
        coefficient
        pre
        (TraceCorQQuotient.add (TraceCorQQuotient.add first second) third)))
    (Eq.trans
      (congrArg
        (TraceCorQQuotient.comp pre)
        (TraceCorQQuotient.smul_add_three_left coefficient first second third))
      (TraceCorQQuotient.comp_add_add_right
        pre
        (TraceCorQQuotient.smul coefficient first)
        (TraceCorQQuotient.smul coefficient second)
        (TraceCorQQuotient.smul coefficient third)))

/-- Scale a quotient composite whose target input is a right-associated three-summand sum. -/
theorem TraceCorQQuotient.smul_comp_add_add_right
    (coefficient : Rat)
    (pre first second third : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.comp
        pre
        (TraceCorQQuotient.add
          first
          (TraceCorQQuotient.add second third))) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp pre (TraceCorQQuotient.smul coefficient first))
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp pre (TraceCorQQuotient.smul coefficient second))
          (TraceCorQQuotient.comp pre (TraceCorQQuotient.smul coefficient third))) :=
  Eq.trans
    (Eq.symm
      (TraceCorQQuotient.comp_smul
        coefficient
        pre
        (TraceCorQQuotient.add first (TraceCorQQuotient.add second third))))
    (Eq.trans
      (congrArg
        (TraceCorQQuotient.comp pre)
        (TraceCorQQuotient.smul_add_three_right coefficient first second third))
      (TraceCorQQuotient.comp_add_add_right
        pre
        (TraceCorQQuotient.smul coefficient first)
        (TraceCorQQuotient.smul coefficient second)
        (TraceCorQQuotient.smul coefficient third)))

/-- Scale a quotient composite whose target input is a left-associated four-summand sum. -/
theorem TraceCorQQuotient.smul_comp_add_add_add
    (coefficient : Rat)
    (pre first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.comp
        pre
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add
            (TraceCorQQuotient.add first second)
            third)
          fourth)) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp pre (TraceCorQQuotient.smul coefficient first))
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp pre (TraceCorQQuotient.smul coefficient second))
          (TraceCorQQuotient.add
            (TraceCorQQuotient.comp pre (TraceCorQQuotient.smul coefficient third))
            (TraceCorQQuotient.comp pre (TraceCorQQuotient.smul coefficient fourth)))) :=
  Eq.trans
    (Eq.symm
      (TraceCorQQuotient.comp_smul
        coefficient
        pre
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add (TraceCorQQuotient.add first second) third)
          fourth)))
    (Eq.trans
      (congrArg
        (TraceCorQQuotient.comp pre)
        (TraceCorQQuotient.smul_add_four_left coefficient first second third fourth))
      (TraceCorQQuotient.comp_add_add_add_right
        pre
        (TraceCorQQuotient.smul coefficient first)
        (TraceCorQQuotient.smul coefficient second)
        (TraceCorQQuotient.smul coefficient third)
        (TraceCorQQuotient.smul coefficient fourth)))

/-- Scale a quotient composite whose target input is a right-associated four-summand sum. -/
theorem TraceCorQQuotient.smul_comp_add_add_add_right
    (coefficient : Rat)
    (pre first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.comp
        pre
        (TraceCorQQuotient.add
          first
          (TraceCorQQuotient.add
            second
            (TraceCorQQuotient.add third fourth)))) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp pre (TraceCorQQuotient.smul coefficient first))
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp pre (TraceCorQQuotient.smul coefficient second))
          (TraceCorQQuotient.add
            (TraceCorQQuotient.comp pre (TraceCorQQuotient.smul coefficient third))
            (TraceCorQQuotient.comp pre (TraceCorQQuotient.smul coefficient fourth)))) :=
  Eq.trans
    (Eq.symm
      (TraceCorQQuotient.comp_smul
        coefficient
        pre
        (TraceCorQQuotient.add
          first
          (TraceCorQQuotient.add second (TraceCorQQuotient.add third fourth)))))
    (Eq.trans
      (congrArg
        (TraceCorQQuotient.comp pre)
        (TraceCorQQuotient.smul_add_four_right coefficient first second third fourth))
      (TraceCorQQuotient.comp_add_add_add_right
        pre
        (TraceCorQQuotient.smul coefficient first)
        (TraceCorQQuotient.smul coefficient second)
        (TraceCorQQuotient.smul coefficient third)
        (TraceCorQQuotient.smul coefficient fourth)))

end AnalyticMotives
end LFunctions
end Boundary
