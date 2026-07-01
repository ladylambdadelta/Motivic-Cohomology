import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Laws.Distribution.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Laws.Distribution.Owner

/-!
# Longer subtractive distribution for quotient composition

This file owns normal forms for composing longer quotient sums whose final
summand is subtracted.  The target normal form is fully right-associated.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Compose a left-associated three-summand quotient source sum with subtraction pushed last. -/
theorem TraceCorQQuotient.add_add_sub_comp
    (first second third tail post : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.sub
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add first second)
          third)
        tail)
      post =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp first post)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp second post)
          (TraceCorQQuotient.sub
            (TraceCorQQuotient.comp third post)
            (TraceCorQQuotient.comp tail post))) :=
  Eq.trans
    (congrArg
      (fun normalized =>
        TraceCorQQuotient.comp normalized post)
      (TraceCorQQuotient.add_add_sub first second third tail))
    (Eq.trans
      (TraceCorQQuotient.add_add_comp_right
        first
        second
        (TraceCorQQuotient.sub third tail)
        post)
      (congrArg
        (TraceCorQQuotient.add (TraceCorQQuotient.comp first post))
        (congrArg
          (TraceCorQQuotient.add (TraceCorQQuotient.comp second post))
          (TraceCorQQuotient.sub_comp third tail post))))

/-- Compose a right-associated three-summand quotient source sum with subtraction pushed last. -/
theorem TraceCorQQuotient.add_add_sub_comp_right
    (first second third tail post : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.sub
        (TraceCorQQuotient.add
          first
          (TraceCorQQuotient.add second third))
        tail)
      post =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp first post)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp second post)
          (TraceCorQQuotient.sub
            (TraceCorQQuotient.comp third post)
            (TraceCorQQuotient.comp tail post))) :=
  Eq.trans
    (congrArg
      (fun normalized =>
        TraceCorQQuotient.comp normalized post)
      (TraceCorQQuotient.add_add_sub_right first second third tail))
    (Eq.trans
      (TraceCorQQuotient.add_add_comp_right
        first
        second
        (TraceCorQQuotient.sub third tail)
        post)
      (congrArg
        (TraceCorQQuotient.add (TraceCorQQuotient.comp first post))
        (congrArg
          (TraceCorQQuotient.add (TraceCorQQuotient.comp second post))
          (TraceCorQQuotient.sub_comp third tail post))))

/-- Compose a left-associated four-summand quotient source sum with subtraction pushed last. -/
theorem TraceCorQQuotient.add_add_add_sub_comp
    (first second third fourth tail post : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.sub
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add
            (TraceCorQQuotient.add first second)
            third)
          fourth)
        tail)
      post =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp first post)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp second post)
          (TraceCorQQuotient.add
            (TraceCorQQuotient.comp third post)
            (TraceCorQQuotient.sub
              (TraceCorQQuotient.comp fourth post)
              (TraceCorQQuotient.comp tail post)))) :=
  Eq.trans
    (congrArg
      (fun normalized =>
        TraceCorQQuotient.comp normalized post)
      (TraceCorQQuotient.add_add_add_sub first second third fourth tail))
    (Eq.trans
      (TraceCorQQuotient.add_add_add_comp_right
        first
        second
        third
        (TraceCorQQuotient.sub fourth tail)
        post)
      (congrArg
        (TraceCorQQuotient.add (TraceCorQQuotient.comp first post))
        (congrArg
          (TraceCorQQuotient.add (TraceCorQQuotient.comp second post))
          (congrArg
            (TraceCorQQuotient.add (TraceCorQQuotient.comp third post))
            (TraceCorQQuotient.sub_comp fourth tail post)))))

/-- Compose a right-associated four-summand quotient source sum with subtraction pushed last. -/
theorem TraceCorQQuotient.add_add_add_sub_comp_right
    (first second third fourth tail post : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.sub
        (TraceCorQQuotient.add
          first
          (TraceCorQQuotient.add
            second
            (TraceCorQQuotient.add third fourth)))
        tail)
      post =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp first post)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp second post)
          (TraceCorQQuotient.add
            (TraceCorQQuotient.comp third post)
            (TraceCorQQuotient.sub
              (TraceCorQQuotient.comp fourth post)
              (TraceCorQQuotient.comp tail post)))) :=
  Eq.trans
    (congrArg
      (fun normalized =>
        TraceCorQQuotient.comp normalized post)
      (TraceCorQQuotient.add_add_add_sub_right first second third fourth tail))
    (Eq.trans
      (TraceCorQQuotient.add_add_add_comp_right
        first
        second
        third
        (TraceCorQQuotient.sub fourth tail)
        post)
      (congrArg
        (TraceCorQQuotient.add (TraceCorQQuotient.comp first post))
        (congrArg
          (TraceCorQQuotient.add (TraceCorQQuotient.comp second post))
          (congrArg
            (TraceCorQQuotient.add (TraceCorQQuotient.comp third post))
            (TraceCorQQuotient.sub_comp fourth tail post)))))

/-- Compose into a left-associated three-summand quotient target sum with subtraction pushed last. -/
theorem TraceCorQQuotient.comp_add_add_sub
    (pre first second third tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      pre
      (TraceCorQQuotient.sub
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add first second)
          third)
        tail) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp pre first)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp pre second)
          (TraceCorQQuotient.sub
            (TraceCorQQuotient.comp pre third)
            (TraceCorQQuotient.comp pre tail))) :=
  Eq.trans
    (congrArg
      (TraceCorQQuotient.comp pre)
      (TraceCorQQuotient.add_add_sub first second third tail))
    (Eq.trans
      (TraceCorQQuotient.comp_add_add_right
        pre
        first
        second
        (TraceCorQQuotient.sub third tail))
      (congrArg
        (TraceCorQQuotient.add (TraceCorQQuotient.comp pre first))
        (congrArg
          (TraceCorQQuotient.add (TraceCorQQuotient.comp pre second))
          (TraceCorQQuotient.comp_sub pre third tail))))

/-- Compose into a right-associated three-summand quotient target sum with subtraction pushed last. -/
theorem TraceCorQQuotient.comp_add_add_sub_right
    (pre first second third tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      pre
      (TraceCorQQuotient.sub
        (TraceCorQQuotient.add
          first
          (TraceCorQQuotient.add second third))
        tail) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp pre first)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp pre second)
          (TraceCorQQuotient.sub
            (TraceCorQQuotient.comp pre third)
            (TraceCorQQuotient.comp pre tail))) :=
  Eq.trans
    (congrArg
      (TraceCorQQuotient.comp pre)
      (TraceCorQQuotient.add_add_sub_right first second third tail))
    (Eq.trans
      (TraceCorQQuotient.comp_add_add_right
        pre
        first
        second
        (TraceCorQQuotient.sub third tail))
      (congrArg
        (TraceCorQQuotient.add (TraceCorQQuotient.comp pre first))
        (congrArg
          (TraceCorQQuotient.add (TraceCorQQuotient.comp pre second))
          (TraceCorQQuotient.comp_sub pre third tail))))

/-- Compose into a left-associated four-summand quotient target sum with subtraction pushed last. -/
theorem TraceCorQQuotient.comp_add_add_add_sub
    (pre first second third fourth tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      pre
      (TraceCorQQuotient.sub
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add
            (TraceCorQQuotient.add first second)
            third)
          fourth)
        tail) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp pre first)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp pre second)
          (TraceCorQQuotient.add
            (TraceCorQQuotient.comp pre third)
            (TraceCorQQuotient.sub
              (TraceCorQQuotient.comp pre fourth)
              (TraceCorQQuotient.comp pre tail)))) :=
  Eq.trans
    (congrArg
      (TraceCorQQuotient.comp pre)
      (TraceCorQQuotient.add_add_add_sub first second third fourth tail))
    (Eq.trans
      (TraceCorQQuotient.comp_add_add_add_right
        pre
        first
        second
        third
        (TraceCorQQuotient.sub fourth tail))
      (congrArg
        (TraceCorQQuotient.add (TraceCorQQuotient.comp pre first))
        (congrArg
          (TraceCorQQuotient.add (TraceCorQQuotient.comp pre second))
          (congrArg
            (TraceCorQQuotient.add (TraceCorQQuotient.comp pre third))
            (TraceCorQQuotient.comp_sub pre fourth tail)))))

/-- Compose into a right-associated four-summand quotient target sum with subtraction pushed last. -/
theorem TraceCorQQuotient.comp_add_add_add_sub_right
    (pre first second third fourth tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      pre
      (TraceCorQQuotient.sub
        (TraceCorQQuotient.add
          first
          (TraceCorQQuotient.add
            second
            (TraceCorQQuotient.add third fourth)))
        tail) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp pre first)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp pre second)
          (TraceCorQQuotient.add
            (TraceCorQQuotient.comp pre third)
            (TraceCorQQuotient.sub
              (TraceCorQQuotient.comp pre fourth)
              (TraceCorQQuotient.comp pre tail)))) :=
  Eq.trans
    (congrArg
      (TraceCorQQuotient.comp pre)
      (TraceCorQQuotient.add_add_add_sub_right first second third fourth tail))
    (Eq.trans
      (TraceCorQQuotient.comp_add_add_add_right
        pre
        first
        second
        third
        (TraceCorQQuotient.sub fourth tail))
      (congrArg
        (TraceCorQQuotient.add (TraceCorQQuotient.comp pre first))
        (congrArg
          (TraceCorQQuotient.add (TraceCorQQuotient.comp pre second))
          (congrArg
            (TraceCorQQuotient.add (TraceCorQQuotient.comp pre third))
            (TraceCorQQuotient.comp_sub pre fourth tail)))))

end AnalyticMotives
end LFunctions
end Boundary
