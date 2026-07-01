import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Add.Distribution.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Sub.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Laws.Distribution.Owner

/-!
# Longer subtractive distribution for typed composition

This file owns normal forms for composing longer sums whose final summand is
subtracted.  The target normal form is fully right-associated.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Compose a left-associated three-summand source sum with subtraction pushed to the last term. -/
theorem TraceCorQHom.add_add_sub_comp
    {source middle target : TraceCorQObject}
    (first second third tail : TraceCorQHom source middle)
    (post : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.sub
        (TraceCorQHom.add
          (TraceCorQHom.add first second)
          third)
        tail)
      post =
      TraceCorQHom.add
        (TraceCorQHom.comp first post)
        (TraceCorQHom.add
          (TraceCorQHom.comp second post)
          (TraceCorQHom.sub
            (TraceCorQHom.comp third post)
            (TraceCorQHom.comp tail post))) :=
  Eq.trans
    (congrArg
      (fun normalized =>
        TraceCorQHom.comp normalized post)
      (TraceCorQHom.add_add_sub first second third tail))
    (Eq.trans
      (TraceCorQHom.add_add_comp_right
        first
        second
        (TraceCorQHom.sub third tail)
        post)
      (congrArg
        (TraceCorQHom.add (TraceCorQHom.comp first post))
        (congrArg
          (TraceCorQHom.add (TraceCorQHom.comp second post))
          (TraceCorQHom.sub_comp third tail post))))

/-- Compose a fully right-associated three-summand source sum with subtraction pushed last. -/
theorem TraceCorQHom.add_add_sub_comp_right
    {source middle target : TraceCorQObject}
    (first second third tail : TraceCorQHom source middle)
    (post : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.sub
        (TraceCorQHom.add
          first
          (TraceCorQHom.add second third))
        tail)
      post =
      TraceCorQHom.add
        (TraceCorQHom.comp first post)
        (TraceCorQHom.add
          (TraceCorQHom.comp second post)
          (TraceCorQHom.sub
            (TraceCorQHom.comp third post)
            (TraceCorQHom.comp tail post))) :=
  Eq.trans
    (congrArg
      (fun normalized =>
        TraceCorQHom.comp normalized post)
      (TraceCorQHom.add_add_sub_right first second third tail))
    (Eq.trans
      (TraceCorQHom.add_add_comp_right
        first
        second
        (TraceCorQHom.sub third tail)
        post)
      (congrArg
        (TraceCorQHom.add (TraceCorQHom.comp first post))
        (congrArg
          (TraceCorQHom.add (TraceCorQHom.comp second post))
          (TraceCorQHom.sub_comp third tail post))))

/-- Compose a fully left-associated four-summand source sum with subtraction pushed last. -/
theorem TraceCorQHom.add_add_add_sub_comp
    {source middle target : TraceCorQObject}
    (first second third fourth tail : TraceCorQHom source middle)
    (post : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.sub
        (TraceCorQHom.add
          (TraceCorQHom.add
            (TraceCorQHom.add first second)
            third)
          fourth)
        tail)
      post =
      TraceCorQHom.add
        (TraceCorQHom.comp first post)
        (TraceCorQHom.add
          (TraceCorQHom.comp second post)
          (TraceCorQHom.add
            (TraceCorQHom.comp third post)
            (TraceCorQHom.sub
              (TraceCorQHom.comp fourth post)
              (TraceCorQHom.comp tail post)))) :=
  Eq.trans
    (congrArg
      (fun normalized =>
        TraceCorQHom.comp normalized post)
      (TraceCorQHom.add_add_add_sub first second third fourth tail))
    (Eq.trans
      (TraceCorQHom.add_add_add_comp_right
        first
        second
        third
        (TraceCorQHom.sub fourth tail)
        post)
      (congrArg
        (TraceCorQHom.add (TraceCorQHom.comp first post))
        (congrArg
          (TraceCorQHom.add (TraceCorQHom.comp second post))
          (congrArg
            (TraceCorQHom.add (TraceCorQHom.comp third post))
            (TraceCorQHom.sub_comp fourth tail post)))))

/-- Compose a fully right-associated four-summand source sum with subtraction pushed last. -/
theorem TraceCorQHom.add_add_add_sub_comp_right
    {source middle target : TraceCorQObject}
    (first second third fourth tail : TraceCorQHom source middle)
    (post : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.sub
        (TraceCorQHom.add
          first
          (TraceCorQHom.add
            second
            (TraceCorQHom.add third fourth)))
        tail)
      post =
      TraceCorQHom.add
        (TraceCorQHom.comp first post)
        (TraceCorQHom.add
          (TraceCorQHom.comp second post)
          (TraceCorQHom.add
            (TraceCorQHom.comp third post)
            (TraceCorQHom.sub
              (TraceCorQHom.comp fourth post)
              (TraceCorQHom.comp tail post)))) :=
  Eq.trans
    (congrArg
      (fun normalized =>
        TraceCorQHom.comp normalized post)
      (TraceCorQHom.add_add_add_sub_right first second third fourth tail))
    (Eq.trans
      (TraceCorQHom.add_add_add_comp_right
        first
        second
        third
        (TraceCorQHom.sub fourth tail)
        post)
      (congrArg
        (TraceCorQHom.add (TraceCorQHom.comp first post))
        (congrArg
          (TraceCorQHom.add (TraceCorQHom.comp second post))
          (congrArg
            (TraceCorQHom.add (TraceCorQHom.comp third post))
            (TraceCorQHom.sub_comp fourth tail post)))))

/-- Compose into a left-associated three-summand target sum with subtraction pushed last. -/
theorem TraceCorQHom.comp_add_add_sub
    {source middle target : TraceCorQObject}
    (pre : TraceCorQHom source middle)
    (first second third tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      pre
      (TraceCorQHom.sub
        (TraceCorQHom.add
          (TraceCorQHom.add first second)
          third)
        tail) =
      TraceCorQHom.add
        (TraceCorQHom.comp pre first)
        (TraceCorQHom.add
          (TraceCorQHom.comp pre second)
          (TraceCorQHom.sub
            (TraceCorQHom.comp pre third)
            (TraceCorQHom.comp pre tail))) :=
  Eq.trans
    (congrArg
      (TraceCorQHom.comp pre)
      (TraceCorQHom.add_add_sub first second third tail))
    (Eq.trans
      (TraceCorQHom.comp_add_add_right
        pre
        first
        second
        (TraceCorQHom.sub third tail))
      (congrArg
        (TraceCorQHom.add (TraceCorQHom.comp pre first))
        (congrArg
          (TraceCorQHom.add (TraceCorQHom.comp pre second))
          (TraceCorQHom.comp_sub pre third tail))))

/-- Compose into a right-associated three-summand target sum with subtraction pushed last. -/
theorem TraceCorQHom.comp_add_add_sub_right
    {source middle target : TraceCorQObject}
    (pre : TraceCorQHom source middle)
    (first second third tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      pre
      (TraceCorQHom.sub
        (TraceCorQHom.add
          first
          (TraceCorQHom.add second third))
        tail) =
      TraceCorQHom.add
        (TraceCorQHom.comp pre first)
        (TraceCorQHom.add
          (TraceCorQHom.comp pre second)
          (TraceCorQHom.sub
            (TraceCorQHom.comp pre third)
            (TraceCorQHom.comp pre tail))) :=
  Eq.trans
    (congrArg
      (TraceCorQHom.comp pre)
      (TraceCorQHom.add_add_sub_right first second third tail))
    (Eq.trans
      (TraceCorQHom.comp_add_add_right
        pre
        first
        second
        (TraceCorQHom.sub third tail))
      (congrArg
        (TraceCorQHom.add (TraceCorQHom.comp pre first))
        (congrArg
          (TraceCorQHom.add (TraceCorQHom.comp pre second))
          (TraceCorQHom.comp_sub pre third tail))))

/-- Compose into a fully left-associated four-summand target sum with subtraction pushed last. -/
theorem TraceCorQHom.comp_add_add_add_sub
    {source middle target : TraceCorQObject}
    (pre : TraceCorQHom source middle)
    (first second third fourth tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      pre
      (TraceCorQHom.sub
        (TraceCorQHom.add
          (TraceCorQHom.add
            (TraceCorQHom.add first second)
            third)
          fourth)
        tail) =
      TraceCorQHom.add
        (TraceCorQHom.comp pre first)
        (TraceCorQHom.add
          (TraceCorQHom.comp pre second)
          (TraceCorQHom.add
            (TraceCorQHom.comp pre third)
            (TraceCorQHom.sub
              (TraceCorQHom.comp pre fourth)
              (TraceCorQHom.comp pre tail)))) :=
  Eq.trans
    (congrArg
      (TraceCorQHom.comp pre)
      (TraceCorQHom.add_add_add_sub first second third fourth tail))
    (Eq.trans
      (TraceCorQHom.comp_add_add_add_right
        pre
        first
        second
        third
        (TraceCorQHom.sub fourth tail))
      (congrArg
        (TraceCorQHom.add (TraceCorQHom.comp pre first))
        (congrArg
          (TraceCorQHom.add (TraceCorQHom.comp pre second))
          (congrArg
            (TraceCorQHom.add (TraceCorQHom.comp pre third))
            (TraceCorQHom.comp_sub pre fourth tail)))))

/-- Compose into a fully right-associated four-summand target sum with subtraction pushed last. -/
theorem TraceCorQHom.comp_add_add_add_sub_right
    {source middle target : TraceCorQObject}
    (pre : TraceCorQHom source middle)
    (first second third fourth tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      pre
      (TraceCorQHom.sub
        (TraceCorQHom.add
          first
          (TraceCorQHom.add
            second
            (TraceCorQHom.add third fourth)))
        tail) =
      TraceCorQHom.add
        (TraceCorQHom.comp pre first)
        (TraceCorQHom.add
          (TraceCorQHom.comp pre second)
          (TraceCorQHom.add
            (TraceCorQHom.comp pre third)
            (TraceCorQHom.sub
              (TraceCorQHom.comp pre fourth)
              (TraceCorQHom.comp pre tail)))) :=
  Eq.trans
    (congrArg
      (TraceCorQHom.comp pre)
      (TraceCorQHom.add_add_add_sub_right first second third fourth tail))
    (Eq.trans
      (TraceCorQHom.comp_add_add_add_right
        pre
        first
        second
        third
        (TraceCorQHom.sub fourth tail))
      (congrArg
        (TraceCorQHom.add (TraceCorQHom.comp pre first))
        (congrArg
          (TraceCorQHom.add (TraceCorQHom.comp pre second))
          (congrArg
            (TraceCorQHom.add (TraceCorQHom.comp pre third))
            (TraceCorQHom.comp_sub pre fourth tail)))))

end AnalyticMotives
end LFunctions
end Boundary
