import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Associativity.Ambient.Owner

/-!
# Typed associativity owner for trace-correspondence composition

This file owns typed associativity for trace-correspondence composition.

The dependency order is ambient associativity first, then the relation-level
typed witness that identifies the two associated typed representatives.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-!
The next four lemmas keep the public associativity theorem from hiding the
actual typed quotient step.  The proof expands the two quotient compositions to
representatives, applies the ambient reassociation relation to those two
representatives, then contracts back to the right-associated typed composite.
-/

/-- Expand the left-associated typed composite to representative composition. -/
theorem TraceCorQHom.comp_assoc_left_expansion
    {first second third fourth : TraceCorQObject}
    (left : TraceCorQHomRepresentative first second)
    (middle : TraceCorQHomRepresentative second third)
    (right : TraceCorQHomRepresentative third fourth) :
    TraceCorQHom.comp
      (TraceCorQHom.comp
        (TraceCorQHom.ofRepresentative left)
        (TraceCorQHom.ofRepresentative middle))
      (TraceCorQHom.ofRepresentative right) =
      TraceCorQHom.ofRepresentative
        (TraceCorQHomRepresentative.comp
          (TraceCorQHomRepresentative.comp left middle)
          right) :=
  Eq.trans
    (congrArg
      (fun leftMiddle =>
        TraceCorQHom.comp
          leftMiddle
          (TraceCorQHom.ofRepresentative right))
      (TraceCorQHom.comp_ofRepresentative left middle))
    (TraceCorQHom.comp_ofRepresentative
      (TraceCorQHomRepresentative.comp left middle)
      right)

/-- Expand the right-associated typed composite to representative composition. -/
theorem TraceCorQHom.comp_assoc_right_expansion
    {first second third fourth : TraceCorQObject}
    (left : TraceCorQHomRepresentative first second)
    (middle : TraceCorQHomRepresentative second third)
    (right : TraceCorQHomRepresentative third fourth) :
    TraceCorQHom.comp
      (TraceCorQHom.ofRepresentative left)
      (TraceCorQHom.comp
        (TraceCorQHom.ofRepresentative middle)
        (TraceCorQHom.ofRepresentative right)) =
      TraceCorQHom.ofRepresentative
        (TraceCorQHomRepresentative.comp
          left
          (TraceCorQHomRepresentative.comp middle right)) :=
  Eq.trans
    (congrArg
      (fun middleRight =>
        TraceCorQHom.comp
          (TraceCorQHom.ofRepresentative left)
          middleRight)
      (TraceCorQHom.comp_ofRepresentative middle right))
    (TraceCorQHom.comp_ofRepresentative
      left
      (TraceCorQHomRepresentative.comp middle right))

/-- The two associated representative composites have equal ambient classes. -/
theorem TraceCorQHom.comp_assoc_representative_ambient_eq
    {first second third fourth : TraceCorQObject}
    (left : TraceCorQHomRepresentative first second)
    (middle : TraceCorQHomRepresentative second third)
    (right : TraceCorQHomRepresentative third fourth) :
    TraceCorQHom.ambient
      (TraceCorQHom.ofRepresentative
        (TraceCorQHomRepresentative.comp
          (TraceCorQHomRepresentative.comp left middle)
          right)) =
      TraceCorQHom.ambient
        (TraceCorQHom.ofRepresentative
          (TraceCorQHomRepresentative.comp
            left
            (TraceCorQHomRepresentative.comp middle right))) :=
  Eq.trans
    (Eq.symm
      (congrArg
        TraceCorQHom.ambient
        (TraceCorQHom.comp_assoc_left_expansion
          left
          middle
          right)))
    (Eq.trans
      (TraceCorQHom.ambient_comp_assoc
        (TraceCorQHom.ofRepresentative left)
        (TraceCorQHom.ofRepresentative middle)
        (TraceCorQHom.ofRepresentative right))
      (congrArg
        TraceCorQHom.ambient
        (TraceCorQHom.comp_assoc_right_expansion
          left
          middle
          right)))

/-- Reassociate representative composites as typed hom classes. -/
theorem TraceCorQHom.comp_assoc_representative_eq
    {first second third fourth : TraceCorQObject}
    (left : TraceCorQHomRepresentative first second)
    (middle : TraceCorQHomRepresentative second third)
    (right : TraceCorQHomRepresentative third fourth) :
    TraceCorQHom.ofRepresentative
      (TraceCorQHomRepresentative.comp
        (TraceCorQHomRepresentative.comp left middle)
        right) =
      TraceCorQHom.ofRepresentative
        (TraceCorQHomRepresentative.comp
          left
          (TraceCorQHomRepresentative.comp middle right)) :=
  TraceCorQHom.eq_of_ambient_eq
    (TraceCorQHom.comp_assoc_representative_ambient_eq
      left
      middle
      right)

/-- Associativity for three representative-backed typed hom classes. -/
theorem TraceCorQHom.comp_assoc_ofRepresentative
    {first second third fourth : TraceCorQObject}
    (left : TraceCorQHomRepresentative first second)
    (middle : TraceCorQHomRepresentative second third)
    (right : TraceCorQHomRepresentative third fourth) :
    TraceCorQHom.comp
      (TraceCorQHom.comp
        (TraceCorQHom.ofRepresentative left)
        (TraceCorQHom.ofRepresentative middle))
      (TraceCorQHom.ofRepresentative right) =
      TraceCorQHom.comp
        (TraceCorQHom.ofRepresentative left)
        (TraceCorQHom.comp
          (TraceCorQHom.ofRepresentative middle)
          (TraceCorQHom.ofRepresentative right)) :=
  Eq.trans
    (TraceCorQHom.comp_assoc_left_expansion left middle right)
    (Eq.trans
      (TraceCorQHom.comp_assoc_representative_eq left middle right)
      (Eq.symm
        (TraceCorQHom.comp_assoc_right_expansion left middle right)))

/-- Typed hom composition is associative. -/
theorem TraceCorQHom.comp_assoc
    {first second third fourth : TraceCorQObject}
    (left : TraceCorQHom first second)
    (middle : TraceCorQHom second third)
    (right : TraceCorQHom third fourth) :
    TraceCorQHom.comp
      (TraceCorQHom.comp left middle)
      right =
      TraceCorQHom.comp
        left
        (TraceCorQHom.comp middle right) :=
  Quotient.inductionOn₃
    left
    middle
    right
    (fun leftRepresentative middleRepresentative rightRepresentative =>
      TraceCorQHom.comp_assoc_ofRepresentative
        leftRepresentative
        middleRepresentative
        rightRepresentative)

end AnalyticMotives
end LFunctions
end Boundary
