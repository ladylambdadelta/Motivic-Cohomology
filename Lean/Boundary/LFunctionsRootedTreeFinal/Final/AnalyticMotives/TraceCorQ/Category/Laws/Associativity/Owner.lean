import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Associativity.Ambient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Associativity.Typed.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Associativity.Full.Owner

/-!
# Associativity laws for typed trace-correspondence composition

This aggregate owns the associativity lane for typed trace correspondences:
ambient quotient expansion, typed reassociation, and full fourfold
normalization.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Associativity aggregate: ambient left-associated expansion. -/
theorem TraceCorQCategoryAssociativity.ambient_left_expansion
    {first second third fourth : TraceCorQObject}
    (left : TraceCorQHom first second)
    (middle : TraceCorQHom second third)
    (right : TraceCorQHom third fourth) :
    TraceCorQHom.ambient
      (TraceCorQHom.comp
        (TraceCorQHom.comp left middle)
        right) =
      TraceCorQQuotient.comp
        (TraceCorQQuotient.comp
          (TraceCorQHom.ambient left)
          (TraceCorQHom.ambient middle))
        (TraceCorQHom.ambient right) :=
  TraceCorQHom.ambient_comp_assoc_left_expansion
    left
    middle
    right

/-- Associativity aggregate: ambient right-associated expansion. -/
theorem TraceCorQCategoryAssociativity.ambient_right_expansion
    {first second third fourth : TraceCorQObject}
    (left : TraceCorQHom first second)
    (middle : TraceCorQHom second third)
    (right : TraceCorQHom third fourth) :
    TraceCorQHom.ambient
      (TraceCorQHom.comp
        left
        (TraceCorQHom.comp middle right)) =
      TraceCorQQuotient.comp
        (TraceCorQHom.ambient left)
        (TraceCorQQuotient.comp
          (TraceCorQHom.ambient middle)
          (TraceCorQHom.ambient right)) :=
  TraceCorQHom.ambient_comp_assoc_right_expansion
    left
    middle
    right

/-- Associativity aggregate: ambient typed composition is associative. -/
theorem TraceCorQCategoryAssociativity.ambient_assoc
    {first second third fourth : TraceCorQObject}
    (left : TraceCorQHom first second)
    (middle : TraceCorQHom second third)
    (right : TraceCorQHom third fourth) :
    TraceCorQHom.ambient
      (TraceCorQHom.comp
        (TraceCorQHom.comp left middle)
        right) =
      TraceCorQHom.ambient
        (TraceCorQHom.comp
          left
          (TraceCorQHom.comp middle right)) :=
  TraceCorQHom.ambient_comp_assoc
    left
    middle
    right

/-- Associativity aggregate: representative composites reassociate. -/
theorem TraceCorQCategoryAssociativity.representative_eq
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
  TraceCorQHom.comp_assoc_representative_eq
    left
    middle
    right

/-- Associativity aggregate: representative-backed typed homs compose associatively. -/
theorem TraceCorQCategoryAssociativity.ofRepresentative
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
  TraceCorQHom.comp_assoc_ofRepresentative
    left
    middle
    right

/-- Associativity aggregate: typed trace-correspondence composition is associative. -/
theorem TraceCorQCategoryAssociativity.assoc
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
  TraceCorQHom.comp_assoc
    left
    middle
    right

/-- Associativity aggregate: fully left-associated fourfold composites normalize. -/
theorem TraceCorQCategoryAssociativity.four_left
    {first second third fourth fifth : TraceCorQObject}
    (firstMap : TraceCorQHom first second)
    (secondMap : TraceCorQHom second third)
    (thirdMap : TraceCorQHom third fourth)
    (fourthMap : TraceCorQHom fourth fifth) :
    TraceCorQHom.comp
      (TraceCorQHom.comp
        (TraceCorQHom.comp firstMap secondMap)
        thirdMap)
      fourthMap =
      TraceCorQHom.comp
        firstMap
        (TraceCorQHom.comp
          secondMap
          (TraceCorQHom.comp thirdMap fourthMap)) :=
  TraceCorQHom.comp_assoc_four_left
    firstMap
    secondMap
    thirdMap
    fourthMap

/-- Associativity aggregate: binary-split fourfold composites normalize. -/
theorem TraceCorQCategoryAssociativity.four_binary
    {first second third fourth fifth : TraceCorQObject}
    (firstMap : TraceCorQHom first second)
    (secondMap : TraceCorQHom second third)
    (thirdMap : TraceCorQHom third fourth)
    (fourthMap : TraceCorQHom fourth fifth) :
    TraceCorQHom.comp
      (TraceCorQHom.comp firstMap secondMap)
      (TraceCorQHom.comp thirdMap fourthMap) =
      TraceCorQHom.comp
        firstMap
        (TraceCorQHom.comp
          secondMap
          (TraceCorQHom.comp thirdMap fourthMap)) :=
  TraceCorQHom.comp_assoc_four_binary
    firstMap
    secondMap
    thirdMap
    fourthMap

end AnalyticMotives
end LFunctions
end Boundary
