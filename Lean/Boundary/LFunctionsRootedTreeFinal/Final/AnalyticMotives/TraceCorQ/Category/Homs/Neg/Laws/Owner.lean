import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Neg.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Neg.Laws.Owner

/-!
# Negation laws for typed trace-correspondence hom classes

This file starts the typed additive inverse theory from the concrete singleton
cancellation law in the ambient quotient.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Negating the zero typed hom gives zero. -/
theorem TraceCorQHom.neg_zero
    (source target : TraceCorQObject) :
    TraceCorQHom.neg
      (TraceCorQHom.zero source target) =
      TraceCorQHom.zero source target :=
  TraceCorQHom.smul_zero source target (-1)

/-- Negation distributes over typed hom addition. -/
theorem TraceCorQHom.neg_add
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    TraceCorQHom.neg
      (TraceCorQHom.add left right) =
      TraceCorQHom.add
        (TraceCorQHom.neg left)
        (TraceCorQHom.neg right) :=
  TraceCorQHom.smul_add (-1) left right

/-- Typed hom negation is involutive. -/
theorem TraceCorQHom.neg_neg
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.neg
      (TraceCorQHom.neg hom) =
      hom :=
  Eq.trans
    (TraceCorQHom.smul_smul
      (-1)
      (-1)
      hom)
    (Eq.trans
      (congrArg
        (fun coefficient =>
          TraceCorQHom.smul coefficient hom)
        TraceCorQ.neg_one_mul_neg_one)
      (TraceCorQHom.one_smul hom))

/-- Every typed hom has its negation as a left additive inverse. -/
theorem TraceCorQHom.neg_add_self
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.add
      (TraceCorQHom.neg hom)
      hom =
      TraceCorQHom.zero source target :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_add
        (TraceCorQHom.neg hom)
        hom)
      (Eq.trans
        (congrArg
          (fun leftClass =>
            TraceCorQQuotient.add
              leftClass
              (TraceCorQHom.ambient hom))
          (TraceCorQHom.ambient_neg hom))
        (Eq.trans
          (TraceCorQQuotient.neg_add_self
            (TraceCorQHom.ambient hom))
          (Eq.symm
            (TraceCorQHom.ambient_zero source target)))))

/-- Every typed hom has its negation as a right additive inverse. -/
theorem TraceCorQHom.add_neg_self
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.add
      hom
      (TraceCorQHom.neg hom) =
      TraceCorQHom.zero source target :=
  Eq.trans
    (TraceCorQHom.add_comm hom (TraceCorQHom.neg hom))
    (TraceCorQHom.neg_add_self hom)

/-- Typed hom addition cancels a common left summand. -/
theorem TraceCorQHom.add_left_cancel
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_right_eq_left_tail :
      TraceCorQHom.add left right =
        TraceCorQHom.add left tail) :
    right = tail :=
  Eq.trans
    (Eq.symm (TraceCorQHom.zero_add right))
    (Eq.trans
      (congrArg
        (fun zeroHom =>
          TraceCorQHom.add zeroHom right)
        (Eq.symm (TraceCorQHom.neg_add_self left)))
      (Eq.trans
        (TraceCorQHom.add_assoc
          (TraceCorQHom.neg left)
          left
          right)
        (Eq.trans
          (congrArg
            (TraceCorQHom.add (TraceCorQHom.neg left))
            left_right_eq_left_tail)
          (Eq.trans
            (Eq.symm
              (TraceCorQHom.add_assoc
                (TraceCorQHom.neg left)
                left
                tail))
            (Eq.trans
              (congrArg
                (fun zeroHom =>
                  TraceCorQHom.add zeroHom tail)
                (TraceCorQHom.neg_add_self left))
              (TraceCorQHom.zero_add tail))))))

/-- Typed hom addition cancels a common right summand. -/
theorem TraceCorQHom.add_right_cancel
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_tail_eq_right_tail :
      TraceCorQHom.add left tail =
        TraceCorQHom.add right tail) :
    left = right :=
  TraceCorQHom.add_left_cancel
    tail
    left
    right
    (Eq.trans
      (TraceCorQHom.add_comm tail left)
      (Eq.trans
        left_tail_eq_right_tail
        (TraceCorQHom.add_comm right tail)))

/-- A negative typed singleton plus the singleton itself cancels. -/
theorem TraceCorQHom.neg_singleton_add_singleton
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    TraceCorQHom.add
      (TraceCorQHom.singleton
        source
        target
        (-coefficient)
        generator
        source_eq
        target_eq)
      (TraceCorQHom.singleton
        source
        target
        coefficient
        generator
        source_eq
        target_eq) =
      TraceCorQHom.zero source target :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_add
        (TraceCorQHom.singleton
          source
          target
          (-coefficient)
          generator
          source_eq
          target_eq)
        (TraceCorQHom.singleton
          source
          target
          coefficient
          generator
          source_eq
          target_eq))
      (Eq.trans
        (congrArg
          (fun leftClass =>
            TraceCorQQuotient.add
              leftClass
              (TraceCorQHom.ambient
                (TraceCorQHom.singleton
                  source
                  target
                  coefficient
                  generator
                  source_eq
                  target_eq)))
          (TraceCorQHom.ambient_singleton
            source
            target
            (-coefficient)
            generator
            source_eq
            target_eq))
        (Eq.trans
          (congrArg
            (fun rightClass =>
              TraceCorQQuotient.add
                (TraceCorQQuotient.singleton (-coefficient) generator)
                rightClass)
            (TraceCorQHom.ambient_singleton
              source
              target
              coefficient
              generator
              source_eq
              target_eq))
          (Eq.trans
            (TraceCorQQuotient.neg_singleton_add_singleton
              coefficient
              generator)
            (Eq.symm
              (TraceCorQHom.ambient_zero source target))))))

/-- A typed singleton plus its negative cancels. -/
theorem TraceCorQHom.singleton_add_neg_singleton
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    TraceCorQHom.add
      (TraceCorQHom.singleton
        source
        target
        coefficient
        generator
        source_eq
        target_eq)
      (TraceCorQHom.singleton
        source
        target
        (-coefficient)
        generator
        source_eq
        target_eq) =
      TraceCorQHom.zero source target :=
  Eq.trans
    (TraceCorQHom.add_comm
      (TraceCorQHom.singleton
        source
        target
        coefficient
        generator
        source_eq
        target_eq)
      (TraceCorQHom.singleton
        source
        target
        (-coefficient)
        generator
        source_eq
        target_eq))
    (TraceCorQHom.neg_singleton_add_singleton
      source
      target
      coefficient
      generator
      source_eq
      target_eq)

end AnalyticMotives
end LFunctions
end Boundary
