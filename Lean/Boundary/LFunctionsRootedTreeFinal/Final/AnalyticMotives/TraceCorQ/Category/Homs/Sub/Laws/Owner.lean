import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Neg.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Laws.Owner

/-!
# Subtraction laws for typed trace-correspondence hom classes

This file proves basic typed subtraction laws from the concrete definition
`left + neg right`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Subtracting zero on the right leaves a typed hom unchanged. -/
theorem TraceCorQHom.sub_zero
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.sub hom (TraceCorQHom.zero source target) =
      hom :=
  Eq.trans
    (TraceCorQHom.sub_eq_add_neg
      hom
      (TraceCorQHom.zero source target))
    (Eq.trans
      (congrArg
        (TraceCorQHom.add hom)
        (TraceCorQHom.neg_zero source target))
      (TraceCorQHom.add_zero hom))

/-- Zero minus a typed hom is its negative. -/
theorem TraceCorQHom.zero_sub
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.sub (TraceCorQHom.zero source target) hom =
      TraceCorQHom.neg hom :=
  Eq.trans
    (TraceCorQHom.sub_eq_add_neg
      (TraceCorQHom.zero source target)
      hom)
    (TraceCorQHom.zero_add (TraceCorQHom.neg hom))

/-- A typed hom minus itself is zero. -/
theorem TraceCorQHom.sub_self
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.sub hom hom =
      TraceCorQHom.zero source target :=
  Eq.trans
    (TraceCorQHom.sub_eq_add_neg hom hom)
    (TraceCorQHom.add_neg_self hom)

/-- Equal typed homs have zero subtraction. -/
theorem TraceCorQHom.sub_eq_zero_of_eq
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target)
    (left_eq_right : left = right) :
    TraceCorQHom.sub left right =
      TraceCorQHom.zero source target :=
  Eq.trans
    (congrArg
      (fun leftHom =>
        TraceCorQHom.sub leftHom right)
      left_eq_right)
    (TraceCorQHom.sub_self right)

/-- Zero subtraction detects equality of typed homs. -/
theorem TraceCorQHom.eq_of_sub_eq_zero
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target)
    (left_sub_right_eq_zero :
      TraceCorQHom.sub left right =
        TraceCorQHom.zero source target) :
    left = right :=
  Eq.trans
    (Eq.symm (TraceCorQHom.add_zero left))
    (Eq.trans
      (congrArg
        (TraceCorQHom.add left)
        (Eq.symm (TraceCorQHom.neg_add_self right)))
      (Eq.trans
        (Eq.symm
          (TraceCorQHom.add_assoc
            left
            (TraceCorQHom.neg right)
            right))
        (Eq.trans
          (congrArg
            (fun leftMinusRight =>
              TraceCorQHom.add leftMinusRight right)
            (Eq.trans
              (Eq.symm
                (TraceCorQHom.sub_eq_add_neg left right))
              left_sub_right_eq_zero))
          (TraceCorQHom.zero_add right))))

/-- Move a right summand across an equality of typed homs. -/
theorem TraceCorQHom.left_eq_sub_of_add_eq
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_add_right_eq_tail :
      TraceCorQHom.add left right = tail) :
    left = TraceCorQHom.sub tail right :=
  Eq.trans
    (Eq.symm (TraceCorQHom.add_zero left))
    (Eq.trans
      (congrArg
        (TraceCorQHom.add left)
        (Eq.symm (TraceCorQHom.add_neg_self right)))
      (Eq.trans
        (Eq.symm
          (TraceCorQHom.add_assoc
            left
            right
            (TraceCorQHom.neg right)))
        (Eq.trans
          (congrArg
            (fun leftRight =>
              TraceCorQHom.add
                leftRight
                (TraceCorQHom.neg right))
            left_add_right_eq_tail)
          (Eq.symm
            (TraceCorQHom.sub_eq_add_neg tail right)))))

/-- Move a left summand across an equality of typed homs. -/
theorem TraceCorQHom.right_eq_sub_of_add_eq
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_add_right_eq_tail :
      TraceCorQHom.add left right = tail) :
    right = TraceCorQHom.sub tail left :=
  TraceCorQHom.left_eq_sub_of_add_eq
    right
    left
    tail
    (Eq.trans
      (TraceCorQHom.add_comm right left)
      left_add_right_eq_tail)

/-- Rebuild a typed hom sum from a left-subtraction solution. -/
theorem TraceCorQHom.add_eq_of_left_eq_sub
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_eq_tail_sub_right :
      left = TraceCorQHom.sub tail right) :
    TraceCorQHom.add left right = tail :=
  Eq.trans
    (congrArg
      (fun leftHom =>
        TraceCorQHom.add leftHom right)
      left_eq_tail_sub_right)
    (Eq.trans
      (congrArg
        (fun tailSubRight =>
          TraceCorQHom.add tailSubRight right)
        (TraceCorQHom.sub_eq_add_neg tail right))
      (Eq.trans
        (TraceCorQHom.add_assoc
          tail
          (TraceCorQHom.neg right)
          right)
        (Eq.trans
          (congrArg
            (TraceCorQHom.add tail)
            (TraceCorQHom.neg_add_self right))
          (TraceCorQHom.add_zero tail))))

/-- Rebuild a typed hom sum from a right-subtraction solution. -/
theorem TraceCorQHom.add_eq_of_right_eq_sub
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (right_eq_tail_sub_left :
      right = TraceCorQHom.sub tail left) :
    TraceCorQHom.add left right = tail :=
  Eq.trans
    (TraceCorQHom.add_comm left right)
    (TraceCorQHom.add_eq_of_left_eq_sub
      right
      left
      tail
      right_eq_tail_sub_left)

/-- Typed hom subtraction cancels a common right-hand subtrahend. -/
theorem TraceCorQHom.sub_right_cancel
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_sub_tail_eq_right_sub_tail :
      TraceCorQHom.sub left tail =
        TraceCorQHom.sub right tail) :
    left = right :=
  TraceCorQHom.add_right_cancel
    left
    right
    (TraceCorQHom.neg tail)
    (Eq.trans
      (Eq.symm (TraceCorQHom.sub_eq_add_neg left tail))
      (Eq.trans
        left_sub_tail_eq_right_sub_tail
        (TraceCorQHom.sub_eq_add_neg right tail)))

/-- Typed hom subtraction cancels a common left-hand minuend. -/
theorem TraceCorQHom.sub_left_cancel
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_sub_right_eq_left_sub_tail :
      TraceCorQHom.sub left right =
        TraceCorQHom.sub left tail) :
    right = tail :=
  Eq.trans
    (Eq.symm (TraceCorQHom.neg_neg right))
    (Eq.trans
      (congrArg
        TraceCorQHom.neg
        (TraceCorQHom.add_left_cancel
          left
          (TraceCorQHom.neg right)
          (TraceCorQHom.neg tail)
          (Eq.trans
            (Eq.symm (TraceCorQHom.sub_eq_add_neg left right))
            (Eq.trans
              left_sub_right_eq_left_sub_tail
              (TraceCorQHom.sub_eq_add_neg left tail)))))
      (TraceCorQHom.neg_neg tail))

/-- Negating typed hom subtraction reverses its two terms. -/
theorem TraceCorQHom.neg_sub
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    TraceCorQHom.neg
      (TraceCorQHom.sub left right) =
      TraceCorQHom.sub right left :=
  Eq.trans
    (congrArg
      TraceCorQHom.neg
      (TraceCorQHom.sub_eq_add_neg left right))
    (Eq.trans
      (TraceCorQHom.neg_add left (TraceCorQHom.neg right))
      (Eq.trans
        (congrArg
          (TraceCorQHom.add (TraceCorQHom.neg left))
          (TraceCorQHom.neg_neg right))
        (Eq.trans
          (TraceCorQHom.add_comm
            (TraceCorQHom.neg left)
            right)
          (Eq.symm
            (TraceCorQHom.sub_eq_add_neg right left)))))

/-- Subtraction from a typed hom sum reassociates through the right summand. -/
theorem TraceCorQHom.add_sub
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target) :
    TraceCorQHom.sub
      (TraceCorQHom.add left right)
      tail =
      TraceCorQHom.add
        left
        (TraceCorQHom.sub right tail) :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_sub
        (TraceCorQHom.add left right)
        tail)
      (Eq.trans
        (congrArg
          (fun leftRightClass =>
            TraceCorQQuotient.sub
              leftRightClass
              (TraceCorQHom.ambient tail))
          (TraceCorQHom.ambient_add left right))
        (Eq.trans
          (TraceCorQQuotient.add_sub
            (TraceCorQHom.ambient left)
            (TraceCorQHom.ambient right)
            (TraceCorQHom.ambient tail))
          (Eq.symm
            (Eq.trans
              (TraceCorQHom.ambient_add
                left
                (TraceCorQHom.sub right tail))
              (congrArg
                (TraceCorQQuotient.add
                  (TraceCorQHom.ambient left))
                (TraceCorQHom.ambient_sub right tail)))))))

/-- Subtracting a typed hom sum reassociates as iterated subtraction. -/
theorem TraceCorQHom.sub_add
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target) :
    TraceCorQHom.sub
      left
      (TraceCorQHom.add right tail) =
      TraceCorQHom.sub
        (TraceCorQHom.sub left right)
        tail :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_sub
        left
        (TraceCorQHom.add right tail))
      (Eq.trans
        (congrArg
          (TraceCorQQuotient.sub (TraceCorQHom.ambient left))
          (TraceCorQHom.ambient_add right tail))
        (Eq.trans
          (TraceCorQQuotient.sub_add
            (TraceCorQHom.ambient left)
            (TraceCorQHom.ambient right)
            (TraceCorQHom.ambient tail))
          (Eq.symm
            (Eq.trans
              (TraceCorQHom.ambient_sub
                (TraceCorQHom.sub left right)
                tail)
              (congrArg
                (fun leftMinusRightClass =>
                  TraceCorQQuotient.sub
                    leftMinusRightClass
                    (TraceCorQHom.ambient tail))
                (TraceCorQHom.ambient_sub left right)))))))

/-- Subtracting a typed hom subtraction reassociates through addition. -/
theorem TraceCorQHom.sub_sub
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target) :
    TraceCorQHom.sub
      left
      (TraceCorQHom.sub right tail) =
      TraceCorQHom.add
        (TraceCorQHom.sub left right)
        tail :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_sub
        left
        (TraceCorQHom.sub right tail))
      (Eq.trans
        (congrArg
          (TraceCorQQuotient.sub (TraceCorQHom.ambient left))
          (TraceCorQHom.ambient_sub right tail))
        (Eq.trans
          (TraceCorQQuotient.sub_sub
            (TraceCorQHom.ambient left)
            (TraceCorQHom.ambient right)
            (TraceCorQHom.ambient tail))
          (Eq.symm
            (Eq.trans
              (TraceCorQHom.ambient_add
                (TraceCorQHom.sub left right)
                tail)
              (congrArg
                (fun leftMinusRightClass =>
                  TraceCorQQuotient.add
                    leftMinusRightClass
                    (TraceCorQHom.ambient tail))
                (TraceCorQHom.ambient_sub left right)))))))

/-- Scalar multiplication distributes over typed hom subtraction. -/
theorem TraceCorQHom.smul_sub
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (left right : TraceCorQHom source target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.sub left right) =
      TraceCorQHom.sub
        (TraceCorQHom.smul coefficient left)
        (TraceCorQHom.smul coefficient right) :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_smul
        coefficient
        (TraceCorQHom.sub left right))
      (Eq.trans
        (congrArg
          (TraceCorQQuotient.smul coefficient)
          (TraceCorQHom.ambient_sub left right))
        (Eq.trans
          (TraceCorQQuotient.smul_sub
            coefficient
            (TraceCorQHom.ambient left)
            (TraceCorQHom.ambient right))
          (Eq.symm
            (Eq.trans
              (TraceCorQHom.ambient_sub
                (TraceCorQHom.smul coefficient left)
                (TraceCorQHom.smul coefficient right))
              (Eq.trans
                (congrArg
                  (fun leftClass =>
                    TraceCorQQuotient.sub
                      leftClass
                      (TraceCorQHom.ambient
                        (TraceCorQHom.smul coefficient right)))
                  (TraceCorQHom.ambient_smul coefficient left))
                (congrArg
                  (fun rightClass =>
                    TraceCorQQuotient.sub
                      (TraceCorQQuotient.smul
                        coefficient
                        (TraceCorQHom.ambient left))
                      rightClass)
                  (TraceCorQHom.ambient_smul coefficient right))))))))

/-- A typed singleton minus itself is zero. -/
theorem TraceCorQHom.singleton_sub_self
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    TraceCorQHom.sub
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
        coefficient
        generator
        source_eq
        target_eq) =
      TraceCorQHom.zero source target :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_sub
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
          coefficient
          generator
          source_eq
          target_eq))
      (Eq.trans
        (congrArg
          (fun leftClass =>
            TraceCorQQuotient.sub
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
            coefficient
            generator
            source_eq
            target_eq))
        (Eq.trans
          (congrArg
            (fun rightClass =>
              TraceCorQQuotient.sub
                (TraceCorQQuotient.singleton coefficient generator)
                rightClass)
            (TraceCorQHom.ambient_singleton
              source
              target
              coefficient
              generator
              source_eq
              target_eq))
          (Eq.trans
            (TraceCorQQuotient.singleton_sub_self
              coefficient
              generator)
            (Eq.symm
              (TraceCorQHom.ambient_zero source target))))))

end AnalyticMotives
end LFunctions
end Boundary
