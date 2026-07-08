import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Laws.Basic.Owner

/-!
# Subtraction laws for typed trace-correspondence hom classes

This file proves reassociation and scalar laws for typed subtraction from the
basic solver and cancellation laws.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

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
