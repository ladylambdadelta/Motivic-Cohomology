import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Composition.Quotient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.QuotientOperations.Owner

/-!
# Quotient composition laws

This owner records the zero, additive, and scalar laws for composition on
quotient homs modulo finite reindexing.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQFormalSum

/-- Quotient composition with a zero left input is zero. -/
theorem compClass_zero_left
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (B : QuotientHom Y Z) :
    compClass C (zeroClass X Y) B = zeroClass X Z :=
  Quotient.inductionOn B
    (fun T =>
      Eq.trans
        (compClass_quotientClass C (ContourCorQFormalSum.zero X Y) T)
        (Quotient.sound
          (Nonempty.intro
            (ContourCorQFormalSumReindexing.comp_zero_left C T))))

/-- Quotient composition with a zero right input is zero. -/
theorem compClass_zero_right
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (A : QuotientHom X Y) :
    compClass C A (zeroClass Y Z) = zeroClass X Z :=
  Quotient.inductionOn A
    (fun S =>
      Eq.trans
        (compClass_quotientClass C S (ContourCorQFormalSum.zero Y Z))
        (Quotient.sound
          (Nonempty.intro
            (ContourCorQFormalSumReindexing.comp_zero_right C S))))

/-- Quotient composition is additive in the left input. -/
theorem compClass_add_left
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (A₁ A₂ : QuotientHom X Y)
    (B : QuotientHom Y Z) :
    compClass C (addClass A₁ A₂) B =
      addClass (compClass C A₁ B) (compClass C A₂ B) :=
  Quotient.inductionOn A₁
    (fun S₁ =>
      Quotient.inductionOn A₂
        (fun S₂ =>
          Quotient.inductionOn B
            (fun T =>
              Eq.trans
                (congrArg
                  (fun A => compClass C A (quotientClass T))
                  (addClass_quotientClass S₁ S₂))
                (Eq.trans
                  (compClass_quotientClass
                    C (ContourCorQFormalSum.add S₁ S₂) T)
                  (Eq.trans
                    (Quotient.sound
                      (Nonempty.intro
                        (ContourCorQFormalSumReindexing.comp_add_left
                          C S₁ S₂ T)))
                    (Eq.symm
                      (addClass_quotientClass
                        (ContourCorQFormalSum.comp C S₁ T)
                        (ContourCorQFormalSum.comp C S₂ T))))))))

/-- Quotient composition is additive in the right input. -/
theorem compClass_add_right
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (A : QuotientHom X Y)
    (B₁ B₂ : QuotientHom Y Z) :
    compClass C A (addClass B₁ B₂) =
      addClass (compClass C A B₁) (compClass C A B₂) :=
  Quotient.inductionOn A
    (fun S =>
      Quotient.inductionOn B₁
        (fun T₁ =>
          Quotient.inductionOn B₂
            (fun T₂ =>
              Eq.trans
                (congrArg
                  (fun B => compClass C (quotientClass S) B)
                  (addClass_quotientClass T₁ T₂))
                (Eq.trans
                  (compClass_quotientClass
                    C S (ContourCorQFormalSum.add T₁ T₂))
                  (Eq.trans
                    (Quotient.sound
                      (Nonempty.intro
                        (ContourCorQFormalSumReindexing.comp_add_right
                          C S T₁ T₂)))
                    (Eq.symm
                      (addClass_quotientClass
                        (ContourCorQFormalSum.comp C S T₁)
                        (ContourCorQFormalSum.comp C S T₂))))))))

/-- Quotient composition is compatible with left scalar multiplication. -/
theorem compClass_scale_left
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (q : Rat)
    (A : QuotientHom X Y)
    (B : QuotientHom Y Z) :
    compClass C (scaleClass q A) B =
      scaleClass q (compClass C A B) :=
  Quotient.inductionOn A
    (fun S =>
      Quotient.inductionOn B
        (fun T =>
          Eq.trans
            (congrArg
              (fun A0 => compClass C A0 (quotientClass T))
              (scaleClass_quotientClass q S))
            (Eq.trans
              (compClass_quotientClass
                C (ContourCorQFormalSum.scale q S) T)
              (Eq.trans
                (Quotient.sound
                  (Nonempty.intro
                    (ContourCorQFormalSumReindexing.comp_scale_left
                      C q S T)))
                (Eq.symm
                  (scaleClass_quotientClass
                    q (ContourCorQFormalSum.comp C S T)))))))

/-- Quotient composition is compatible with right scalar multiplication. -/
theorem compClass_scale_right
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (q : Rat)
    (A : QuotientHom X Y)
    (B : QuotientHom Y Z) :
    compClass C A (scaleClass q B) =
      scaleClass q (compClass C A B) :=
  Quotient.inductionOn A
    (fun S =>
      Quotient.inductionOn B
        (fun T =>
          Eq.trans
            (congrArg
              (fun B0 => compClass C (quotientClass S) B0)
              (scaleClass_quotientClass q T))
            (Eq.trans
              (compClass_quotientClass
                C S (ContourCorQFormalSum.scale q T))
              (Eq.trans
                (Quotient.sound
                  (Nonempty.intro
                    (ContourCorQFormalSumReindexing.comp_scale_right
                      C q S T)))
                (Eq.symm
                  (scaleClass_quotientClass
                    q (ContourCorQFormalSum.comp C S T)))))))

/-- Quotient composition is compatible with negation in the left input. -/
theorem compClass_neg_left
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (A : QuotientHom X Y)
    (B : QuotientHom Y Z) :
    compClass C (negClass A) B =
      negClass (compClass C A B) :=
  compClass_scale_left C (-1) A B

/-- Quotient composition is compatible with negation in the right input. -/
theorem compClass_neg_right
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (A : QuotientHom X Y)
    (B : QuotientHom Y Z) :
    compClass C A (negClass B) =
      negClass (compClass C A B) :=
  compClass_scale_right C (-1) A B

/-- Quotient composition expands subtraction in the left input. -/
theorem compClass_sub_left
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (A₁ A₂ : QuotientHom X Y)
    (B : QuotientHom Y Z) :
    compClass C (subClass A₁ A₂) B =
      addClass (compClass C A₁ B) (negClass (compClass C A₂ B)) :=
  Eq.trans
    (compClass_add_left C A₁ (negClass A₂) B)
    (congrArg
      (fun R =>
        addClass (compClass C A₁ B) R)
      (compClass_neg_left C A₂ B))

/-- Quotient composition expands subtraction in the right input. -/
theorem compClass_sub_right
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (A : QuotientHom X Y)
    (B₁ B₂ : QuotientHom Y Z) :
    compClass C A (subClass B₁ B₂) =
      addClass (compClass C A B₁) (negClass (compClass C A B₂)) :=
  Eq.trans
    (compClass_add_right C A B₁ (negClass B₂))
    (congrArg
      (fun R =>
        addClass (compClass C A B₁) R)
      (compClass_neg_right C A B₂))

end ContourCorQFormalSum

end AnalyticMotives
end LFunctions
end Boundary
