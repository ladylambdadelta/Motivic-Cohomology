import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Composition.Basic.Term.Owner

/-!
# Formal-sum composition

This file owns bilinear composition of raw formal `Q`-linear
trace-correspondence sums and the composition laws used by quotient and
category layers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Compose formal sums by the finite bilinear expansion on generators. -/
def TraceCorQFormalSum.comp
    (left right : TraceCorQFormalSum) :
    TraceCorQFormalSum :=
  left.bind
    (fun leftTerm => TraceCorQTerm.compRight leftTerm right)

/-- Adding the zero formal sum on the left leaves a formal sum unchanged. -/
theorem TraceCorQFormalSum.zero_add
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.add
      TraceCorQFormalSum.zero
      formalSum =
      formalSum :=
  rfl

/-- Adding the zero formal sum on the right leaves a formal sum unchanged. -/
theorem TraceCorQFormalSum.add_zero
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.add
      formalSum
      TraceCorQFormalSum.zero =
      formalSum :=
  List.append_nil formalSum

/-- Addition of formal trace-correspondence sums is associative. -/
theorem TraceCorQFormalSum.add_assoc
    (first second third : TraceCorQFormalSum) :
    TraceCorQFormalSum.add
      (TraceCorQFormalSum.add first second)
      third =
      TraceCorQFormalSum.add
        first
        (TraceCorQFormalSum.add second third) :=
  List.append_assoc first second third

/-- Composing the zero formal sum on the left gives zero. -/
theorem TraceCorQFormalSum.zero_comp
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      TraceCorQFormalSum.zero
      formalSum =
      TraceCorQFormalSum.zero :=
  rfl

/-- Composing the zero formal sum on the left carries the empty certificate ledger. -/
theorem TraceCorQFormalSum.zero_comp_certificateLedger
    (formalSum : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      TraceCorQFormalSum.zero
      formalSum).certificateLedger =
      ResidueChannelCertificateLedger.empty :=
  rfl

/-- Composing the zero formal sum on the left carries no rewrite-step payload. -/
theorem TraceCorQFormalSum.zero_comp_rewriteStepCount
    (formalSum : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      TraceCorQFormalSum.zero
      formalSum).rewriteStepCount =
      0 :=
  rfl

/-- Composing a formal term on the right with the zero formal sum gives zero. -/
theorem TraceCorQTerm.compRight_zero
    (term : TraceCorQTerm) :
    TraceCorQTerm.compRight term TraceCorQFormalSum.zero =
      TraceCorQFormalSum.zero :=
  rfl

/-- The certificate ledger of formal composition with a cons left side splits by the head term. -/
theorem TraceCorQFormalSum.comp_cons_left_certificateLedger
    (leftTerm : TraceCorQTerm)
    (leftTail right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      (leftTerm :: leftTail)
      right).certificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceCorQTerm.compRight leftTerm right).certificateLedger
        (TraceCorQFormalSum.comp leftTail right).certificateLedger :=
  TraceCorQFormalSum.add_certificateLedger
    (TraceCorQTerm.compRight leftTerm right)
    (TraceCorQFormalSum.comp leftTail right)

/-- The rewrite-step payload of formal composition with a cons left side splits by the head term. -/
theorem TraceCorQFormalSum.comp_cons_left_rewriteStepCount
    (leftTerm : TraceCorQTerm)
    (leftTail right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.comp
      (leftTerm :: leftTail)
      right).rewriteStepCount =
      (TraceCorQTerm.compRight leftTerm right).rewriteStepCount +
        (TraceCorQFormalSum.comp leftTail right).rewriteStepCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.rewriteStepCount
      (TraceCorQFormalSum.comp_cons_left_certificateLedger
        leftTerm
        leftTail
        right))
    (ResidueChannelCertificateLedger.append_rewriteStepCount
      (TraceCorQTerm.compRight leftTerm right).certificateLedger
      (TraceCorQFormalSum.comp leftTail right).certificateLedger)

/-- Composing the zero formal sum on the right gives zero. -/
theorem TraceCorQFormalSum.comp_zero
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      formalSum
      TraceCorQFormalSum.zero =
      TraceCorQFormalSum.zero :=
  match formalSum with
  | [] => rfl
  | term :: tail =>
      Eq.trans
        (congrArg
          (fun tailComp =>
            TraceCorQTerm.compRight term TraceCorQFormalSum.zero ++
              tailComp)
          (TraceCorQFormalSum.comp_zero tail))
        (TraceCorQFormalSum.zero_add TraceCorQFormalSum.zero)

/-- Formal composition is left-distributive over formal-sum addition. -/
theorem TraceCorQFormalSum.add_comp
    (left right tail : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      (TraceCorQFormalSum.add left right)
      tail =
      TraceCorQFormalSum.add
        (TraceCorQFormalSum.comp left tail)
        (TraceCorQFormalSum.comp right tail) :=
  match left with
  | [] => rfl
  | term :: leftTail =>
      Eq.trans
        (congrArg
          (fun tailComp =>
            TraceCorQTerm.compRight term tail ++ tailComp)
          (TraceCorQFormalSum.add_comp leftTail right tail))
        (Eq.symm
          (List.append_assoc
            (TraceCorQTerm.compRight term tail)
            (TraceCorQFormalSum.comp leftTail tail)
            (TraceCorQFormalSum.comp right tail)))

/-- Formal composition is right-distributive over addition up to list permutation. -/
theorem TraceCorQFormalSum.comp_add_perm
    (left right tail : TraceCorQFormalSum) :
    List.Perm
      (TraceCorQFormalSum.comp
        left
        (TraceCorQFormalSum.add right tail))
      (TraceCorQFormalSum.add
        (TraceCorQFormalSum.comp left right)
        (TraceCorQFormalSum.comp left tail)) :=
  (List.Perm.flatMap_left
    left
    (fun term _ =>
      Eq.subst
        (motive := fun formalSum =>
          List.Perm
            (TraceCorQTerm.compRight
              term
              (TraceCorQFormalSum.add right tail))
            formalSum)
        (TraceCorQTerm.compRight_add term right tail)
        (List.Perm.refl
          (TraceCorQTerm.compRight
            term
            (TraceCorQFormalSum.add right tail))))).trans
    (List.flatMap_append_perm
      left
      (fun term => TraceCorQTerm.compRight term right)
      (fun term => TraceCorQTerm.compRight term tail)).symm

/-- Scaling the left term scales term-right composition. -/
theorem TraceCorQTerm.smul_compRight
    (coefficient : Rat)
    (term : TraceCorQTerm)
    (formalSum : TraceCorQFormalSum) :
    TraceCorQTerm.compRight
      (coefficient * term.1, term.2)
      formalSum =
      TraceCorQFormalSum.smul
        coefficient
        (TraceCorQTerm.compRight term formalSum) :=
  match formalSum with
  | [] => rfl
  | rightTerm :: tail =>
      Eq.trans
        (congrArg
          (fun scaledCoefficient =>
            (scaledCoefficient,
              TraceCorQGenerator.comp term.2 rightTerm.2) ::
              TraceCorQTerm.compRight
                (coefficient * term.1, term.2)
                tail)
          (mul_assoc coefficient term.1 rightTerm.1))
        (congrArg
          (fun scaledTail =>
            (coefficient * (term.1 * rightTerm.1),
              TraceCorQGenerator.comp term.2 rightTerm.2) ::
              scaledTail)
          (TraceCorQTerm.smul_compRight coefficient term tail))

/-- Scaling the right formal sum scales term-right composition. -/
theorem TraceCorQTerm.compRight_smul
    (coefficient : Rat)
    (term : TraceCorQTerm)
    (formalSum : TraceCorQFormalSum) :
    TraceCorQTerm.compRight
      term
      (TraceCorQFormalSum.smul coefficient formalSum) =
      TraceCorQFormalSum.smul
        coefficient
        (TraceCorQTerm.compRight term formalSum) :=
  match formalSum with
  | [] => rfl
  | rightTerm :: tail =>
      Eq.trans
        (congrArg
          (fun scaledCoefficient =>
            (scaledCoefficient,
              TraceCorQGenerator.comp term.2 rightTerm.2) ::
              TraceCorQTerm.compRight
                term
                (TraceCorQFormalSum.smul coefficient tail))
          (Eq.trans
            (Eq.symm
              (mul_assoc term.1 coefficient rightTerm.1))
            (Eq.trans
              (congrArg
                (fun leftCoefficient =>
                  leftCoefficient * rightTerm.1)
                (mul_comm term.1 coefficient))
              (mul_assoc coefficient term.1 rightTerm.1))))
        (congrArg
          (fun scaledTail =>
            (coefficient * (term.1 * rightTerm.1),
              TraceCorQGenerator.comp term.2 rightTerm.2) ::
              scaledTail)
          (TraceCorQTerm.compRight_smul coefficient term tail))

/-- Scaling the left formal sum scales formal composition. -/
theorem TraceCorQFormalSum.smul_comp
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      (TraceCorQFormalSum.smul coefficient left)
      right =
      TraceCorQFormalSum.smul
        coefficient
        (TraceCorQFormalSum.comp left right) :=
  match left with
  | [] => rfl
  | term :: tail =>
      Eq.trans
        (congrArg
          (fun tailComp =>
            TraceCorQTerm.compRight
              (coefficient * term.1, term.2)
              right ++ tailComp)
          (TraceCorQFormalSum.smul_comp coefficient tail right))
        (Eq.trans
          (congrArg
            (fun headComp =>
              headComp ++
                TraceCorQFormalSum.smul
                  coefficient
                  (TraceCorQFormalSum.comp tail right))
            (TraceCorQTerm.smul_compRight coefficient term right))
          (Eq.symm
            (TraceCorQFormalSum.smul_add
              coefficient
              (TraceCorQTerm.compRight term right)
              (TraceCorQFormalSum.comp tail right))))

/-- Scaling the right formal sum scales formal composition. -/
theorem TraceCorQFormalSum.comp_smul
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      left
      (TraceCorQFormalSum.smul coefficient right) =
      TraceCorQFormalSum.smul
        coefficient
        (TraceCorQFormalSum.comp left right) :=
  match left with
  | [] => rfl
  | term :: tail =>
      Eq.trans
        (congrArg
          (fun tailComp =>
            TraceCorQTerm.compRight
              term
              (TraceCorQFormalSum.smul coefficient right) ++
              tailComp)
          (TraceCorQFormalSum.comp_smul coefficient tail right))
        (Eq.trans
          (congrArg
            (fun headComp =>
              headComp ++
                TraceCorQFormalSum.smul
                  coefficient
                  (TraceCorQFormalSum.comp tail right))
            (TraceCorQTerm.compRight_smul coefficient term right))
          (Eq.symm
            (TraceCorQFormalSum.smul_add
              coefficient
              (TraceCorQTerm.compRight term right)
              (TraceCorQFormalSum.comp tail right))))

end AnalyticMotives
end LFunctions
end Boundary
