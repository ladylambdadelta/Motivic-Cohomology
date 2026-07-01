import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Neg.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Zero.Owner

/-!
# Composition laws for quotient trace correspondences

This file proves the first laws for quotient composition.  The proofs use
same-formal-sum soundness to erase ledger bookkeeping differences.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Composing the zero quotient class on the left gives zero. -/
theorem TraceCorQQuotient.zero_comp
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      TraceCorQQuotient.zero
      candidateClass =
      TraceCorQQuotient.zero :=
  Quotient.inductionOn
    candidateClass
    (fun candidate =>
      Eq.trans
        (TraceCorQQuotient.comp_ofCandidate
          TraceCorQQuotientCandidate.empty
          candidate)
        (TraceCorQQuotient.sound_sameFormalSum
          (TraceCorQRelationLedger.append
            TraceCorQRelationLedger.empty
            candidate.ledger)
          (TraceCorQFormalSum.zero_comp candidate.formalSum)))

/-- Composing the zero quotient class on the right gives zero. -/
theorem TraceCorQQuotient.comp_zero
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      candidateClass
      TraceCorQQuotient.zero =
      TraceCorQQuotient.zero :=
  Quotient.inductionOn
    candidateClass
    (fun candidate =>
      Eq.trans
        (TraceCorQQuotient.comp_ofCandidate
          candidate
          TraceCorQQuotientCandidate.empty)
        (TraceCorQQuotient.sound_sameFormalSum
          (TraceCorQRelationLedger.append
            candidate.ledger
            TraceCorQRelationLedger.empty)
          (TraceCorQFormalSum.comp_zero candidate.formalSum)))

/-- Scaling the left factor scales quotient composition. -/
theorem TraceCorQQuotient.smul_comp
    (coefficient : Rat)
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.smul coefficient left)
      right =
      TraceCorQQuotient.smul
        coefficient
        (TraceCorQQuotient.comp left right) :=
  Quotient.inductionOn₂
    left
    right
    (fun leftCandidate rightCandidate =>
      Eq.trans
        (congrArg
          (fun leftClass =>
            TraceCorQQuotient.comp
              leftClass
              (TraceCorQQuotient.ofCandidate rightCandidate))
          (TraceCorQQuotient.smul_ofCandidate
            coefficient
            leftCandidate))
        (Eq.trans
          (TraceCorQQuotient.comp_ofCandidate
            (TraceCorQQuotientCandidate.smul
              coefficient
              leftCandidate)
            rightCandidate)
          (Eq.trans
            (TraceCorQQuotient.sound_sameFormalSum
              (TraceCorQRelationLedger.append
                leftCandidate.ledger
                rightCandidate.ledger)
              (TraceCorQQuotientCandidate.smul_comp_formalSum
                coefficient
                leftCandidate
                rightCandidate))
            (Eq.trans
              (Eq.symm
                (TraceCorQQuotient.smul_ofCandidate
                  coefficient
                  (TraceCorQQuotientCandidate.comp
                    leftCandidate
                    rightCandidate)))
              (congrArg
                (TraceCorQQuotient.smul coefficient)
                (Eq.symm
                  (TraceCorQQuotient.comp_ofCandidate
                    leftCandidate
                    rightCandidate)))))))

/-- Scaling the right factor scales quotient composition. -/
theorem TraceCorQQuotient.comp_smul
    (coefficient : Rat)
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      left
      (TraceCorQQuotient.smul coefficient right) =
      TraceCorQQuotient.smul
        coefficient
        (TraceCorQQuotient.comp left right) :=
  Quotient.inductionOn₂
    left
    right
    (fun leftCandidate rightCandidate =>
      Eq.trans
        (congrArg
          (fun rightClass =>
            TraceCorQQuotient.comp
              (TraceCorQQuotient.ofCandidate leftCandidate)
              rightClass)
          (TraceCorQQuotient.smul_ofCandidate
            coefficient
            rightCandidate))
        (Eq.trans
          (TraceCorQQuotient.comp_ofCandidate
            leftCandidate
            (TraceCorQQuotientCandidate.smul
              coefficient
              rightCandidate))
          (Eq.trans
            (TraceCorQQuotient.sound_sameFormalSum
              (TraceCorQRelationLedger.append
                leftCandidate.ledger
                rightCandidate.ledger)
              (TraceCorQQuotientCandidate.comp_smul_formalSum
                coefficient
                leftCandidate
                rightCandidate))
            (Eq.trans
              (Eq.symm
                (TraceCorQQuotient.smul_ofCandidate
                  coefficient
                  (TraceCorQQuotientCandidate.comp
                    leftCandidate
                    rightCandidate)))
              (congrArg
                (TraceCorQQuotient.smul coefficient)
                (Eq.symm
                  (TraceCorQQuotient.comp_ofCandidate
                    leftCandidate
                    rightCandidate)))))))

/-- Negating the left factor negates quotient composition. -/
theorem TraceCorQQuotient.neg_comp
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.neg left)
      right =
      TraceCorQQuotient.neg
        (TraceCorQQuotient.comp left right) :=
  TraceCorQQuotient.smul_comp (-1) left right

/-- Negating the right factor negates quotient composition. -/
theorem TraceCorQQuotient.comp_neg
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      left
      (TraceCorQQuotient.neg right) =
      TraceCorQQuotient.neg
        (TraceCorQQuotient.comp left right) :=
  TraceCorQQuotient.comp_smul (-1) left right

/-- Composition is left-distributive over quotient addition. -/
theorem TraceCorQQuotient.add_comp
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.add left right)
      tail =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp left tail)
        (TraceCorQQuotient.comp right tail) :=
  Quotient.inductionOn₃
    left
    right
    tail
    (fun leftCandidate rightCandidate tailCandidate =>
      Eq.trans
        (congrArg
          (fun leftClass =>
            TraceCorQQuotient.comp
              leftClass
              (TraceCorQQuotient.ofCandidate tailCandidate))
          (TraceCorQQuotient.add_ofCandidate
            leftCandidate
            rightCandidate))
        (Eq.trans
          (TraceCorQQuotient.comp_ofCandidate
            (TraceCorQQuotientCandidate.add
              leftCandidate
              rightCandidate)
            tailCandidate)
          (Eq.trans
            (TraceCorQQuotient.sound_sameFormalSum
              (TraceCorQRelationLedger.append
                (TraceCorQRelationLedger.append
                  leftCandidate.ledger
                  rightCandidate.ledger)
                tailCandidate.ledger)
              (TraceCorQQuotientCandidate.add_comp_formalSum
                leftCandidate
                rightCandidate
                tailCandidate))
            (Eq.trans
              (Eq.symm
                (TraceCorQQuotient.add_ofCandidate
                  (TraceCorQQuotientCandidate.comp
                    leftCandidate
                    tailCandidate)
                  (TraceCorQQuotientCandidate.comp
                    rightCandidate
                    tailCandidate)))
              (Eq.trans
                (congrArg
                  (fun leftClass =>
                    TraceCorQQuotient.add
                      leftClass
                      (TraceCorQQuotient.ofCandidate
                        (TraceCorQQuotientCandidate.comp
                          rightCandidate
                          tailCandidate)))
                  (Eq.symm
                    (TraceCorQQuotient.comp_ofCandidate
                      leftCandidate
                      tailCandidate)))
                (congrArg
                  (fun rightClass =>
                    TraceCorQQuotient.add
                      (TraceCorQQuotient.comp
                        (TraceCorQQuotient.ofCandidate leftCandidate)
                        (TraceCorQQuotient.ofCandidate tailCandidate))
                      rightClass)
                  (Eq.symm
                    (TraceCorQQuotient.comp_ofCandidate
                      rightCandidate
                      tailCandidate))))))))

/-- Composition is right-distributive over quotient addition. -/
theorem TraceCorQQuotient.comp_add
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      left
      (TraceCorQQuotient.add right tail) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp left right)
        (TraceCorQQuotient.comp left tail) :=
  Quotient.inductionOn₃
    left
    right
    tail
    (fun leftCandidate rightCandidate tailCandidate =>
      Eq.trans
        (congrArg
          (fun rightClass =>
            TraceCorQQuotient.comp
              (TraceCorQQuotient.ofCandidate leftCandidate)
              rightClass)
          (TraceCorQQuotient.add_ofCandidate
            rightCandidate
            tailCandidate))
        (Eq.trans
          (TraceCorQQuotient.comp_ofCandidate
            leftCandidate
            (TraceCorQQuotientCandidate.add
              rightCandidate
              tailCandidate))
          (Eq.trans
            (TraceCorQQuotient.sound_permFormalSum
              (TraceCorQRelationLedger.append
                leftCandidate.ledger
                (TraceCorQRelationLedger.append
                  rightCandidate.ledger
                  tailCandidate.ledger))
              (TraceCorQQuotientCandidate.comp_add_formalSum_perm
                leftCandidate
                rightCandidate
                tailCandidate))
            (Eq.trans
              (Eq.symm
                (TraceCorQQuotient.add_ofCandidate
                  (TraceCorQQuotientCandidate.comp
                    leftCandidate
                    rightCandidate)
                  (TraceCorQQuotientCandidate.comp
                    leftCandidate
                    tailCandidate)))
              (Eq.trans
                (congrArg
                  (fun leftClass =>
                    TraceCorQQuotient.add
                      leftClass
                      (TraceCorQQuotient.ofCandidate
                        (TraceCorQQuotientCandidate.comp
                          leftCandidate
                          tailCandidate)))
                  (Eq.symm
                    (TraceCorQQuotient.comp_ofCandidate
                      leftCandidate
                      rightCandidate)))
                (congrArg
                  (fun rightClass =>
                    TraceCorQQuotient.add
                      (TraceCorQQuotient.comp
                        (TraceCorQQuotient.ofCandidate leftCandidate)
                        (TraceCorQQuotient.ofCandidate rightCandidate))
                      rightClass)
                  (Eq.symm
                    (TraceCorQQuotient.comp_ofCandidate
                      leftCandidate
                      tailCandidate))))))))

end AnalyticMotives
end LFunctions
end Boundary
