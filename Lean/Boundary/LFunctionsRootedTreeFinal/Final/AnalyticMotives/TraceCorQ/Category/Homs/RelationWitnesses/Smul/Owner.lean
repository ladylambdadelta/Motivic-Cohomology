import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Owner

/-!
# Scalar compatibility for typed hom relation witnesses

This file lifts scalar compatibility from proof-valued typed hom relations to
data-bearing typed hom relation witnesses.  The construction follows the
existing proof-valued route: compare the scaled representative to ambient
candidate scaling, apply raw witness scalar compatibility, and compare back.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Witness from representative scaling to ambient candidate scaling. -/
def TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQRelationWitness
      (TraceCorQHomRepresentative.smul coefficient representative).rawCandidate
      (TraceCorQQuotientCandidate.smul
        coefficient
        representative.rawCandidate) :=
  TraceCorQRelationWitness.sameFormalSum
    representative.rawCandidate.ledger
    (TraceCorQHomRepresentative.smul_rawCandidate_formalSum
      coefficient
      representative)

/-- Witness from ambient candidate scaling back to representative scaling. -/
def TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQRelationWitness
      (TraceCorQQuotientCandidate.smul
        coefficient
        representative.rawCandidate)
      (TraceCorQHomRepresentative.smul coefficient representative).rawCandidate :=
  TraceCorQRelationWitness.symm
    (TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul
      coefficient
      representative)

/-- Scalar compatibility for data-bearing typed hom relation witnesses. -/
def TraceCorQHomRelationWitness.smulCongr
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (coefficient : Rat)
    (witness : TraceCorQHomRelationWitness left right) :
    TraceCorQHomRelationWitness
      (TraceCorQHomRepresentative.smul coefficient left)
      (TraceCorQHomRepresentative.smul coefficient right) :=
  TraceCorQRelationWitness.trans
    (TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul
      coefficient
      left)
    (TraceCorQRelationWitness.trans
      (TraceCorQRelationWitness.smulCongr coefficient witness)
      (TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative
        coefficient
        right))

/-- The representative-to-candidate scalar witness carries the representative ledger certificates. -/
theorem TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul_certificateLedger
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul
      coefficient
      representative).certificateLedger =
      representative.rawCandidate.ledger.certificateLedger :=
  rfl

/-- The representative-to-candidate scalar witness carries the representative ledger imported payload. -/
theorem TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul_importedRectangleCount
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul
      coefficient
      representative).importedRectangleCount =
      representative.rawCandidate.ledger.importedRectangleCount :=
  rfl

/-- The representative-to-candidate scalar witness carries the representative ledger rectangles. -/
theorem TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul_importedRectangles
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul
      coefficient
      representative).importedRectangles =
      representative.rawCandidate.ledger.importedRectangles :=
  rfl

/-- The representative-to-candidate scalar witness carries the representative ledger bookkeeping payload. -/
theorem TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul_traceBookkeepingCount
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul
      coefficient
      representative).traceBookkeepingCount =
      representative.rawCandidate.ledger.traceBookkeepingCount :=
  rfl

/-- The candidate-to-representative scalar witness carries the representative ledger certificates. -/
theorem TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative_certificateLedger
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative
      coefficient
      representative).certificateLedger =
      representative.rawCandidate.ledger.certificateLedger :=
  rfl

/-- The candidate-to-representative scalar witness carries the representative ledger imported payload. -/
theorem TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative_importedRectangleCount
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative
      coefficient
      representative).importedRectangleCount =
      representative.rawCandidate.ledger.importedRectangleCount :=
  rfl

/-- The candidate-to-representative scalar witness carries the representative ledger rectangles. -/
theorem TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative_importedRectangles
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative
      coefficient
      representative).importedRectangles =
      representative.rawCandidate.ledger.importedRectangles :=
  rfl

/-- The candidate-to-representative scalar witness carries the representative ledger bookkeeping payload. -/
theorem TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative_traceBookkeepingCount
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative
      coefficient
      representative).traceBookkeepingCount =
      representative.rawCandidate.ledger.traceBookkeepingCount :=
  rfl

/-- Scalar compatibility records endpoint certificates around the scaled witness certificates. -/
theorem TraceCorQHomRelationWitness.smulCongr_certificateLedger
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (coefficient : Rat)
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.smulCongr
      coefficient
      witness).certificateLedger =
      ResidueChannelCertificateLedger.append
        left.rawCandidate.ledger.certificateLedger
        (ResidueChannelCertificateLedger.append
          witness.certificateLedger
          right.rawCandidate.ledger.certificateLedger) :=
  Eq.trans
    (TraceCorQRelationWitness.trans_certificateLedger
      (TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul
        coefficient
        left)
      (TraceCorQRelationWitness.trans
        (TraceCorQRelationWitness.smulCongr coefficient witness)
        (TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative
          coefficient
          right)))
    (congrArg
      (ResidueChannelCertificateLedger.append
        left.rawCandidate.ledger.certificateLedger)
      (TraceCorQRelationWitness.trans_certificateLedger
        (TraceCorQRelationWitness.smulCongr coefficient witness)
        (TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative
          coefficient
          right)))

/-- Scalar compatibility records endpoint and witness imported finite-rectangle payload. -/
theorem TraceCorQHomRelationWitness.smulCongr_importedRectangleCount
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (coefficient : Rat)
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.smulCongr
      coefficient
      witness).importedRectangleCount =
      left.rawCandidate.ledger.importedRectangleCount +
        (witness.importedRectangleCount +
          right.rawCandidate.ledger.importedRectangleCount) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.importedRectangleCount
        (TraceCorQHomRelationWitness.smulCongr_certificateLedger
          coefficient
          witness))
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        left.rawCandidate.ledger.certificateLedger
        (ResidueChannelCertificateLedger.append
          witness.certificateLedger
          right.rawCandidate.ledger.certificateLedger)))
    (congrArg
      (fun count =>
        left.rawCandidate.ledger.importedRectangleCount + count)
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        witness.certificateLedger
        right.rawCandidate.ledger.certificateLedger))

/-- Scalar compatibility records endpoint and witness imported rectangles. -/
theorem TraceCorQHomRelationWitness.smulCongr_importedRectangles
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (coefficient : Rat)
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.smulCongr
      coefficient
      witness).importedRectangles =
      left.rawCandidate.ledger.importedRectangles ++
        (witness.importedRectangles ++
          right.rawCandidate.ledger.importedRectangles) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.importedRectangles
        (TraceCorQHomRelationWitness.smulCongr_certificateLedger
          coefficient
          witness))
      (ResidueChannelCertificateLedger.append_importedRectangles
        left.rawCandidate.ledger.certificateLedger
        (ResidueChannelCertificateLedger.append
          witness.certificateLedger
          right.rawCandidate.ledger.certificateLedger)))
    (congrArg
      (fun rectangles =>
        left.rawCandidate.ledger.importedRectangles ++ rectangles)
      (ResidueChannelCertificateLedger.append_importedRectangles
        witness.certificateLedger
        right.rawCandidate.ledger.certificateLedger))

/-- Scalar compatibility records endpoint and witness internal trace-bookkeeping payload. -/
theorem TraceCorQHomRelationWitness.smulCongr_traceBookkeepingCount
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (coefficient : Rat)
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.smulCongr
      coefficient
      witness).traceBookkeepingCount =
      left.rawCandidate.ledger.traceBookkeepingCount +
        (witness.traceBookkeepingCount +
          right.rawCandidate.ledger.traceBookkeepingCount) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.traceBookkeepingCount
        (TraceCorQHomRelationWitness.smulCongr_certificateLedger
          coefficient
          witness))
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        left.rawCandidate.ledger.certificateLedger
        (ResidueChannelCertificateLedger.append
          witness.certificateLedger
          right.rawCandidate.ledger.certificateLedger)))
    (congrArg
      (fun count =>
        left.rawCandidate.ledger.traceBookkeepingCount + count)
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        witness.certificateLedger
        right.rawCandidate.ledger.certificateLedger))

/-- Scalar compatibility records endpoint and witness explicit rewrite-step payload. -/
theorem TraceCorQHomRelationWitness.smulCongr_rewriteStepCount
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (coefficient : Rat)
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.smulCongr
      coefficient
      witness).rewriteStepCount =
      left.rawCandidate.ledger.rewriteStepCount +
        (witness.rewriteStepCount +
          right.rawCandidate.ledger.rewriteStepCount) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.rewriteStepCount
        (TraceCorQHomRelationWitness.smulCongr_certificateLedger
          coefficient
          witness))
      (ResidueChannelCertificateLedger.append_rewriteStepCount
        left.rawCandidate.ledger.certificateLedger
        (ResidueChannelCertificateLedger.append
          witness.certificateLedger
          right.rawCandidate.ledger.certificateLedger)))
    (congrArg
      (fun count =>
        left.rawCandidate.ledger.rewriteStepCount + count)
      (ResidueChannelCertificateLedger.append_rewriteStepCount
        witness.certificateLedger
        right.rawCandidate.ledger.certificateLedger))

end AnalyticMotives
end LFunctions
end Boundary
