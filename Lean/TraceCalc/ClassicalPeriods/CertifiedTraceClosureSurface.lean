import TraceCalc.ClassicalPeriods.ClassicalManuscriptTargets

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

/-- Family labels for the Campaign 7 packet rows that now feed admissible-generator data. -/
inductive PrimitiveFamily where
  | corr
  | loc
  | nis
  | a1
  | env
deriving DecidableEq, Repr

/-- Compatibility wrapper for downstream Prop-valued theorem-target lanes.

Slice 2 no longer uses this as the primary proof-relevant carrier. The primary data is now held by
the family-specific admissible-generator witness structures below, and this wrapper is derived from
them only when older Prop-shaped interfaces still need a generic certificate object. -/
structure AdmissibleGeneratorCertificate
    (ctx : ClassicalComparisonContext.{u, v}) where
  family : PrimitiveFamily
  GeneratorCarrier : Type _
  generatorCarrier : GeneratorCarrier
  sourceSoundnessTarget : Prop
  sourceSoundness : sourceSoundnessTarget
  admissibleGeneratorTarget : Prop
  soundnessFeedsAdmissibility : sourceSoundnessTarget → admissibleGeneratorTarget

namespace AdmissibleGeneratorCertificate

def admissibleGenerator
    {ctx : ClassicalComparisonContext.{u, v}}
    (certificate : AdmissibleGeneratorCertificate ctx) :
    certificate.admissibleGeneratorTarget :=
  certificate.soundnessFeedsAdmissibility certificate.sourceSoundness

end AdmissibleGeneratorCertificate

def CorrRowAdmissibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (row : CorrGeneratorFamilyData ctx realization) : Prop :=
  ∀ gen : row.GeneratorIndex,
    (row.generatorCorrespondence gen).correspondenceTarget ∧
      (row.sourceObjectData gen).comparisonData.grothendieckComparisonTarget ∧
      (row.targetObjectData gen).comparisonData.grothendieckComparisonTarget

def LocRowAdmissibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (row : LocGeneratorFamilyData ctx realization) : Prop :=
  ∀ gen : row.GeneratorIndex,
    (row.ambientData gen).comparisonData.periodCompatibilityTarget ∧
      (row.openData gen).comparisonData.periodCompatibilityTarget ∧
      (row.closedData gen).comparisonData.periodCompatibilityTarget

def NisRowAdmissibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (row : NisGeneratorFamilyData ctx realization) : Prop :=
  ∀ gen : row.GeneratorIndex,
    (row.baseData gen).comparisonData.grothendieckComparisonTarget ∧
      (row.patchData gen).comparisonData.grothendieckComparisonTarget ∧
      (row.overlapData gen).comparisonData.grothendieckComparisonTarget

def A1RowAdmissibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (row : A1GeneratorFamilyData ctx realization) : Prop :=
  ∀ gen : row.GeneratorIndex,
    (row.baseData gen).comparisonData.grothendieckComparisonTarget ∧
      (row.cylinderData gen).comparisonData.grothendieckComparisonTarget ∧
      (row.baseData gen).comparisonData.periodCompatibilityTarget ∧
      (row.cylinderData gen).comparisonData.periodCompatibilityTarget

def EnvComparisonAdmissibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (row : EnvGeneratorFamilyData ctx realization) : Prop :=
  ∀ gen : row.GeneratorIndex,
    (row.ambientData gen).comparisonData.grothendieckComparisonTarget ∧
      (row.envelopeData gen).comparisonData.grothendieckComparisonTarget ∧
      (row.ambientData gen).comparisonData.periodCompatibilityTarget ∧
      (row.envelopeData gen).comparisonData.periodCompatibilityTarget

def EnvRowAdmissibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (row : EnvGeneratorFamilyData ctx realization) : Prop :=
  ∀ gen : row.GeneratorIndex,
    (row.envelopeCorrespondence gen).correspondenceTarget ∧
      (row.ambientData gen).comparisonData.grothendieckComparisonTarget ∧
      (row.envelopeData gen).comparisonData.grothendieckComparisonTarget ∧
      (row.ambientData gen).comparisonData.periodCompatibilityTarget ∧
      (row.envelopeData gen).comparisonData.periodCompatibilityTarget

/-- Corr-family admissible-generator witness extracted from a typed row and Campaign 7 soundness. -/
structure CorrAdmissibleGeneratorWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  realization : GeometricRealizationFunctorData ctx
  row : CorrGeneratorFamilyData ctx realization
  sourceSoundnessTarget : Prop
  sourceSoundness : sourceSoundnessTarget
  soundnessToAdmissibleGenerators :
    sourceSoundnessTarget → CorrRowAdmissibilityTarget row

namespace CorrAdmissibleGeneratorWitness

def admissibleGenerators
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CorrAdmissibleGeneratorWitness ctx) :
  CorrRowAdmissibilityTarget witness.row :=
  witness.soundnessToAdmissibleGenerators witness.sourceSoundness

def admissibleGeneratorTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CorrAdmissibleGeneratorWitness ctx) : Prop :=
  CorrRowAdmissibilityTarget witness.row

theorem admissibleGeneratorShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CorrAdmissibleGeneratorWitness ctx) :
    witness.admissibleGeneratorTarget :=
  witness.admissibleGenerators

def toAdmissibleGeneratorCertificate
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CorrAdmissibleGeneratorWitness ctx) :
    AdmissibleGeneratorCertificate ctx where
  family := .corr
  GeneratorCarrier := CorrGeneratorFamilyData ctx witness.realization
  generatorCarrier := witness.row
  sourceSoundnessTarget := witness.sourceSoundnessTarget
  sourceSoundness := witness.sourceSoundness
  admissibleGeneratorTarget := witness.admissibleGeneratorTarget
  soundnessFeedsAdmissibility := witness.soundnessToAdmissibleGenerators

end CorrAdmissibleGeneratorWitness

/-- Loc-family admissible-generator witness extracted from a typed row and Campaign 7 soundness. -/
structure LocAdmissibleGeneratorWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  realization : GeometricRealizationFunctorData ctx
  row : LocGeneratorFamilyData ctx realization
  sourceSoundnessTarget : Prop
  sourceSoundness : sourceSoundnessTarget
  localizationTriangleTarget : Prop
  soundnessToAdmissibleGenerators :
    sourceSoundnessTarget → LocRowAdmissibilityTarget row
  soundnessToLocalizationTriangle : sourceSoundnessTarget → localizationTriangleTarget

namespace LocAdmissibleGeneratorWitness

def admissibleGenerators
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : LocAdmissibleGeneratorWitness ctx) :
  LocRowAdmissibilityTarget witness.row :=
  witness.soundnessToAdmissibleGenerators witness.sourceSoundness

def localizationTriangle
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : LocAdmissibleGeneratorWitness ctx) :
    witness.localizationTriangleTarget :=
  witness.soundnessToLocalizationTriangle witness.sourceSoundness

def admissibleGeneratorTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : LocAdmissibleGeneratorWitness ctx) : Prop :=
  LocRowAdmissibilityTarget witness.row ∧
    witness.localizationTriangleTarget

theorem admissibleGeneratorShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : LocAdmissibleGeneratorWitness ctx) :
    witness.admissibleGeneratorTarget := by
  exact ⟨witness.admissibleGenerators, witness.localizationTriangle⟩

def toAdmissibleGeneratorCertificate
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : LocAdmissibleGeneratorWitness ctx) :
    AdmissibleGeneratorCertificate ctx where
  family := .loc
  GeneratorCarrier := LocGeneratorFamilyData ctx witness.realization
  generatorCarrier := witness.row
  sourceSoundnessTarget := witness.sourceSoundnessTarget
  sourceSoundness := witness.sourceSoundness
  admissibleGeneratorTarget := witness.admissibleGeneratorTarget
  soundnessFeedsAdmissibility := by
    intro h
    exact ⟨witness.soundnessToAdmissibleGenerators h, witness.soundnessToLocalizationTriangle h⟩

end LocAdmissibleGeneratorWitness

/-- Nis-family admissible-generator witness extracted from a typed row and Campaign 7 soundness. -/
structure NisAdmissibleGeneratorWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  realization : GeometricRealizationFunctorData ctx
  row : NisGeneratorFamilyData ctx realization
  sourceSoundnessTarget : Prop
  sourceSoundness : sourceSoundnessTarget
  descentSquareCompatibilityTarget : Prop
  soundnessToAdmissibleGenerators :
    sourceSoundnessTarget → NisRowAdmissibilityTarget row
  soundnessToDescentSquareCompatibility : sourceSoundnessTarget → descentSquareCompatibilityTarget

namespace NisAdmissibleGeneratorWitness

def admissibleGenerators
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : NisAdmissibleGeneratorWitness ctx) :
  NisRowAdmissibilityTarget witness.row :=
  witness.soundnessToAdmissibleGenerators witness.sourceSoundness

def descentSquareCompatibility
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : NisAdmissibleGeneratorWitness ctx) :
    witness.descentSquareCompatibilityTarget :=
  witness.soundnessToDescentSquareCompatibility witness.sourceSoundness

def admissibleGeneratorTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : NisAdmissibleGeneratorWitness ctx) : Prop :=
  NisRowAdmissibilityTarget witness.row ∧
    witness.descentSquareCompatibilityTarget

theorem admissibleGeneratorShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : NisAdmissibleGeneratorWitness ctx) :
    witness.admissibleGeneratorTarget := by
  exact ⟨witness.admissibleGenerators, witness.descentSquareCompatibility⟩

def toAdmissibleGeneratorCertificate
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : NisAdmissibleGeneratorWitness ctx) :
    AdmissibleGeneratorCertificate ctx where
  family := .nis
  GeneratorCarrier := NisGeneratorFamilyData ctx witness.realization
  generatorCarrier := witness.row
  sourceSoundnessTarget := witness.sourceSoundnessTarget
  sourceSoundness := witness.sourceSoundness
  admissibleGeneratorTarget := witness.admissibleGeneratorTarget
  soundnessFeedsAdmissibility := by
    intro h
    exact
      ⟨witness.soundnessToAdmissibleGenerators h,
        witness.soundnessToDescentSquareCompatibility h⟩

end NisAdmissibleGeneratorWitness

/-- A1-family admissible-generator witness extracted from a typed row and Campaign 7 soundness. -/
structure A1AdmissibleGeneratorWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  realization : GeometricRealizationFunctorData ctx
  row : A1GeneratorFamilyData ctx realization
  sourceSoundnessTarget : Prop
  sourceSoundness : sourceSoundnessTarget
  homotopyInvarianceTarget : Prop
  soundnessToAdmissibleGenerators :
    sourceSoundnessTarget → A1RowAdmissibilityTarget row
  soundnessToHomotopyInvariance : sourceSoundnessTarget → homotopyInvarianceTarget

namespace A1AdmissibleGeneratorWitness

def admissibleGenerators
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : A1AdmissibleGeneratorWitness ctx) :
  A1RowAdmissibilityTarget witness.row :=
  witness.soundnessToAdmissibleGenerators witness.sourceSoundness

def homotopyInvariance
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : A1AdmissibleGeneratorWitness ctx) :
    witness.homotopyInvarianceTarget :=
  witness.soundnessToHomotopyInvariance witness.sourceSoundness

def admissibleGeneratorTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : A1AdmissibleGeneratorWitness ctx) : Prop :=
  A1RowAdmissibilityTarget witness.row ∧
    witness.homotopyInvarianceTarget

theorem admissibleGeneratorShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : A1AdmissibleGeneratorWitness ctx) :
    witness.admissibleGeneratorTarget := by
  exact ⟨witness.admissibleGenerators, witness.homotopyInvariance⟩

def toAdmissibleGeneratorCertificate
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : A1AdmissibleGeneratorWitness ctx) :
    AdmissibleGeneratorCertificate ctx where
  family := .a1
  GeneratorCarrier := A1GeneratorFamilyData ctx witness.realization
  generatorCarrier := witness.row
  sourceSoundnessTarget := witness.sourceSoundnessTarget
  sourceSoundness := witness.sourceSoundness
  admissibleGeneratorTarget := witness.admissibleGeneratorTarget
  soundnessFeedsAdmissibility := by
    intro h
    exact ⟨witness.soundnessToAdmissibleGenerators h, witness.soundnessToHomotopyInvariance h⟩

end A1AdmissibleGeneratorWitness

/-- Env-family admissible-generator witness extracted from a typed row and Campaign 7 soundness.

Unlike the other rows, Campaign 7 exports the comparison and formal-closure side but not the
envelope-correspondence component, so the strengthened witness keeps that correspondence proof as a
typed row-level ingredient and combines it with Campaign 7 soundness to assemble the full row-wise
admissibility witness. -/
structure EnvAdmissibleGeneratorWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  realization : GeometricRealizationFunctorData ctx
  row : EnvGeneratorFamilyData ctx realization
  sourceSoundnessTarget : Prop
  sourceSoundness : sourceSoundnessTarget
  formalClosureTarget : Prop
  correspondenceAdmissibility :
    ∀ gen : row.GeneratorIndex, (row.envelopeCorrespondence gen).correspondenceTarget
  soundnessToComparisonAdmissibility :
    sourceSoundnessTarget → EnvComparisonAdmissibilityTarget row
  soundnessToFormalClosure : sourceSoundnessTarget → formalClosureTarget

namespace EnvAdmissibleGeneratorWitness

def admissibleGenerators
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : EnvAdmissibleGeneratorWitness ctx) :
  EnvRowAdmissibilityTarget witness.row := by
  intro gen
  rcases witness.soundnessToComparisonAdmissibility witness.sourceSoundness gen with
    ⟨hAmbientGroth, hEnvelopeGroth, hAmbientPeriod, hEnvelopePeriod⟩
  exact
    ⟨witness.correspondenceAdmissibility gen, hAmbientGroth, hEnvelopeGroth,
      hAmbientPeriod, hEnvelopePeriod⟩

def formalClosure
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : EnvAdmissibleGeneratorWitness ctx) :
    witness.formalClosureTarget :=
  witness.soundnessToFormalClosure witness.sourceSoundness

def admissibleGeneratorTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : EnvAdmissibleGeneratorWitness ctx) : Prop :=
  EnvRowAdmissibilityTarget witness.row ∧
    witness.formalClosureTarget

theorem admissibleGeneratorShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : EnvAdmissibleGeneratorWitness ctx) :
    witness.admissibleGeneratorTarget := by
  exact ⟨witness.admissibleGenerators, witness.formalClosure⟩

def toAdmissibleGeneratorCertificate
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : EnvAdmissibleGeneratorWitness ctx) :
    AdmissibleGeneratorCertificate ctx where
  family := .env
  GeneratorCarrier := EnvGeneratorFamilyData ctx witness.realization
  generatorCarrier := witness.row
  sourceSoundnessTarget := witness.sourceSoundnessTarget
  sourceSoundness := witness.sourceSoundness
  admissibleGeneratorTarget := witness.admissibleGeneratorTarget
  soundnessFeedsAdmissibility := by
    intro h
    refine ⟨?_, witness.soundnessToFormalClosure h⟩
    intro gen
    rcases witness.soundnessToComparisonAdmissibility h gen with
      ⟨hAmbientGroth, hEnvelopeGroth, hAmbientPeriod, hEnvelopePeriod⟩
    exact
      ⟨witness.correspondenceAdmissibility gen, hAmbientGroth, hEnvelopeGroth,
        hAmbientPeriod, hEnvelopePeriod⟩

end EnvAdmissibleGeneratorWitness

/-- Aggregate of the strengthened primitive admissible-generator witnesses. -/
structure PrimitiveAdmissibleGeneratorWitnesses
    (ctx : ClassicalComparisonContext.{u, v}) where
  corr : CorrAdmissibleGeneratorWitness ctx
  loc : LocAdmissibleGeneratorWitness ctx
  nis : NisAdmissibleGeneratorWitness ctx
  a1 : A1AdmissibleGeneratorWitness ctx
  env : EnvAdmissibleGeneratorWitness ctx

def primitiveWitnessesSoundnessTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (witnesses : PrimitiveAdmissibleGeneratorWitnesses ctx) : Prop :=
  witnesses.corr.admissibleGeneratorTarget ∧
    witnesses.loc.admissibleGeneratorTarget ∧
      witnesses.nis.admissibleGeneratorTarget ∧
        witnesses.a1.admissibleGeneratorTarget ∧
          witnesses.env.admissibleGeneratorTarget

def primitiveWitnessesEnvelopeClosureTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (witnesses : PrimitiveAdmissibleGeneratorWitnesses ctx) : Prop :=
  witnesses.env.formalClosureTarget

theorem primitiveWitnessesSoundnessShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witnesses : PrimitiveAdmissibleGeneratorWitnesses ctx) :
    primitiveWitnessesSoundnessTarget witnesses := by
  exact ⟨witnesses.corr.admissibleGeneratorShadow,
    witnesses.loc.admissibleGeneratorShadow,
    witnesses.nis.admissibleGeneratorShadow,
    witnesses.a1.admissibleGeneratorShadow,
    witnesses.env.admissibleGeneratorShadow⟩

theorem primitiveWitnessesEnvelopeClosureShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witnesses : PrimitiveAdmissibleGeneratorWitnesses ctx) :
    primitiveWitnessesEnvelopeClosureTarget witnesses :=
  witnesses.env.formalClosure

inductive CertifiedTraceClosureGenerator
    (ctx : ClassicalComparisonContext.{u, v}) where
  | corr : CorrAdmissibleGeneratorWitness ctx → CertifiedTraceClosureGenerator ctx
  | loc : LocAdmissibleGeneratorWitness ctx → CertifiedTraceClosureGenerator ctx
  | nis : NisAdmissibleGeneratorWitness ctx → CertifiedTraceClosureGenerator ctx
  | a1 : A1AdmissibleGeneratorWitness ctx → CertifiedTraceClosureGenerator ctx
  | env : EnvAdmissibleGeneratorWitness ctx → CertifiedTraceClosureGenerator ctx

namespace CertifiedTraceClosureGenerator

def soundnessShadowTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (generator : CertifiedTraceClosureGenerator ctx) : Prop :=
  match generator with
  | .corr witness => witness.admissibleGeneratorTarget
  | .loc witness => witness.admissibleGeneratorTarget
  | .nis witness => witness.admissibleGeneratorTarget
  | .a1 witness => witness.admissibleGeneratorTarget
  | .env witness => witness.admissibleGeneratorTarget

def envelopeClosureShadowTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (generator : CertifiedTraceClosureGenerator ctx) : Prop :=
  match generator with
  | .env witness => witness.formalClosureTarget
  | _ => True

theorem soundnessShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (generator : CertifiedTraceClosureGenerator ctx) :
    generator.soundnessShadowTarget := by
  cases generator with
  | corr witness => exact witness.admissibleGeneratorShadow
  | loc witness => exact witness.admissibleGeneratorShadow
  | nis witness => exact witness.admissibleGeneratorShadow
  | a1 witness => exact witness.admissibleGeneratorShadow
  | env witness => exact witness.admissibleGeneratorShadow

theorem envelopeClosureSoundnessShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (generator : CertifiedTraceClosureGenerator ctx) :
    generator.envelopeClosureShadowTarget := by
  cases generator with
  | corr => simp [CertifiedTraceClosureGenerator.envelopeClosureShadowTarget]
  | loc => simp [CertifiedTraceClosureGenerator.envelopeClosureShadowTarget]
  | nis => simp [CertifiedTraceClosureGenerator.envelopeClosureShadowTarget]
  | a1 => simp [CertifiedTraceClosureGenerator.envelopeClosureShadowTarget]
  | env witness =>
      simpa [CertifiedTraceClosureGenerator.envelopeClosureShadowTarget] using witness.formalClosure

end CertifiedTraceClosureGenerator

structure CertifiedComposeClosureWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  comparisonAgreementTarget : Prop
  formalClosureTarget : Prop
  replayData : CertifiedEnvReplayData ctx comparisonAgreementTarget formalClosureTarget
  replayTransformer : EnvReplayTransformerTarget
  replayTransformer_eq :
    replayTransformer =
      EnvReplayTransformerTarget.envCompose_from_certifiedReplay replayData.replayTransformerTarget
  leftInputCertifiedTarget : Prop
  rightInputCertifiedTarget : Prop
  outputCertifiedTarget : Prop
  soundness_holds : outputCertifiedTarget

namespace CertifiedComposeClosureWitness

theorem replayOperationShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedComposeClosureWitness ctx) :
    witness.replayTransformer.operation = EnvReplayOperation.compose := by
  simp [witness.replayTransformer_eq, EnvReplayTransformerTarget.envCompose_from_certifiedReplay]

theorem formalClosureShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedComposeClosureWitness ctx) :
    witness.formalClosureTarget :=
  witness.replayData.formalClosure_holds

end CertifiedComposeClosureWitness

structure CertifiedTensorClosureWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  comparisonAgreementTarget : Prop
  formalClosureTarget : Prop
  replayData : CertifiedEnvReplayData ctx comparisonAgreementTarget formalClosureTarget
  replayTransformer : EnvReplayTransformerTarget
  replayTransformer_eq :
    replayTransformer =
      EnvReplayTransformerTarget.envTensor_from_certifiedReplay replayData.replayTransformerTarget
  leftInputCertifiedTarget : Prop
  rightInputCertifiedTarget : Prop
  outputCertifiedTarget : Prop
  soundness_holds : outputCertifiedTarget

namespace CertifiedTensorClosureWitness

theorem replayOperationShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedTensorClosureWitness ctx) :
    witness.replayTransformer.operation = EnvReplayOperation.tensor := by
  simp [witness.replayTransformer_eq, EnvReplayTransformerTarget.envTensor_from_certifiedReplay]

theorem formalClosureShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedTensorClosureWitness ctx) :
    witness.formalClosureTarget :=
  witness.replayData.formalClosure_holds

end CertifiedTensorClosureWitness

structure CertifiedWhiskerClosureWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  comparisonAgreementTarget : Prop
  formalClosureTarget : Prop
  replayData : CertifiedEnvReplayData ctx comparisonAgreementTarget formalClosureTarget
  replayTransformer : EnvReplayTransformerTarget
  replayTransformer_eq :
    replayTransformer =
      EnvReplayTransformerTarget.envWhisker_from_certifiedReplay replayData.replayTransformerTarget
  inputCertifiedTarget : Prop
  outputCertifiedTarget : Prop
  soundness_holds : outputCertifiedTarget

namespace CertifiedWhiskerClosureWitness

theorem replayOperationShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedWhiskerClosureWitness ctx) :
    witness.replayTransformer.operation = EnvReplayOperation.whisker := by
  simp [witness.replayTransformer_eq, EnvReplayTransformerTarget.envWhisker_from_certifiedReplay]

theorem formalClosureShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedWhiskerClosureWitness ctx) :
    witness.formalClosureTarget :=
  witness.replayData.formalClosure_holds

end CertifiedWhiskerClosureWitness

structure CertifiedStructuralAdminClosureWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  comparisonAgreementTarget : Prop
  formalClosureTarget : Prop
  replayData : CertifiedEnvReplayData ctx comparisonAgreementTarget formalClosureTarget
  replayTransformer : EnvReplayTransformerTarget
  replayTransformer_eq :
    replayTransformer =
      EnvReplayTransformerTarget.envStructuralAdmin_from_certifiedReplay
        replayData.replayTransformerTarget
  inputCertifiedTarget : Prop
  outputCertifiedTarget : Prop
  soundness_holds : outputCertifiedTarget

namespace CertifiedStructuralAdminClosureWitness

theorem replayOperationShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedStructuralAdminClosureWitness ctx) :
    witness.replayTransformer.operation = EnvReplayOperation.structuralAdmin := by
  simp [witness.replayTransformer_eq,
    EnvReplayTransformerTarget.envStructuralAdmin_from_certifiedReplay]

theorem formalClosureShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedStructuralAdminClosureWitness ctx) :
    witness.formalClosureTarget :=
  witness.replayData.formalClosure_holds

end CertifiedStructuralAdminClosureWitness

structure CertifiedShiftClosureWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  comparisonAgreementTarget : Prop
  formalClosureTarget : Prop
  replayData : CertifiedEnvReplayData ctx comparisonAgreementTarget formalClosureTarget
  replayTransformer : EnvReplayTransformerTarget
  replayTransformer_eq :
    replayTransformer =
      EnvReplayTransformerTarget.envShift_from_certifiedReplay replayData.replayTransformerTarget
  inputCertifiedTarget : Prop
  outputCertifiedTarget : Prop
  soundness_holds : outputCertifiedTarget

namespace CertifiedShiftClosureWitness

theorem replayOperationShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedShiftClosureWitness ctx) :
    witness.replayTransformer.operation = EnvReplayOperation.shift := by
  simp [witness.replayTransformer_eq, EnvReplayTransformerTarget.envShift_from_certifiedReplay]

theorem formalClosureShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedShiftClosureWitness ctx) :
    witness.formalClosureTarget :=
  witness.replayData.formalClosure_holds

end CertifiedShiftClosureWitness

structure CertifiedConeClosureWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  connectingPacketComparisonTarget : Prop
  locReplayData : CertifiedLocPacketReplayData ctx connectingPacketComparisonTarget
  triangleCompatibilityTarget : Prop
  ambientCertifiedTarget : Prop
  closedCertifiedTarget : Prop
  coneCertifiedTarget : Prop
  connectingMorphismTarget : Prop
  shiftClosedTarget : Prop
  triangleCompatibility_holds : triangleCompatibilityTarget
  soundness_holds : coneCertifiedTarget

namespace CertifiedConeClosureWitness

theorem connectingPacketComparisonShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedConeClosureWitness ctx) :
    witness.connectingPacketComparisonTarget :=
  witness.locReplayData.connectingPacketComparisonNaturality_holds

theorem triangleCompatibilityShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedConeClosureWitness ctx) :
    witness.triangleCompatibilityTarget :=
  witness.triangleCompatibility_holds

end CertifiedConeClosureWitness

structure CertifiedCofiberClosureWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  connectingPacketComparisonTarget : Prop
  locReplayData : CertifiedLocPacketReplayData ctx connectingPacketComparisonTarget
  triangleCompatibilityTarget : Prop
  sourceCertifiedTarget : Prop
  targetCertifiedTarget : Prop
  cofiberCertifiedTarget : Prop
  connectingMorphismTarget : Prop
  shiftSourceTarget : Prop
  triangleCompatibility_holds : triangleCompatibilityTarget
  soundness_holds : cofiberCertifiedTarget

namespace CertifiedCofiberClosureWitness

theorem connectingPacketComparisonShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedCofiberClosureWitness ctx) :
    witness.connectingPacketComparisonTarget :=
  witness.locReplayData.connectingPacketComparisonNaturality_holds

theorem triangleCompatibilityShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedCofiberClosureWitness ctx) :
    witness.triangleCompatibilityTarget :=
  witness.triangleCompatibility_holds

end CertifiedCofiberClosureWitness

structure CertifiedRetractClosureWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  inputCertifiedTarget : Prop
  retractCertifiedTarget : Prop
  sectionTarget : Prop
  retractionTarget : Prop
  idempotentCompatibilityTarget : Prop
  idempotentCompatibility_holds : idempotentCompatibilityTarget
  soundness_holds : retractCertifiedTarget

namespace CertifiedRetractClosureWitness

theorem idempotentCompatibilityShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedRetractClosureWitness ctx) :
    witness.idempotentCompatibilityTarget :=
  witness.idempotentCompatibility_holds

end CertifiedRetractClosureWitness

inductive CertifiedTraceClosure
    (ctx : ClassicalComparisonContext.{u, v}) where
  | ofPrimitiveWitnesses :
      PrimitiveAdmissibleGeneratorWitnesses ctx → CertifiedTraceClosure ctx
  | seed : CertifiedTraceClosureGenerator ctx → CertifiedTraceClosure ctx
  | compose :
      CertifiedTraceClosure ctx →
      CertifiedTraceClosure ctx →
      CertifiedComposeClosureWitness ctx →
      CertifiedTraceClosure ctx
  | tensor :
      CertifiedTraceClosure ctx →
      CertifiedTraceClosure ctx →
      CertifiedTensorClosureWitness ctx →
      CertifiedTraceClosure ctx
  | whisker :
      CertifiedTraceClosure ctx →
      CertifiedWhiskerClosureWitness ctx →
      CertifiedTraceClosure ctx
  | admin :
      CertifiedTraceClosure ctx →
      CertifiedStructuralAdminClosureWitness ctx →
      CertifiedTraceClosure ctx
  | shift :
      CertifiedTraceClosure ctx →
      CertifiedShiftClosureWitness ctx →
      CertifiedTraceClosure ctx
  | cone :
      CertifiedTraceClosure ctx →
      CertifiedConeClosureWitness ctx →
      CertifiedTraceClosure ctx
  | cofiber :
      CertifiedTraceClosure ctx →
      CertifiedCofiberClosureWitness ctx →
      CertifiedTraceClosure ctx
  | retract :
      CertifiedTraceClosure ctx →
      CertifiedRetractClosureWitness ctx →
      CertifiedTraceClosure ctx

namespace CertifiedTraceClosure

def seedCorr
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CorrAdmissibleGeneratorWitness ctx) :
    CertifiedTraceClosure ctx :=
  .seed (.corr witness)

def seedLoc
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : LocAdmissibleGeneratorWitness ctx) :
    CertifiedTraceClosure ctx :=
  .seed (.loc witness)

def seedNis
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : NisAdmissibleGeneratorWitness ctx) :
    CertifiedTraceClosure ctx :=
  .seed (.nis witness)

def seedA1
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : A1AdmissibleGeneratorWitness ctx) :
    CertifiedTraceClosure ctx :=
  .seed (.a1 witness)

def seedEnv
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : EnvAdmissibleGeneratorWitness ctx) :
    CertifiedTraceClosure ctx :=
  .seed (.env witness)

def composeWith
    {ctx : ClassicalComparisonContext.{u, v}}
    (left right : CertifiedTraceClosure ctx)
    (witness : CertifiedComposeClosureWitness ctx) :
    CertifiedTraceClosure ctx :=
  .compose left right witness

def tensorWith
    {ctx : ClassicalComparisonContext.{u, v}}
    (left right : CertifiedTraceClosure ctx)
    (witness : CertifiedTensorClosureWitness ctx) :
    CertifiedTraceClosure ctx :=
  .tensor left right witness

def whiskerBy
    {ctx : ClassicalComparisonContext.{u, v}}
    (closure : CertifiedTraceClosure ctx)
    (witness : CertifiedWhiskerClosureWitness ctx) :
    CertifiedTraceClosure ctx :=
  .whisker closure witness

def structuralAdmin
    {ctx : ClassicalComparisonContext.{u, v}}
    (closure : CertifiedTraceClosure ctx)
    (witness : CertifiedStructuralAdminClosureWitness ctx) :
    CertifiedTraceClosure ctx :=
  .admin closure witness

def shiftBy
    {ctx : ClassicalComparisonContext.{u, v}}
    (closure : CertifiedTraceClosure ctx)
    (witness : CertifiedShiftClosureWitness ctx) :
    CertifiedTraceClosure ctx :=
  .shift closure witness

def coneBy
    {ctx : ClassicalComparisonContext.{u, v}}
    (closure : CertifiedTraceClosure ctx)
    (witness : CertifiedConeClosureWitness ctx) :
    CertifiedTraceClosure ctx :=
  .cone closure witness

def cofiberBy
    {ctx : ClassicalComparisonContext.{u, v}}
    (closure : CertifiedTraceClosure ctx)
    (witness : CertifiedCofiberClosureWitness ctx) :
    CertifiedTraceClosure ctx :=
  .cofiber closure witness

def retractBy
    {ctx : ClassicalComparisonContext.{u, v}}
    (closure : CertifiedTraceClosure ctx)
    (witness : CertifiedRetractClosureWitness ctx) :
    CertifiedTraceClosure ctx :=
  .retract closure witness

def soundnessShadowTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (closure : CertifiedTraceClosure ctx) : Prop :=
  match closure with
  | .ofPrimitiveWitnesses witnesses => primitiveWitnessesSoundnessTarget witnesses
  | .seed generator => generator.soundnessShadowTarget
  | .compose left right witness =>
      left.soundnessShadowTarget ∧ right.soundnessShadowTarget ∧ witness.outputCertifiedTarget
  | .tensor left right witness =>
      left.soundnessShadowTarget ∧ right.soundnessShadowTarget ∧ witness.outputCertifiedTarget
  | .whisker source witness => source.soundnessShadowTarget ∧ witness.outputCertifiedTarget
  | .admin source witness => source.soundnessShadowTarget ∧ witness.outputCertifiedTarget
  | .shift source witness => source.soundnessShadowTarget ∧ witness.outputCertifiedTarget
  | .cone source witness => source.soundnessShadowTarget ∧ witness.coneCertifiedTarget
  | .cofiber source witness => source.soundnessShadowTarget ∧ witness.cofiberCertifiedTarget
  | .retract source witness => source.soundnessShadowTarget ∧ witness.retractCertifiedTarget

def envelopeClosureShadowTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (closure : CertifiedTraceClosure ctx) : Prop :=
  match closure with
  | .ofPrimitiveWitnesses witnesses => primitiveWitnessesEnvelopeClosureTarget witnesses
  | .seed generator => generator.envelopeClosureShadowTarget
  | .compose _ _ witness => witness.formalClosureTarget
  | .tensor _ _ witness => witness.formalClosureTarget
  | .whisker _ witness => witness.formalClosureTarget
  | .admin _ witness => witness.formalClosureTarget
  | .shift _ witness => witness.formalClosureTarget
  | .cone _ witness => witness.triangleCompatibilityTarget
  | .cofiber _ witness => witness.triangleCompatibilityTarget
  | .retract _ witness => witness.idempotentCompatibilityTarget

theorem soundnessShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (closure : CertifiedTraceClosure ctx) :
    closure.soundnessShadowTarget := by
  induction closure with
  | ofPrimitiveWitnesses witnesses => exact primitiveWitnessesSoundnessShadow witnesses
  | seed generator => exact generator.soundnessShadow
  | compose _ _ witness hLeft hRight => exact ⟨hLeft, hRight, witness.soundness_holds⟩
  | tensor _ _ witness hLeft hRight => exact ⟨hLeft, hRight, witness.soundness_holds⟩
  | whisker _ witness hSource => exact ⟨hSource, witness.soundness_holds⟩
  | admin _ witness hSource => exact ⟨hSource, witness.soundness_holds⟩
  | shift _ witness hSource => exact ⟨hSource, witness.soundness_holds⟩
  | cone _ witness hSource => exact ⟨hSource, witness.soundness_holds⟩
  | cofiber _ witness hSource => exact ⟨hSource, witness.soundness_holds⟩
  | retract _ witness hSource => exact ⟨hSource, witness.soundness_holds⟩

theorem envelopeClosureSoundnessShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (closure : CertifiedTraceClosure ctx) :
    closure.envelopeClosureShadowTarget := by
  induction closure with
  | ofPrimitiveWitnesses witnesses => exact primitiveWitnessesEnvelopeClosureShadow witnesses
  | seed generator => exact generator.envelopeClosureSoundnessShadow
  | compose _ _ witness _ _ => exact witness.formalClosureShadow
  | tensor _ _ witness _ _ => exact witness.formalClosureShadow
  | whisker _ witness _ => exact witness.formalClosureShadow
  | admin _ witness _ => exact witness.formalClosureShadow
  | shift _ witness _ => exact witness.formalClosureShadow
  | cone _ witness _ => exact witness.triangleCompatibilityShadow
  | cofiber _ witness _ => exact witness.triangleCompatibilityShadow
  | retract _ witness _ => exact witness.idempotentCompatibilityShadow

theorem primitiveWitnesses_generate_certifiedTraceClosure
    {ctx : ClassicalComparisonContext.{u, v}}
    (witnesses : PrimitiveAdmissibleGeneratorWitnesses ctx) :
    (CertifiedTraceClosure.ofPrimitiveWitnesses witnesses).soundnessShadowTarget :=
  primitiveWitnessesSoundnessShadow witnesses

def certifiedTraceClosure_from_primitiveAdmissibleGeneratorWitnesses
    {ctx : ClassicalComparisonContext.{u, v}}
    (witnesses : PrimitiveAdmissibleGeneratorWitnesses ctx) :
    CertifiedTraceClosure ctx :=
  .ofPrimitiveWitnesses witnesses

theorem seedCorr_soundnessShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CorrAdmissibleGeneratorWitness ctx) :
    (seedCorr witness).soundnessShadowTarget :=
  witness.admissibleGeneratorShadow

theorem seedLoc_soundnessShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : LocAdmissibleGeneratorWitness ctx) :
    (seedLoc witness).soundnessShadowTarget :=
  witness.admissibleGeneratorShadow

theorem seedNis_soundnessShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : NisAdmissibleGeneratorWitness ctx) :
    (seedNis witness).soundnessShadowTarget :=
  witness.admissibleGeneratorShadow

theorem seedA1_soundnessShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : A1AdmissibleGeneratorWitness ctx) :
    (seedA1 witness).soundnessShadowTarget :=
  witness.admissibleGeneratorShadow

theorem seedEnv_soundnessShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : EnvAdmissibleGeneratorWitness ctx) :
    (seedEnv witness).soundnessShadowTarget :=
  witness.admissibleGeneratorShadow

end CertifiedTraceClosure

end ClassicalPeriods
end TraceCalc