import TraceCalc.ClassicalPeriods.CertifiedTraceClosureSurface

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

inductive AdmissibleGeometricClosureGenerator
    (ctx : ClassicalComparisonContext.{u, v}) where
  | corr : CorrAdmissibleGeneratorWitness ctx → AdmissibleGeometricClosureGenerator ctx
  | loc : LocAdmissibleGeneratorWitness ctx → AdmissibleGeometricClosureGenerator ctx
  | nis : NisAdmissibleGeneratorWitness ctx → AdmissibleGeometricClosureGenerator ctx
  | a1 : A1AdmissibleGeneratorWitness ctx → AdmissibleGeometricClosureGenerator ctx
  | env : EnvAdmissibleGeneratorWitness ctx → AdmissibleGeometricClosureGenerator ctx

namespace AdmissibleGeometricClosureGenerator

def soundnessShadowTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (generator : AdmissibleGeometricClosureGenerator ctx) : Prop :=
  match generator with
  | .corr witness => witness.admissibleGeneratorTarget
  | .loc witness => witness.admissibleGeneratorTarget
  | .nis witness => witness.admissibleGeneratorTarget
  | .a1 witness => witness.admissibleGeneratorTarget
  | .env witness => witness.admissibleGeneratorTarget

def envelopeClosureShadowTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (generator : AdmissibleGeometricClosureGenerator ctx) : Prop :=
  match generator with
  | .env witness => witness.formalClosureTarget
  | _ => True

theorem soundnessShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (generator : AdmissibleGeometricClosureGenerator ctx) :
    generator.soundnessShadowTarget := by
  cases generator with
  | corr witness => exact witness.admissibleGeneratorShadow
  | loc witness => exact witness.admissibleGeneratorShadow
  | nis witness => exact witness.admissibleGeneratorShadow
  | a1 witness => exact witness.admissibleGeneratorShadow
  | env witness => exact witness.admissibleGeneratorShadow

theorem envelopeClosureSoundnessShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (generator : AdmissibleGeometricClosureGenerator ctx) :
    generator.envelopeClosureShadowTarget := by
  cases generator with
  | corr => simp [AdmissibleGeometricClosureGenerator.envelopeClosureShadowTarget]
  | loc => simp [AdmissibleGeometricClosureGenerator.envelopeClosureShadowTarget]
  | nis => simp [AdmissibleGeometricClosureGenerator.envelopeClosureShadowTarget]
  | a1 => simp [AdmissibleGeometricClosureGenerator.envelopeClosureShadowTarget]
  | env witness =>
      simpa [AdmissibleGeometricClosureGenerator.envelopeClosureShadowTarget] using witness.formalClosure

end AdmissibleGeometricClosureGenerator

structure AdmissibleComposeClosureWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  comparisonAgreementTarget : Prop
  formalClosureTarget : Prop
  replayData : CertifiedEnvReplayData ctx comparisonAgreementTarget formalClosureTarget
  replayTransformer : EnvReplayTransformerTarget
  replayTransformer_eq :
    replayTransformer =
      EnvReplayTransformerTarget.envCompose_from_certifiedReplay replayData.replayTransformerTarget
  leftInputAdmissibleTarget : Prop
  rightInputAdmissibleTarget : Prop
  outputAdmissibleTarget : Prop
  soundness_holds : outputAdmissibleTarget

namespace AdmissibleComposeClosureWitness

def ofCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedComposeClosureWitness ctx) :
    AdmissibleComposeClosureWitness ctx where
  comparisonAgreementTarget := witness.comparisonAgreementTarget
  formalClosureTarget := witness.formalClosureTarget
  replayData := witness.replayData
  replayTransformer := witness.replayTransformer
  replayTransformer_eq := witness.replayTransformer_eq
  leftInputAdmissibleTarget := witness.leftInputCertifiedTarget
  rightInputAdmissibleTarget := witness.rightInputCertifiedTarget
  outputAdmissibleTarget := witness.outputCertifiedTarget
  soundness_holds := witness.soundness_holds

def toCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleComposeClosureWitness ctx) :
    CertifiedComposeClosureWitness ctx where
  comparisonAgreementTarget := witness.comparisonAgreementTarget
  formalClosureTarget := witness.formalClosureTarget
  replayData := witness.replayData
  replayTransformer := witness.replayTransformer
  replayTransformer_eq := witness.replayTransformer_eq
  leftInputCertifiedTarget := witness.leftInputAdmissibleTarget
  rightInputCertifiedTarget := witness.rightInputAdmissibleTarget
  outputCertifiedTarget := witness.outputAdmissibleTarget
  soundness_holds := witness.soundness_holds

@[simp] theorem toCertifiedWitness_ofCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedComposeClosureWitness ctx) :
    (ofCertifiedWitness witness).toCertifiedWitness = witness := by
  cases witness
  rfl

@[simp] theorem ofCertifiedWitness_toCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleComposeClosureWitness ctx) :
    ofCertifiedWitness witness.toCertifiedWitness = witness := by
  cases witness
  rfl

theorem formalClosureShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleComposeClosureWitness ctx) :
    witness.formalClosureTarget :=
  witness.replayData.formalClosure_holds

end AdmissibleComposeClosureWitness

structure AdmissibleTensorClosureWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  comparisonAgreementTarget : Prop
  formalClosureTarget : Prop
  replayData : CertifiedEnvReplayData ctx comparisonAgreementTarget formalClosureTarget
  replayTransformer : EnvReplayTransformerTarget
  replayTransformer_eq :
    replayTransformer =
      EnvReplayTransformerTarget.envTensor_from_certifiedReplay replayData.replayTransformerTarget
  leftInputAdmissibleTarget : Prop
  rightInputAdmissibleTarget : Prop
  outputAdmissibleTarget : Prop
  soundness_holds : outputAdmissibleTarget

namespace AdmissibleTensorClosureWitness

def ofCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedTensorClosureWitness ctx) :
    AdmissibleTensorClosureWitness ctx where
  comparisonAgreementTarget := witness.comparisonAgreementTarget
  formalClosureTarget := witness.formalClosureTarget
  replayData := witness.replayData
  replayTransformer := witness.replayTransformer
  replayTransformer_eq := witness.replayTransformer_eq
  leftInputAdmissibleTarget := witness.leftInputCertifiedTarget
  rightInputAdmissibleTarget := witness.rightInputCertifiedTarget
  outputAdmissibleTarget := witness.outputCertifiedTarget
  soundness_holds := witness.soundness_holds

def toCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleTensorClosureWitness ctx) :
    CertifiedTensorClosureWitness ctx where
  comparisonAgreementTarget := witness.comparisonAgreementTarget
  formalClosureTarget := witness.formalClosureTarget
  replayData := witness.replayData
  replayTransformer := witness.replayTransformer
  replayTransformer_eq := witness.replayTransformer_eq
  leftInputCertifiedTarget := witness.leftInputAdmissibleTarget
  rightInputCertifiedTarget := witness.rightInputAdmissibleTarget
  outputCertifiedTarget := witness.outputAdmissibleTarget
  soundness_holds := witness.soundness_holds

@[simp] theorem toCertifiedWitness_ofCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedTensorClosureWitness ctx) :
    (ofCertifiedWitness witness).toCertifiedWitness = witness := by
  cases witness
  rfl

@[simp] theorem ofCertifiedWitness_toCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleTensorClosureWitness ctx) :
    ofCertifiedWitness witness.toCertifiedWitness = witness := by
  cases witness
  rfl

theorem formalClosureShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleTensorClosureWitness ctx) :
    witness.formalClosureTarget :=
  witness.replayData.formalClosure_holds

end AdmissibleTensorClosureWitness

structure AdmissibleWhiskerClosureWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  comparisonAgreementTarget : Prop
  formalClosureTarget : Prop
  replayData : CertifiedEnvReplayData ctx comparisonAgreementTarget formalClosureTarget
  replayTransformer : EnvReplayTransformerTarget
  replayTransformer_eq :
    replayTransformer =
      EnvReplayTransformerTarget.envWhisker_from_certifiedReplay replayData.replayTransformerTarget
  inputAdmissibleTarget : Prop
  outputAdmissibleTarget : Prop
  soundness_holds : outputAdmissibleTarget

namespace AdmissibleWhiskerClosureWitness

def ofCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedWhiskerClosureWitness ctx) :
    AdmissibleWhiskerClosureWitness ctx where
  comparisonAgreementTarget := witness.comparisonAgreementTarget
  formalClosureTarget := witness.formalClosureTarget
  replayData := witness.replayData
  replayTransformer := witness.replayTransformer
  replayTransformer_eq := witness.replayTransformer_eq
  inputAdmissibleTarget := witness.inputCertifiedTarget
  outputAdmissibleTarget := witness.outputCertifiedTarget
  soundness_holds := witness.soundness_holds

def toCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleWhiskerClosureWitness ctx) :
    CertifiedWhiskerClosureWitness ctx where
  comparisonAgreementTarget := witness.comparisonAgreementTarget
  formalClosureTarget := witness.formalClosureTarget
  replayData := witness.replayData
  replayTransformer := witness.replayTransformer
  replayTransformer_eq := witness.replayTransformer_eq
  inputCertifiedTarget := witness.inputAdmissibleTarget
  outputCertifiedTarget := witness.outputAdmissibleTarget
  soundness_holds := witness.soundness_holds

@[simp] theorem toCertifiedWitness_ofCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedWhiskerClosureWitness ctx) :
    (ofCertifiedWitness witness).toCertifiedWitness = witness := by
  cases witness
  rfl

@[simp] theorem ofCertifiedWitness_toCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleWhiskerClosureWitness ctx) :
    ofCertifiedWitness witness.toCertifiedWitness = witness := by
  cases witness
  rfl

theorem formalClosureShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleWhiskerClosureWitness ctx) :
    witness.formalClosureTarget :=
  witness.replayData.formalClosure_holds

end AdmissibleWhiskerClosureWitness

structure AdmissibleStructuralAdminClosureWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  comparisonAgreementTarget : Prop
  formalClosureTarget : Prop
  replayData : CertifiedEnvReplayData ctx comparisonAgreementTarget formalClosureTarget
  replayTransformer : EnvReplayTransformerTarget
  replayTransformer_eq :
    replayTransformer =
      EnvReplayTransformerTarget.envStructuralAdmin_from_certifiedReplay
        replayData.replayTransformerTarget
  inputAdmissibleTarget : Prop
  outputAdmissibleTarget : Prop
  soundness_holds : outputAdmissibleTarget

namespace AdmissibleStructuralAdminClosureWitness

def ofCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedStructuralAdminClosureWitness ctx) :
    AdmissibleStructuralAdminClosureWitness ctx where
  comparisonAgreementTarget := witness.comparisonAgreementTarget
  formalClosureTarget := witness.formalClosureTarget
  replayData := witness.replayData
  replayTransformer := witness.replayTransformer
  replayTransformer_eq := witness.replayTransformer_eq
  inputAdmissibleTarget := witness.inputCertifiedTarget
  outputAdmissibleTarget := witness.outputCertifiedTarget
  soundness_holds := witness.soundness_holds

def toCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleStructuralAdminClosureWitness ctx) :
    CertifiedStructuralAdminClosureWitness ctx where
  comparisonAgreementTarget := witness.comparisonAgreementTarget
  formalClosureTarget := witness.formalClosureTarget
  replayData := witness.replayData
  replayTransformer := witness.replayTransformer
  replayTransformer_eq := witness.replayTransformer_eq
  inputCertifiedTarget := witness.inputAdmissibleTarget
  outputCertifiedTarget := witness.outputAdmissibleTarget
  soundness_holds := witness.soundness_holds

@[simp] theorem toCertifiedWitness_ofCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedStructuralAdminClosureWitness ctx) :
    (ofCertifiedWitness witness).toCertifiedWitness = witness := by
  cases witness
  rfl

@[simp] theorem ofCertifiedWitness_toCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleStructuralAdminClosureWitness ctx) :
    ofCertifiedWitness witness.toCertifiedWitness = witness := by
  cases witness
  rfl

theorem formalClosureShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleStructuralAdminClosureWitness ctx) :
    witness.formalClosureTarget :=
  witness.replayData.formalClosure_holds

end AdmissibleStructuralAdminClosureWitness

structure AdmissibleShiftClosureWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  comparisonAgreementTarget : Prop
  formalClosureTarget : Prop
  replayData : CertifiedEnvReplayData ctx comparisonAgreementTarget formalClosureTarget
  replayTransformer : EnvReplayTransformerTarget
  replayTransformer_eq :
    replayTransformer =
      EnvReplayTransformerTarget.envShift_from_certifiedReplay replayData.replayTransformerTarget
  inputAdmissibleTarget : Prop
  outputAdmissibleTarget : Prop
  soundness_holds : outputAdmissibleTarget

namespace AdmissibleShiftClosureWitness

def ofCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedShiftClosureWitness ctx) :
    AdmissibleShiftClosureWitness ctx where
  comparisonAgreementTarget := witness.comparisonAgreementTarget
  formalClosureTarget := witness.formalClosureTarget
  replayData := witness.replayData
  replayTransformer := witness.replayTransformer
  replayTransformer_eq := witness.replayTransformer_eq
  inputAdmissibleTarget := witness.inputCertifiedTarget
  outputAdmissibleTarget := witness.outputCertifiedTarget
  soundness_holds := witness.soundness_holds

def toCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleShiftClosureWitness ctx) :
    CertifiedShiftClosureWitness ctx where
  comparisonAgreementTarget := witness.comparisonAgreementTarget
  formalClosureTarget := witness.formalClosureTarget
  replayData := witness.replayData
  replayTransformer := witness.replayTransformer
  replayTransformer_eq := witness.replayTransformer_eq
  inputCertifiedTarget := witness.inputAdmissibleTarget
  outputCertifiedTarget := witness.outputAdmissibleTarget
  soundness_holds := witness.soundness_holds

@[simp] theorem toCertifiedWitness_ofCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedShiftClosureWitness ctx) :
    (ofCertifiedWitness witness).toCertifiedWitness = witness := by
  cases witness
  rfl

@[simp] theorem ofCertifiedWitness_toCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleShiftClosureWitness ctx) :
    ofCertifiedWitness witness.toCertifiedWitness = witness := by
  cases witness
  rfl

theorem formalClosureShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleShiftClosureWitness ctx) :
    witness.formalClosureTarget :=
  witness.replayData.formalClosure_holds

end AdmissibleShiftClosureWitness

structure AdmissibleConeClosureWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  connectingPacketComparisonTarget : Prop
  locReplayData : CertifiedLocPacketReplayData ctx connectingPacketComparisonTarget
  triangleCompatibilityTarget : Prop
  ambientAdmissibleTarget : Prop
  closedAdmissibleTarget : Prop
  coneAdmissibleTarget : Prop
  connectingMorphismTarget : Prop
  shiftClosedTarget : Prop
  triangleCompatibility_holds : triangleCompatibilityTarget
  soundness_holds : coneAdmissibleTarget

namespace AdmissibleConeClosureWitness

def ofCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedConeClosureWitness ctx) :
    AdmissibleConeClosureWitness ctx where
  connectingPacketComparisonTarget := witness.connectingPacketComparisonTarget
  locReplayData := witness.locReplayData
  triangleCompatibilityTarget := witness.triangleCompatibilityTarget
  ambientAdmissibleTarget := witness.ambientCertifiedTarget
  closedAdmissibleTarget := witness.closedCertifiedTarget
  coneAdmissibleTarget := witness.coneCertifiedTarget
  connectingMorphismTarget := witness.connectingMorphismTarget
  shiftClosedTarget := witness.shiftClosedTarget
  triangleCompatibility_holds := witness.triangleCompatibility_holds
  soundness_holds := witness.soundness_holds

def toCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleConeClosureWitness ctx) :
    CertifiedConeClosureWitness ctx where
  connectingPacketComparisonTarget := witness.connectingPacketComparisonTarget
  locReplayData := witness.locReplayData
  triangleCompatibilityTarget := witness.triangleCompatibilityTarget
  ambientCertifiedTarget := witness.ambientAdmissibleTarget
  closedCertifiedTarget := witness.closedAdmissibleTarget
  coneCertifiedTarget := witness.coneAdmissibleTarget
  connectingMorphismTarget := witness.connectingMorphismTarget
  shiftClosedTarget := witness.shiftClosedTarget
  triangleCompatibility_holds := witness.triangleCompatibility_holds
  soundness_holds := witness.soundness_holds

@[simp] theorem toCertifiedWitness_ofCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedConeClosureWitness ctx) :
    (ofCertifiedWitness witness).toCertifiedWitness = witness := by
  cases witness
  rfl

@[simp] theorem ofCertifiedWitness_toCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleConeClosureWitness ctx) :
    ofCertifiedWitness witness.toCertifiedWitness = witness := by
  cases witness
  rfl

theorem triangleCompatibilityShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleConeClosureWitness ctx) :
    witness.triangleCompatibilityTarget :=
  witness.triangleCompatibility_holds

end AdmissibleConeClosureWitness

structure AdmissibleCofiberClosureWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  connectingPacketComparisonTarget : Prop
  locReplayData : CertifiedLocPacketReplayData ctx connectingPacketComparisonTarget
  triangleCompatibilityTarget : Prop
  sourceAdmissibleTarget : Prop
  targetAdmissibleTarget : Prop
  cofiberAdmissibleTarget : Prop
  connectingMorphismTarget : Prop
  shiftSourceTarget : Prop
  triangleCompatibility_holds : triangleCompatibilityTarget
  soundness_holds : cofiberAdmissibleTarget

namespace AdmissibleCofiberClosureWitness

def ofCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedCofiberClosureWitness ctx) :
    AdmissibleCofiberClosureWitness ctx where
  connectingPacketComparisonTarget := witness.connectingPacketComparisonTarget
  locReplayData := witness.locReplayData
  triangleCompatibilityTarget := witness.triangleCompatibilityTarget
  sourceAdmissibleTarget := witness.sourceCertifiedTarget
  targetAdmissibleTarget := witness.targetCertifiedTarget
  cofiberAdmissibleTarget := witness.cofiberCertifiedTarget
  connectingMorphismTarget := witness.connectingMorphismTarget
  shiftSourceTarget := witness.shiftSourceTarget
  triangleCompatibility_holds := witness.triangleCompatibility_holds
  soundness_holds := witness.soundness_holds

def toCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleCofiberClosureWitness ctx) :
    CertifiedCofiberClosureWitness ctx where
  connectingPacketComparisonTarget := witness.connectingPacketComparisonTarget
  locReplayData := witness.locReplayData
  triangleCompatibilityTarget := witness.triangleCompatibilityTarget
  sourceCertifiedTarget := witness.sourceAdmissibleTarget
  targetCertifiedTarget := witness.targetAdmissibleTarget
  cofiberCertifiedTarget := witness.cofiberAdmissibleTarget
  connectingMorphismTarget := witness.connectingMorphismTarget
  shiftSourceTarget := witness.shiftSourceTarget
  triangleCompatibility_holds := witness.triangleCompatibility_holds
  soundness_holds := witness.soundness_holds

@[simp] theorem toCertifiedWitness_ofCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedCofiberClosureWitness ctx) :
    (ofCertifiedWitness witness).toCertifiedWitness = witness := by
  cases witness
  rfl

@[simp] theorem ofCertifiedWitness_toCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleCofiberClosureWitness ctx) :
    ofCertifiedWitness witness.toCertifiedWitness = witness := by
  cases witness
  rfl

theorem triangleCompatibilityShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleCofiberClosureWitness ctx) :
    witness.triangleCompatibilityTarget :=
  witness.triangleCompatibility_holds

end AdmissibleCofiberClosureWitness

structure AdmissibleRetractClosureWitness
    (ctx : ClassicalComparisonContext.{u, v}) where
  inputAdmissibleTarget : Prop
  retractAdmissibleTarget : Prop
  sectionTarget : Prop
  retractionTarget : Prop
  idempotentCompatibilityTarget : Prop
  idempotentCompatibility_holds : idempotentCompatibilityTarget
  soundness_holds : retractAdmissibleTarget

namespace AdmissibleRetractClosureWitness

def ofCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedRetractClosureWitness ctx) :
    AdmissibleRetractClosureWitness ctx where
  inputAdmissibleTarget := witness.inputCertifiedTarget
  retractAdmissibleTarget := witness.retractCertifiedTarget
  sectionTarget := witness.sectionTarget
  retractionTarget := witness.retractionTarget
  idempotentCompatibilityTarget := witness.idempotentCompatibilityTarget
  idempotentCompatibility_holds := witness.idempotentCompatibility_holds
  soundness_holds := witness.soundness_holds

def toCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleRetractClosureWitness ctx) :
    CertifiedRetractClosureWitness ctx where
  inputCertifiedTarget := witness.inputAdmissibleTarget
  retractCertifiedTarget := witness.retractAdmissibleTarget
  sectionTarget := witness.sectionTarget
  retractionTarget := witness.retractionTarget
  idempotentCompatibilityTarget := witness.idempotentCompatibilityTarget
  idempotentCompatibility_holds := witness.idempotentCompatibility_holds
  soundness_holds := witness.soundness_holds

@[simp] theorem toCertifiedWitness_ofCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : CertifiedRetractClosureWitness ctx) :
    (ofCertifiedWitness witness).toCertifiedWitness = witness := by
  cases witness
  rfl

@[simp] theorem ofCertifiedWitness_toCertifiedWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleRetractClosureWitness ctx) :
    ofCertifiedWitness witness.toCertifiedWitness = witness := by
  cases witness
  rfl

theorem idempotentCompatibilityShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (witness : AdmissibleRetractClosureWitness ctx) :
    witness.idempotentCompatibilityTarget :=
  witness.idempotentCompatibility_holds

end AdmissibleRetractClosureWitness

inductive AdmissibleGeometricClosure
    (ctx : ClassicalComparisonContext.{u, v}) where
  | ofPrimitiveWitnesses :
      PrimitiveAdmissibleGeneratorWitnesses ctx → AdmissibleGeometricClosure ctx
  | seed : AdmissibleGeometricClosureGenerator ctx → AdmissibleGeometricClosure ctx
  | compose :
      AdmissibleGeometricClosure ctx →
      AdmissibleGeometricClosure ctx →
      AdmissibleComposeClosureWitness ctx →
      AdmissibleGeometricClosure ctx
  | tensor :
      AdmissibleGeometricClosure ctx →
      AdmissibleGeometricClosure ctx →
      AdmissibleTensorClosureWitness ctx →
      AdmissibleGeometricClosure ctx
  | whisker :
      AdmissibleGeometricClosure ctx →
      AdmissibleWhiskerClosureWitness ctx →
      AdmissibleGeometricClosure ctx
  | admin :
      AdmissibleGeometricClosure ctx →
      AdmissibleStructuralAdminClosureWitness ctx →
      AdmissibleGeometricClosure ctx
  | shift :
      AdmissibleGeometricClosure ctx →
      AdmissibleShiftClosureWitness ctx →
      AdmissibleGeometricClosure ctx
    | cone :
      AdmissibleGeometricClosure ctx →
      AdmissibleConeClosureWitness ctx →
      AdmissibleGeometricClosure ctx
    | cofiber :
      AdmissibleGeometricClosure ctx →
      AdmissibleCofiberClosureWitness ctx →
      AdmissibleGeometricClosure ctx
    | retract :
      AdmissibleGeometricClosure ctx →
      AdmissibleRetractClosureWitness ctx →
      AdmissibleGeometricClosure ctx

namespace AdmissibleGeometricClosure

def soundnessShadowTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (closure : AdmissibleGeometricClosure ctx) : Prop :=
  match closure with
  | .ofPrimitiveWitnesses witnesses => primitiveWitnessesSoundnessTarget witnesses
  | .seed generator => generator.soundnessShadowTarget
  | .compose left right witness =>
      left.soundnessShadowTarget ∧ right.soundnessShadowTarget ∧ witness.outputAdmissibleTarget
  | .tensor left right witness =>
      left.soundnessShadowTarget ∧ right.soundnessShadowTarget ∧ witness.outputAdmissibleTarget
  | .whisker source witness => source.soundnessShadowTarget ∧ witness.outputAdmissibleTarget
  | .admin source witness => source.soundnessShadowTarget ∧ witness.outputAdmissibleTarget
  | .shift source witness => source.soundnessShadowTarget ∧ witness.outputAdmissibleTarget
  | .cone source witness => source.soundnessShadowTarget ∧ witness.coneAdmissibleTarget
  | .cofiber source witness => source.soundnessShadowTarget ∧ witness.cofiberAdmissibleTarget
  | .retract source witness => source.soundnessShadowTarget ∧ witness.retractAdmissibleTarget

def envelopeClosureShadowTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (closure : AdmissibleGeometricClosure ctx) : Prop :=
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
    (closure : AdmissibleGeometricClosure ctx) :
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
    (closure : AdmissibleGeometricClosure ctx) :
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

end AdmissibleGeometricClosure

def certifiedTraceClosureGenerator_to_admissibleGeometricClosureGenerator
    {ctx : ClassicalComparisonContext.{u, v}}
    (generator : CertifiedTraceClosureGenerator ctx) :
    AdmissibleGeometricClosureGenerator ctx :=
  match generator with
  | .corr witness => .corr witness
  | .loc witness => .loc witness
  | .nis witness => .nis witness
  | .a1 witness => .a1 witness
  | .env witness => .env witness

def admissibleGeometricClosureGenerator_to_certifiedTraceClosureGenerator
    {ctx : ClassicalComparisonContext.{u, v}}
    (generator : AdmissibleGeometricClosureGenerator ctx) :
    CertifiedTraceClosureGenerator ctx :=
  match generator with
  | .corr witness => .corr witness
  | .loc witness => .loc witness
  | .nis witness => .nis witness
  | .a1 witness => .a1 witness
  | .env witness => .env witness

@[simp] theorem admissibleGenerator_of_certifiedGenerator
    {ctx : ClassicalComparisonContext.{u, v}}
    (generator : CertifiedTraceClosureGenerator ctx) :
    admissibleGeometricClosureGenerator_to_certifiedTraceClosureGenerator
      (certifiedTraceClosureGenerator_to_admissibleGeometricClosureGenerator generator) = generator := by
  cases generator <;> rfl

@[simp] theorem certifiedGenerator_of_admissibleGenerator
    {ctx : ClassicalComparisonContext.{u, v}}
    (generator : AdmissibleGeometricClosureGenerator ctx) :
    certifiedTraceClosureGenerator_to_admissibleGeometricClosureGenerator
      (admissibleGeometricClosureGenerator_to_certifiedTraceClosureGenerator generator) = generator := by
  cases generator <;> rfl

def certifiedTraceClosure_to_admissibleGeometricClosure
    {ctx : ClassicalComparisonContext.{u, v}} :
    CertifiedTraceClosure ctx → AdmissibleGeometricClosure ctx
  | .ofPrimitiveWitnesses witnesses => .ofPrimitiveWitnesses witnesses
  | .seed generator => .seed (certifiedTraceClosureGenerator_to_admissibleGeometricClosureGenerator generator)
  | .compose left right witness =>
      .compose (certifiedTraceClosure_to_admissibleGeometricClosure left)
        (certifiedTraceClosure_to_admissibleGeometricClosure right)
        (AdmissibleComposeClosureWitness.ofCertifiedWitness witness)
  | .tensor left right witness =>
      .tensor (certifiedTraceClosure_to_admissibleGeometricClosure left)
        (certifiedTraceClosure_to_admissibleGeometricClosure right)
        (AdmissibleTensorClosureWitness.ofCertifiedWitness witness)
  | .whisker source witness =>
      .whisker (certifiedTraceClosure_to_admissibleGeometricClosure source)
        (AdmissibleWhiskerClosureWitness.ofCertifiedWitness witness)
  | .admin source witness =>
      .admin (certifiedTraceClosure_to_admissibleGeometricClosure source)
        (AdmissibleStructuralAdminClosureWitness.ofCertifiedWitness witness)
  | .shift source witness =>
      .shift (certifiedTraceClosure_to_admissibleGeometricClosure source)
        (AdmissibleShiftClosureWitness.ofCertifiedWitness witness)
  | .cone source witness =>
      .cone (certifiedTraceClosure_to_admissibleGeometricClosure source)
        (AdmissibleConeClosureWitness.ofCertifiedWitness witness)
  | .cofiber source witness =>
      .cofiber (certifiedTraceClosure_to_admissibleGeometricClosure source)
        (AdmissibleCofiberClosureWitness.ofCertifiedWitness witness)
  | .retract source witness =>
      .retract (certifiedTraceClosure_to_admissibleGeometricClosure source)
        (AdmissibleRetractClosureWitness.ofCertifiedWitness witness)

def admissibleGeometricClosure_to_certifiedTraceClosure
    {ctx : ClassicalComparisonContext.{u, v}} :
    AdmissibleGeometricClosure ctx → CertifiedTraceClosure ctx
  | .ofPrimitiveWitnesses witnesses => .ofPrimitiveWitnesses witnesses
  | .seed generator => .seed (admissibleGeometricClosureGenerator_to_certifiedTraceClosureGenerator generator)
  | .compose left right witness =>
      .compose (admissibleGeometricClosure_to_certifiedTraceClosure left)
        (admissibleGeometricClosure_to_certifiedTraceClosure right)
        (AdmissibleComposeClosureWitness.toCertifiedWitness witness)
  | .tensor left right witness =>
      .tensor (admissibleGeometricClosure_to_certifiedTraceClosure left)
        (admissibleGeometricClosure_to_certifiedTraceClosure right)
        (AdmissibleTensorClosureWitness.toCertifiedWitness witness)
  | .whisker source witness =>
      .whisker (admissibleGeometricClosure_to_certifiedTraceClosure source)
        (AdmissibleWhiskerClosureWitness.toCertifiedWitness witness)
  | .admin source witness =>
      .admin (admissibleGeometricClosure_to_certifiedTraceClosure source)
        (AdmissibleStructuralAdminClosureWitness.toCertifiedWitness witness)
  | .shift source witness =>
      .shift (admissibleGeometricClosure_to_certifiedTraceClosure source)
        (AdmissibleShiftClosureWitness.toCertifiedWitness witness)
  | .cone source witness =>
      .cone (admissibleGeometricClosure_to_certifiedTraceClosure source)
        (AdmissibleConeClosureWitness.toCertifiedWitness witness)
  | .cofiber source witness =>
      .cofiber (admissibleGeometricClosure_to_certifiedTraceClosure source)
        (AdmissibleCofiberClosureWitness.toCertifiedWitness witness)
  | .retract source witness =>
      .retract (admissibleGeometricClosure_to_certifiedTraceClosure source)
        (AdmissibleRetractClosureWitness.toCertifiedWitness witness)

@[simp] theorem admissibleGeometricClosure_to_certifiedTraceClosure_left_inv
    {ctx : ClassicalComparisonContext.{u, v}} :
    ∀ closure : CertifiedTraceClosure ctx,
      admissibleGeometricClosure_to_certifiedTraceClosure
        (certifiedTraceClosure_to_admissibleGeometricClosure closure) = closure
  | .ofPrimitiveWitnesses witnesses => rfl
  | .seed generator => by cases generator <;> rfl
  | .compose left right witness => by
      simp [certifiedTraceClosure_to_admissibleGeometricClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure_left_inv left,
        admissibleGeometricClosure_to_certifiedTraceClosure_left_inv right,
        AdmissibleComposeClosureWitness.toCertifiedWitness_ofCertifiedWitness]
  | .tensor left right witness => by
      simp [certifiedTraceClosure_to_admissibleGeometricClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure_left_inv left,
        admissibleGeometricClosure_to_certifiedTraceClosure_left_inv right,
        AdmissibleTensorClosureWitness.toCertifiedWitness_ofCertifiedWitness]
  | .whisker source witness => by
      simp [certifiedTraceClosure_to_admissibleGeometricClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure_left_inv source,
        AdmissibleWhiskerClosureWitness.toCertifiedWitness_ofCertifiedWitness]
  | .admin source witness => by
      simp [certifiedTraceClosure_to_admissibleGeometricClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure_left_inv source,
        AdmissibleStructuralAdminClosureWitness.toCertifiedWitness_ofCertifiedWitness]
  | .shift source witness => by
      simp [certifiedTraceClosure_to_admissibleGeometricClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure_left_inv source,
        AdmissibleShiftClosureWitness.toCertifiedWitness_ofCertifiedWitness]
  | .cone source witness => by
      simp [certifiedTraceClosure_to_admissibleGeometricClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure_left_inv source,
        AdmissibleConeClosureWitness.toCertifiedWitness_ofCertifiedWitness]
  | .cofiber source witness => by
      simp [certifiedTraceClosure_to_admissibleGeometricClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure_left_inv source,
        AdmissibleCofiberClosureWitness.toCertifiedWitness_ofCertifiedWitness]
  | .retract source witness => by
      simp [certifiedTraceClosure_to_admissibleGeometricClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure_left_inv source,
        AdmissibleRetractClosureWitness.toCertifiedWitness_ofCertifiedWitness]

@[simp] theorem certifiedTraceClosure_to_admissibleGeometricClosure_right_inv
    {ctx : ClassicalComparisonContext.{u, v}} :
    ∀ closure : AdmissibleGeometricClosure ctx,
      certifiedTraceClosure_to_admissibleGeometricClosure
        (admissibleGeometricClosure_to_certifiedTraceClosure closure) = closure
  | .ofPrimitiveWitnesses witnesses => rfl
  | .seed generator => by cases generator <;> rfl
  | .compose left right witness => by
      simp [certifiedTraceClosure_to_admissibleGeometricClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure,
        certifiedTraceClosure_to_admissibleGeometricClosure_right_inv left,
        certifiedTraceClosure_to_admissibleGeometricClosure_right_inv right,
        AdmissibleComposeClosureWitness.ofCertifiedWitness_toCertifiedWitness]
  | .tensor left right witness => by
      simp [certifiedTraceClosure_to_admissibleGeometricClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure,
        certifiedTraceClosure_to_admissibleGeometricClosure_right_inv left,
        certifiedTraceClosure_to_admissibleGeometricClosure_right_inv right,
        AdmissibleTensorClosureWitness.ofCertifiedWitness_toCertifiedWitness]
  | .whisker source witness => by
      simp [certifiedTraceClosure_to_admissibleGeometricClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure,
        certifiedTraceClosure_to_admissibleGeometricClosure_right_inv source,
        AdmissibleWhiskerClosureWitness.ofCertifiedWitness_toCertifiedWitness]
  | .admin source witness => by
      simp [certifiedTraceClosure_to_admissibleGeometricClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure,
        certifiedTraceClosure_to_admissibleGeometricClosure_right_inv source,
        AdmissibleStructuralAdminClosureWitness.ofCertifiedWitness_toCertifiedWitness]
  | .shift source witness => by
      simp [certifiedTraceClosure_to_admissibleGeometricClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure,
        certifiedTraceClosure_to_admissibleGeometricClosure_right_inv source,
        AdmissibleShiftClosureWitness.ofCertifiedWitness_toCertifiedWitness]
  | .cone source witness => by
      simp [certifiedTraceClosure_to_admissibleGeometricClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure,
        certifiedTraceClosure_to_admissibleGeometricClosure_right_inv source,
        AdmissibleConeClosureWitness.ofCertifiedWitness_toCertifiedWitness]
  | .cofiber source witness => by
      simp [certifiedTraceClosure_to_admissibleGeometricClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure,
        certifiedTraceClosure_to_admissibleGeometricClosure_right_inv source,
        AdmissibleCofiberClosureWitness.ofCertifiedWitness_toCertifiedWitness]
  | .retract source witness => by
      simp [certifiedTraceClosure_to_admissibleGeometricClosure,
        admissibleGeometricClosure_to_certifiedTraceClosure,
        certifiedTraceClosure_to_admissibleGeometricClosure_right_inv source,
        AdmissibleRetractClosureWitness.ofCertifiedWitness_toCertifiedWitness]

def certifiedTraceClosure_admissibleGeometricClosure_equiv
    {ctx : ClassicalComparisonContext.{u, v}} :
    CertifiedTraceClosure ctx ≃ AdmissibleGeometricClosure ctx where
  toFun := certifiedTraceClosure_to_admissibleGeometricClosure
  invFun := admissibleGeometricClosure_to_certifiedTraceClosure
  left_inv := admissibleGeometricClosure_to_certifiedTraceClosure_left_inv
  right_inv := certifiedTraceClosure_to_admissibleGeometricClosure_right_inv

structure PresentationAdmissibleClosureEquivalence
    (ctx : ClassicalComparisonContext.{u, v}) where
  primitiveWitnesses : PrimitiveAdmissibleGeneratorWitnesses ctx
  equivalence : CertifiedTraceClosure ctx ≃ AdmissibleGeometricClosure ctx

namespace PresentationAdmissibleClosureEquivalence

/-- Construct PresentationAdmissibleClosureEquivalence from certified generator and closure data.
    This is the second real step in the DM_gm(Q) recognition ladder: it packages the primitive witnesses
    and the certified equivalence between trace and admissible geometric closures. -/
def ofCertifiedGeneratorAndClosureData
    {ctx : ClassicalComparisonContext.{u, v}}
    (primitiveWitnesses : PrimitiveAdmissibleGeneratorWitnesses ctx)
    (equivalence : CertifiedTraceClosure ctx ≃ AdmissibleGeometricClosure ctx)
    : PresentationAdmissibleClosureEquivalence ctx :=
  {
    primitiveWitnesses := primitiveWitnesses,
    equivalence := equivalence
  }

def certifiedSeedClosure
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PresentationAdmissibleClosureEquivalence ctx) :
    CertifiedTraceClosure ctx :=
  .ofPrimitiveWitnesses package.primitiveWitnesses

def admissibleSeedClosure
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PresentationAdmissibleClosureEquivalence ctx) :
    AdmissibleGeometricClosure ctx :=
  .ofPrimitiveWitnesses package.primitiveWitnesses

def closureComparisonTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PresentationAdmissibleClosureEquivalence ctx) : Prop :=
  (∀ closure : CertifiedTraceClosure ctx,
      package.equivalence.invFun (package.equivalence.toFun closure) = closure) ∧
    ∀ closure : AdmissibleGeometricClosure ctx,
      package.equivalence.toFun (package.equivalence.invFun closure) = closure

theorem closureComparison
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PresentationAdmissibleClosureEquivalence ctx) :
    package.closureComparisonTarget :=
  ⟨package.equivalence.left_inv, package.equivalence.right_inv⟩

theorem certifiedSeedClosureSoundnessShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PresentationAdmissibleClosureEquivalence ctx) :
    package.certifiedSeedClosure.soundnessShadowTarget :=
  primitiveWitnessesSoundnessShadow package.primitiveWitnesses

theorem admissibleSeedClosureSoundnessShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PresentationAdmissibleClosureEquivalence ctx) :
    package.admissibleSeedClosure.soundnessShadowTarget :=
  primitiveWitnessesSoundnessShadow package.primitiveWitnesses

theorem admissibleSeedEnvelopeClosureShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PresentationAdmissibleClosureEquivalence ctx) :
    package.admissibleSeedClosure.envelopeClosureShadowTarget :=
  primitiveWitnessesEnvelopeClosureShadow package.primitiveWitnesses

end PresentationAdmissibleClosureEquivalence

/-- Proof-relevant bridge from the concrete Campaign 7 packet-family proofs into strengthened
admissible-generator witnesses.

The assignment table remains the root witness. Each family field is now a family-specific typed
admissibility witness, and the older generic `AdmissibleGeneratorCertificate` API is derived from
those witnesses only as a compatibility layer. -/
structure Campaign7AdmissibleGeneratorBridge
    (ctx : ClassicalComparisonContext.{u, v}) where
  assignmentTable : GeneratorRealizationAssignmentTable ctx
  corr : CorrAdmissibleGeneratorWitness ctx
  loc : LocAdmissibleGeneratorWitness ctx
  nis : NisAdmissibleGeneratorWitness ctx
  a1 : A1AdmissibleGeneratorWitness ctx
  env : EnvAdmissibleGeneratorWitness ctx

namespace Campaign7AdmissibleGeneratorBridge

def campaign7Bridge_to_primitiveAdmissibleGeneratorWitnesses
    {ctx : ClassicalComparisonContext.{u, v}}
    (bridge : Campaign7AdmissibleGeneratorBridge ctx) :
    PrimitiveAdmissibleGeneratorWitnesses ctx where
  corr := bridge.corr
  loc := bridge.loc
  nis := bridge.nis
  a1 := bridge.a1
  env := bridge.env

def certifiedTraceClosure
    {ctx : ClassicalComparisonContext.{u, v}}
    (bridge : Campaign7AdmissibleGeneratorBridge ctx) :
    CertifiedTraceClosure ctx :=
  .ofPrimitiveWitnesses bridge.campaign7Bridge_to_primitiveAdmissibleGeneratorWitnesses

def presentationAdmissibleClosureEquivalence
    {ctx : ClassicalComparisonContext.{u, v}}
    (bridge : Campaign7AdmissibleGeneratorBridge ctx) :
    PresentationAdmissibleClosureEquivalence ctx where
  primitiveWitnesses := bridge.campaign7Bridge_to_primitiveAdmissibleGeneratorWitnesses
  equivalence := certifiedTraceClosure_admissibleGeometricClosure_equiv

theorem certifiedTraceClosure_soundnessShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (bridge : Campaign7AdmissibleGeneratorBridge ctx) :
    bridge.certifiedTraceClosure.soundnessShadowTarget :=
  CertifiedTraceClosure.primitiveWitnesses_generate_certifiedTraceClosure
    bridge.campaign7Bridge_to_primitiveAdmissibleGeneratorWitnesses

theorem presentationAdmissibleClosureEquivalence_closureComparison
    {ctx : ClassicalComparisonContext.{u, v}}
    (bridge : Campaign7AdmissibleGeneratorBridge ctx) :
    bridge.presentationAdmissibleClosureEquivalence.closureComparisonTarget :=
  PresentationAdmissibleClosureEquivalence.closureComparison
    bridge.presentationAdmissibleClosureEquivalence

def corrCertificate
    {ctx : ClassicalComparisonContext.{u, v}}
    (bridge : Campaign7AdmissibleGeneratorBridge ctx) :
    AdmissibleGeneratorCertificate ctx :=
  bridge.corr.toAdmissibleGeneratorCertificate

def locCertificate
    {ctx : ClassicalComparisonContext.{u, v}}
    (bridge : Campaign7AdmissibleGeneratorBridge ctx) :
    AdmissibleGeneratorCertificate ctx :=
  bridge.loc.toAdmissibleGeneratorCertificate

def nisCertificate
    {ctx : ClassicalComparisonContext.{u, v}}
    (bridge : Campaign7AdmissibleGeneratorBridge ctx) :
    AdmissibleGeneratorCertificate ctx :=
  bridge.nis.toAdmissibleGeneratorCertificate

def a1Certificate
    {ctx : ClassicalComparisonContext.{u, v}}
    (bridge : Campaign7AdmissibleGeneratorBridge ctx) :
    AdmissibleGeneratorCertificate ctx :=
  bridge.a1.toAdmissibleGeneratorCertificate

def envCertificate
    {ctx : ClassicalComparisonContext.{u, v}}
    (bridge : Campaign7AdmissibleGeneratorBridge ctx) :
    AdmissibleGeneratorCertificate ctx :=
  bridge.env.toAdmissibleGeneratorCertificate

def generatorPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (bridge : Campaign7AdmissibleGeneratorBridge ctx) :
    GeometricGeneratorFamilyPackage ctx :=
  bridge.assignmentTable.toGeometricGeneratorFamilyPackage

def localizationPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (bridge : Campaign7AdmissibleGeneratorBridge ctx) :
    GeometricLocalizationPackage ctx :=
  bridge.assignmentTable.toGeometricLocalizationPackage

def traceToGeometricPacketSoundnessShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (bridge : Campaign7AdmissibleGeneratorBridge ctx) : Prop :=
  let witnesses := bridge.campaign7Bridge_to_primitiveAdmissibleGeneratorWitnesses
  witnesses.corr.admissibleGeneratorTarget ∧
    witnesses.loc.admissibleGeneratorTarget ∧
      witnesses.nis.admissibleGeneratorTarget ∧
        witnesses.a1.admissibleGeneratorTarget ∧
          witnesses.env.admissibleGeneratorTarget

def assignmentTableCompatibilityShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (bridge : Campaign7AdmissibleGeneratorBridge ctx) : Prop :=
  bridge.generatorPackage.realizationCompatibilityTarget ∧
    bridge.localizationPackage.realizationCompatibilityTarget

def primitivePacketFamilySoundnessTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (bridge : Campaign7AdmissibleGeneratorBridge ctx)
    (tracePacketEquivalence : TraceToGeometricPacketEquivalenceTarget ctx) :
    PrimitiveGeometricPacketFamilySoundnessTarget ctx :=
  let witnesses := bridge.campaign7Bridge_to_primitiveAdmissibleGeneratorWitnesses
  PrimitiveGeometricPacketFamilySoundnessTarget.ofPacketEquivalence
    tracePacketEquivalence
    bridge.traceToGeometricPacketSoundnessShadow
    witnesses.corr.admissibleGeneratorTarget
    witnesses.loc.admissibleGeneratorTarget
    witnesses.nis.admissibleGeneratorTarget
    witnesses.a1.admissibleGeneratorTarget
    witnesses.env.admissibleGeneratorTarget
    bridge.assignmentTableCompatibilityShadow

def traceToGeometricSoundnessTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (bridge : Campaign7AdmissibleGeneratorBridge ctx)
    (tracePacketEquivalence : TraceToGeometricPacketEquivalenceTarget ctx) :
    TraceToGeometricSoundnessTarget ctx :=
  TraceToGeometricSoundnessTarget.ofPrimitivePacketFamilySoundness
    (bridge.primitivePacketFamilySoundnessTarget tracePacketEquivalence)

def admissibleSixFunctorGeometryShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (bridge : Campaign7AdmissibleGeneratorBridge ctx) :
    AdmissibleSixFunctorGeometryTarget ctx :=
  let witnesses := bridge.campaign7Bridge_to_primitiveAdmissibleGeneratorWitnesses
  AdmissibleSixFunctorGeometryTarget.ofLocalizationPackage
    bridge.localizationPackage
    (witnesses.loc.admissibleGeneratorTarget ∧
      witnesses.nis.admissibleGeneratorTarget ∧
      witnesses.a1.admissibleGeneratorTarget ∧
      witnesses.env.admissibleGeneratorTarget)
    witnesses.env.formalClosureTarget

def ofAssignmentTable
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    Campaign7AdmissibleGeneratorBridge ctx where
  assignmentTable := assignmentTable
  corr :=
    { realization := assignmentTable.realization
      row := assignmentTable.corrAssignment.family
      sourceSoundnessTarget :=
        CorrPacketSoundnessFromGeneratorRealizationTarget assignmentTable
      sourceSoundness := corrPacketSoundnessFromGeneratorRealization assignmentTable
      soundnessToAdmissibleGenerators := by
        intro h gen
        rcases h gen with ⟨hCorr, hSource, hTarget⟩
        refine ⟨hCorr, ?_, ?_⟩
        · rw [CorrGeneratorRealizationAssignment.sourceComparisonDatum_eq_familyData
            (assignment := assignmentTable.corrAssignment) gen]
          exact hSource
        · rw [CorrGeneratorRealizationAssignment.targetComparisonDatum_eq_familyData
            (assignment := assignmentTable.corrAssignment) gen]
          exact hTarget }
  loc :=
    { realization := assignmentTable.realization
      row := assignmentTable.locAssignment.family
      sourceSoundnessTarget :=
        LocPacketPeriodCompatibilityFromGeneratorRealizationTarget assignmentTable ∧
          assignmentTable.locAssignment.triangleCompatibilityTarget
      sourceSoundness := locPacketSoundnessFromGeneratorRealization assignmentTable
      localizationTriangleTarget := assignmentTable.locAssignment.triangleCompatibilityTarget
      soundnessToAdmissibleGenerators := by
        intro h gen
        rcases h.1 gen with ⟨hAmbient, hOpen, hClosed⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [LocGeneratorRealizationAssignment.ambientComparisonDatum_eq_familyData
            (assignment := assignmentTable.locAssignment) gen]
          exact hAmbient
        · rw [LocGeneratorRealizationAssignment.openComparisonDatum_eq_familyData
            (assignment := assignmentTable.locAssignment) gen]
          exact hOpen
        · rw [LocGeneratorRealizationAssignment.closedComparisonDatum_eq_familyData
            (assignment := assignmentTable.locAssignment) gen]
          exact hClosed
      soundnessToLocalizationTriangle := fun h => h.2 }
  nis :=
    { realization := assignmentTable.realization
      row := assignmentTable.nisAssignment.family
      sourceSoundnessTarget :=
        NisPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
          assignmentTable.nisAssignment.descentSquareCompatibilityTarget
      sourceSoundness := nisPacketSoundnessFromGeneratorRealization assignmentTable
      descentSquareCompatibilityTarget := assignmentTable.nisAssignment.descentSquareCompatibilityTarget
      soundnessToAdmissibleGenerators := by
        intro h gen
        rcases h.1 gen with ⟨hBase, hPatch, hOverlap⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [NisGeneratorRealizationAssignment.baseComparisonDatum_eq_familyData
            (assignment := assignmentTable.nisAssignment) gen]
          exact hBase
        · rw [NisGeneratorRealizationAssignment.patchComparisonDatum_eq_familyData
            (assignment := assignmentTable.nisAssignment) gen]
          exact hPatch
        · rw [NisGeneratorRealizationAssignment.overlapComparisonDatum_eq_familyData
            (assignment := assignmentTable.nisAssignment) gen]
          exact hOverlap
      soundnessToDescentSquareCompatibility := fun h => h.2 }
  a1 :=
    { realization := assignmentTable.realization
      row := assignmentTable.a1Assignment.family
      sourceSoundnessTarget :=
        A1PacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
          assignmentTable.a1Assignment.framedExtractionTarget
      sourceSoundness := a1PacketSoundnessFromGeneratorRealization assignmentTable
      homotopyInvarianceTarget := assignmentTable.a1Assignment.framedExtractionTarget
      soundnessToAdmissibleGenerators := by
        intro h gen
        rcases h.1 gen with ⟨hBaseGroth, hCylinderGroth, hBasePeriod, hCylinderPeriod⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [A1GeneratorRealizationAssignment.baseComparisonDatum_eq_familyData
            (assignment := assignmentTable.a1Assignment) gen]
          exact hBaseGroth
        · rw [A1GeneratorRealizationAssignment.cylinderComparisonDatum_eq_familyData
            (assignment := assignmentTable.a1Assignment) gen]
          exact hCylinderGroth
        · rw [A1GeneratorRealizationAssignment.baseComparisonDatum_eq_familyData
            (assignment := assignmentTable.a1Assignment) gen]
          exact hBasePeriod
        · rw [A1GeneratorRealizationAssignment.cylinderComparisonDatum_eq_familyData
            (assignment := assignmentTable.a1Assignment) gen]
          exact hCylinderPeriod
      soundnessToHomotopyInvariance := fun h => h.2 }
  env :=
    { realization := assignmentTable.realization
      row := assignmentTable.envAssignment.family
      sourceSoundnessTarget :=
        EnvPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
          assignmentTable.envAssignment.exactCompletionTarget
      sourceSoundness := envPacketSoundnessFromGeneratorRealization assignmentTable
      formalClosureTarget := assignmentTable.envAssignment.exactCompletionTarget
      correspondenceAdmissibility := fun gen =>
        assignmentTable.envAssignment.family.envelopeCorrespondenceTarget gen
      soundnessToComparisonAdmissibility := by
        intro h gen
        rcases h.1 gen with ⟨hAmbientGroth, hEnvelopeGroth, hAmbientPeriod, hEnvelopePeriod⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [EnvGeneratorRealizationAssignment.ambientComparisonDatum_eq_familyData
            (assignment := assignmentTable.envAssignment) gen]
          exact hAmbientGroth
        · rw [EnvGeneratorRealizationAssignment.envelopeComparisonDatum_eq_familyData
            (assignment := assignmentTable.envAssignment) gen]
          exact hEnvelopeGroth
        · rw [EnvGeneratorRealizationAssignment.ambientComparisonDatum_eq_familyData
            (assignment := assignmentTable.envAssignment) gen]
          exact hAmbientPeriod
        · rw [EnvGeneratorRealizationAssignment.envelopeComparisonDatum_eq_familyData
            (assignment := assignmentTable.envAssignment) gen]
          exact hEnvelopePeriod
      soundnessToFormalClosure := fun h => h.2 }

@[simp] theorem ofAssignmentTable_generatorPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    (ofAssignmentTable assignmentTable).generatorPackage =
      assignmentTable.toGeometricGeneratorFamilyPackage :=
  rfl

@[simp] theorem ofAssignmentTable_localizationPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    (ofAssignmentTable assignmentTable).localizationPackage =
      assignmentTable.toGeometricLocalizationPackage :=
  rfl

end Campaign7AdmissibleGeneratorBridge

end ClassicalPeriods
end TraceCalc