import TraceCalc.ClassicalPeriods.AdmissibleGeneratorBridge

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

structure TraceObject
    (ctx : ClassicalComparisonContext.{u, v}) where
  geometricObject : GeometricPeriodObject ctx
  identityCertifiedClosure : CertifiedTraceClosure ctx
  identitySoundness : identityCertifiedClosure.soundnessShadowTarget

namespace TraceObject

def ofGeometricObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (geometricObject : GeometricPeriodObject ctx)
    (identityCertifiedClosure : CertifiedTraceClosure ctx)
    (identitySoundness : identityCertifiedClosure.soundnessShadowTarget) :
    TraceObject ctx where
  geometricObject := geometricObject
  identityCertifiedClosure := identityCertifiedClosure
  identitySoundness := identitySoundness

def ofPresentationPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PresentationAdmissibleClosureEquivalence ctx)
    (geometricObject : GeometricPeriodObject ctx) :
    TraceObject ctx :=
  ofGeometricObject geometricObject package.certifiedSeedClosure
    package.certifiedSeedClosureSoundnessShadow

structure TensorWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (left right : TraceObject ctx) where
  tensorObject : GeometricPeriodObject ctx
  identityClosure : CertifiedTraceClosure ctx
  realizationDefined : tensorObject.realizationDefinedTarget
  geometricAdmissibility : tensorObject.geometricAdmissibilityTarget
  identitySoundness : identityClosure.soundnessShadowTarget

def tensorWith
    {ctx : ClassicalComparisonContext.{u, v}}
    (left right : TraceObject ctx)
    (witness : TensorWitness left right) :
    TraceObject ctx :=
  ofGeometricObject witness.tensorObject witness.identityClosure witness.identitySoundness

structure ShiftWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (source : TraceObject ctx) where
  shiftedObject : GeometricPeriodObject ctx
  identityClosure : CertifiedTraceClosure ctx
  realizationDefined : shiftedObject.realizationDefinedTarget
  geometricAdmissibility : shiftedObject.geometricAdmissibilityTarget
  identitySoundness : identityClosure.soundnessShadowTarget

def shiftWith
    {ctx : ClassicalComparisonContext.{u, v}}
    (source : TraceObject ctx)
    (witness : ShiftWitness source) :
    TraceObject ctx :=
  ofGeometricObject witness.shiftedObject witness.identityClosure witness.identitySoundness

end TraceObject

structure TraceMorphism
    (ctx : ClassicalComparisonContext.{u, v})
    (source target : TraceObject ctx) where
  closure : CertifiedTraceClosure ctx
  sourceRealizationWitness : source.geometricObject.realizationDefinedTarget
  targetRealizationWitness : target.geometricObject.realizationDefinedTarget
  sourceAdmissibilityWitness : source.geometricObject.geometricAdmissibilityTarget
  targetAdmissibilityWitness : target.geometricObject.geometricAdmissibilityTarget
  certifiedSoundness : closure.soundnessShadowTarget

namespace TraceMorphism

structure Equiv
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : TraceObject ctx}
    (left right : TraceMorphism ctx source target) where
  closureEq : left.closure = right.closure

theorem Equiv.refl
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : TraceObject ctx}
    (morphism : TraceMorphism ctx source target) :
    Equiv morphism morphism :=
  ⟨rfl⟩

theorem Equiv.symm
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : TraceObject ctx}
    {left right : TraceMorphism ctx source target}
    (h : Equiv left right) :
    Equiv right left :=
  ⟨h.closureEq.symm⟩

theorem Equiv.trans
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : TraceObject ctx}
    {left middle right : TraceMorphism ctx source target}
    (h₁ : Equiv left middle)
    (h₂ : Equiv middle right) :
    Equiv left right :=
  ⟨h₁.closureEq.trans h₂.closureEq⟩

structure CertifiedIdentityTraceWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (X : TraceObject ctx) where
  identityClosure : CertifiedTraceClosure ctx
  sourceRealizationWitness : X.geometricObject.realizationDefinedTarget
  targetRealizationWitness : X.geometricObject.realizationDefinedTarget
  admissibilityWitness : X.geometricObject.geometricAdmissibilityTarget
  leftUnitReplayTarget : Prop
  rightUnitReplayTarget : Prop
  soundness : identityClosure.soundnessShadowTarget

def id
    {ctx : ClassicalComparisonContext.{u, v}}
    (X : TraceObject ctx)
    (witness : CertifiedIdentityTraceWitness X) :
    TraceMorphism ctx X X where
  closure := witness.identityClosure
  sourceRealizationWitness := witness.sourceRealizationWitness
  targetRealizationWitness := witness.targetRealizationWitness
  sourceAdmissibilityWitness := witness.admissibilityWitness
  targetAdmissibilityWitness := witness.admissibilityWitness
  certifiedSoundness := witness.soundness

structure CertifiedIdentityCongruenceWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    {X : TraceObject ctx}
    (left right : CertifiedIdentityTraceWitness X) where
  identityEq : left.identityClosure = right.identityClosure

theorem identity_respects_equivalence
    {ctx : ClassicalComparisonContext.{u, v}}
    {X : TraceObject ctx}
    {left right : CertifiedIdentityTraceWitness X}
    (witness : CertifiedIdentityCongruenceWitness left right) :
    Equiv (id X left) (id X right) :=
  ⟨witness.identityEq⟩

structure CertifiedCompositionWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y Z : TraceObject ctx}
    (left : TraceMorphism ctx X Y)
    (right : TraceMorphism ctx Y Z) where
  composeClosureWitness : CertifiedComposeClosureWitness ctx
  boundaryGluingTarget : Prop
  replayCompatibilityTarget : Prop

def comp
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y Z : TraceObject ctx}
    (left : TraceMorphism ctx X Y)
    (right : TraceMorphism ctx Y Z)
    (witness : CertifiedCompositionWitness left right) :
    TraceMorphism ctx X Z where
  closure := .compose left.closure right.closure witness.composeClosureWitness
  sourceRealizationWitness := left.sourceRealizationWitness
  targetRealizationWitness := right.targetRealizationWitness
  sourceAdmissibilityWitness := left.sourceAdmissibilityWitness
  targetAdmissibilityWitness := right.targetAdmissibilityWitness
  certifiedSoundness := CertifiedTraceClosure.soundnessShadow _

structure CertifiedCompositionCongruenceWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y Z : TraceObject ctx}
    {left₁ left₂ : TraceMorphism ctx X Y}
    {right₁ right₂ : TraceMorphism ctx Y Z}
    (compWitness₁ : CertifiedCompositionWitness left₁ right₁)
    (compWitness₂ : CertifiedCompositionWitness left₂ right₂) where
  composedClosureEq :
    (comp left₁ right₁ compWitness₁).closure =
      (comp left₂ right₂ compWitness₂).closure

theorem comp_respects_equivalence
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y Z : TraceObject ctx}
    {left₁ left₂ : TraceMorphism ctx X Y}
    {right₁ right₂ : TraceMorphism ctx Y Z}
    (hLeft : Equiv left₁ left₂)
    (hRight : Equiv right₁ right₂)
    {compWitness₁ : CertifiedCompositionWitness left₁ right₁}
    {compWitness₂ : CertifiedCompositionWitness left₂ right₂}
    (witness : CertifiedCompositionCongruenceWitness compWitness₁ compWitness₂) :
    Equiv (comp left₁ right₁ compWitness₁) (comp left₂ right₂ compWitness₂) :=
  ⟨witness.composedClosureEq⟩

structure CertifiedLeftUnitReplayWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : TraceObject ctx}
    (identityWitness : CertifiedIdentityTraceWitness X)
    (morphism : TraceMorphism ctx X Y)
    (compWitness : CertifiedCompositionWitness (id X identityWitness) morphism) where
  leftUnitEq : (comp (id X identityWitness) morphism compWitness).closure = morphism.closure

theorem id_comp
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : TraceObject ctx}
    (identityWitness : CertifiedIdentityTraceWitness X)
    (morphism : TraceMorphism ctx X Y)
    (compWitness : CertifiedCompositionWitness (id X identityWitness) morphism)
    (witness : CertifiedLeftUnitReplayWitness identityWitness morphism compWitness) :
    Equiv (comp (id X identityWitness) morphism compWitness) morphism :=
  ⟨witness.leftUnitEq⟩

structure CertifiedRightUnitReplayWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : TraceObject ctx}
    (morphism : TraceMorphism ctx X Y)
    (identityWitness : CertifiedIdentityTraceWitness Y)
    (compWitness : CertifiedCompositionWitness morphism (id Y identityWitness)) where
  rightUnitEq : (comp morphism (id Y identityWitness) compWitness).closure = morphism.closure

theorem comp_id
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : TraceObject ctx}
    (morphism : TraceMorphism ctx X Y)
    (identityWitness : CertifiedIdentityTraceWitness Y)
    (compWitness : CertifiedCompositionWitness morphism (id Y identityWitness))
    (witness : CertifiedRightUnitReplayWitness morphism identityWitness compWitness) :
    Equiv (comp morphism (id Y identityWitness) compWitness) morphism :=
  ⟨witness.rightUnitEq⟩

structure CertifiedAssociativityReplayWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    {W X Y Z : TraceObject ctx}
    (f : TraceMorphism ctx W X)
    (g : TraceMorphism ctx X Y)
    (h : TraceMorphism ctx Y Z)
    (fgWitness : CertifiedCompositionWitness f g)
    (leftWitness : CertifiedCompositionWitness (comp f g fgWitness) h)
    (ghWitness : CertifiedCompositionWitness g h)
    (rightWitness : CertifiedCompositionWitness f (comp g h ghWitness)) where
  associativityEq :
    (comp (comp f g fgWitness) h leftWitness).closure =
      (comp f (comp g h ghWitness) rightWitness).closure

theorem assoc
    {ctx : ClassicalComparisonContext.{u, v}}
    {W X Y Z : TraceObject ctx}
    (f : TraceMorphism ctx W X)
    (g : TraceMorphism ctx X Y)
    (h : TraceMorphism ctx Y Z)
    (fgWitness : CertifiedCompositionWitness f g)
    (leftWitness : CertifiedCompositionWitness (comp f g fgWitness) h)
    (ghWitness : CertifiedCompositionWitness g h)
    (rightWitness : CertifiedCompositionWitness f (comp g h ghWitness))
    (witness : CertifiedAssociativityReplayWitness f g h fgWitness leftWitness ghWitness rightWitness) :
    Equiv (comp (comp f g fgWitness) h leftWitness)
      (comp f (comp g h ghWitness) rightWitness) :=
  ⟨witness.associativityEq⟩

structure CertifiedTensorMorphismWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y X' Y' : TraceObject ctx}
    (left : TraceMorphism ctx X Y)
    (right : TraceMorphism ctx X' Y') where
  sourceTensorWitness : TraceObject.TensorWitness X X'
  targetTensorWitness : TraceObject.TensorWitness Y Y'
  tensorClosureWitness : CertifiedTensorClosureWitness ctx
  boundaryTensorTarget : Prop

def tensor
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y X' Y' : TraceObject ctx}
    (left : TraceMorphism ctx X Y)
    (right : TraceMorphism ctx X' Y')
    (witness : CertifiedTensorMorphismWitness left right) :
    TraceMorphism ctx
      (TraceObject.tensorWith X X' witness.sourceTensorWitness)
      (TraceObject.tensorWith Y Y' witness.targetTensorWitness) where
  closure := CertifiedTraceClosure.tensor left.closure right.closure witness.tensorClosureWitness
  sourceRealizationWitness := witness.sourceTensorWitness.realizationDefined
  targetRealizationWitness := witness.targetTensorWitness.realizationDefined
  sourceAdmissibilityWitness := witness.sourceTensorWitness.geometricAdmissibility
  targetAdmissibilityWitness := witness.targetTensorWitness.geometricAdmissibility
  certifiedSoundness := CertifiedTraceClosure.soundnessShadow _

structure CertifiedTensorIdentityWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    {X X' : TraceObject ctx}
    (leftIdentity : CertifiedIdentityTraceWitness X)
    (rightIdentity : CertifiedIdentityTraceWitness X')
    (tensorWitness : CertifiedTensorMorphismWitness (id X leftIdentity) (id X' rightIdentity))
    (targetIdentity : CertifiedIdentityTraceWitness
      (TraceObject.tensorWith X X' tensorWitness.sourceTensorWitness)) where
  tensorIdEq :
    (tensor (id X leftIdentity) (id X' rightIdentity) tensorWitness).closure =
      (id _ targetIdentity).closure

theorem tensor_id
    {ctx : ClassicalComparisonContext.{u, v}}
    {X X' : TraceObject ctx}
    (leftIdentity : CertifiedIdentityTraceWitness X)
    (rightIdentity : CertifiedIdentityTraceWitness X')
    (tensorWitness : CertifiedTensorMorphismWitness (id X leftIdentity) (id X' rightIdentity))
    (targetIdentity : CertifiedIdentityTraceWitness
      (TraceObject.tensorWith X X' tensorWitness.sourceTensorWitness))
    (witness : CertifiedTensorIdentityWitness leftIdentity rightIdentity tensorWitness targetIdentity) :
    (tensor (id X leftIdentity) (id X' rightIdentity) tensorWitness).closure =
      (id _ targetIdentity).closure :=
  witness.tensorIdEq

structure CertifiedTensorCompositionWitness
    {ctx : ClassicalComparisonContext.{u, v}}
  {W X Y : TraceObject ctx}
  {W' X' Y' : TraceObject ctx}
    (f : TraceMorphism ctx W X)
    (g : TraceMorphism ctx X Y)
    (f' : TraceMorphism ctx W' X')
    (g' : TraceMorphism ctx X' Y')
    (fgWitness : CertifiedCompositionWitness f g)
    (f'g'Witness : CertifiedCompositionWitness f' g')
    (leftTensorWitness : CertifiedTensorMorphismWitness f f')
    (rightTensorWitness : CertifiedTensorMorphismWitness g g')
    (tensorCompClosureWitness : CertifiedComposeClosureWitness ctx)
    (compTensorClosureWitness : CertifiedTensorClosureWitness ctx) where
  tensorCompEq :
    CertifiedTraceClosure.compose
        (CertifiedTraceClosure.tensor f.closure f'.closure leftTensorWitness.tensorClosureWitness)
        (CertifiedTraceClosure.tensor g.closure g'.closure rightTensorWitness.tensorClosureWitness)
        tensorCompClosureWitness =
      CertifiedTraceClosure.tensor
        (CertifiedTraceClosure.compose f.closure g.closure fgWitness.composeClosureWitness)
        (CertifiedTraceClosure.compose f'.closure g'.closure f'g'Witness.composeClosureWitness)
        compTensorClosureWitness

theorem tensor_comp
    {ctx : ClassicalComparisonContext.{u, v}}
    {W X Y : TraceObject ctx}
    {W' X' Y' : TraceObject ctx}
    (f : TraceMorphism ctx W X)
    (g : TraceMorphism ctx X Y)
    (f' : TraceMorphism ctx W' X')
    (g' : TraceMorphism ctx X' Y')
    (fgWitness : CertifiedCompositionWitness f g)
    (f'g'Witness : CertifiedCompositionWitness f' g')
    (leftTensorWitness : CertifiedTensorMorphismWitness f f')
    (rightTensorWitness : CertifiedTensorMorphismWitness g g')
    (tensorCompClosureWitness : CertifiedComposeClosureWitness ctx)
    (compTensorClosureWitness : CertifiedTensorClosureWitness ctx)
    (witness : CertifiedTensorCompositionWitness f g f' g' fgWitness f'g'Witness
      leftTensorWitness rightTensorWitness tensorCompClosureWitness compTensorClosureWitness) :
    CertifiedTraceClosure.compose
        (CertifiedTraceClosure.tensor f.closure f'.closure leftTensorWitness.tensorClosureWitness)
        (CertifiedTraceClosure.tensor g.closure g'.closure rightTensorWitness.tensorClosureWitness)
        tensorCompClosureWitness =
      CertifiedTraceClosure.tensor
        (CertifiedTraceClosure.compose f.closure g.closure fgWitness.composeClosureWitness)
        (CertifiedTraceClosure.compose f'.closure g'.closure f'g'Witness.composeClosureWitness)
        compTensorClosureWitness :=
  witness.tensorCompEq

structure CertifiedAssociatorWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (leftAssociated rightAssociated : TraceObject ctx) where
  forward : TraceMorphism ctx leftAssociated rightAssociated
  inverse : TraceMorphism ctx rightAssociated leftAssociated
  forwardInverseTarget : Prop
  backwardInverseTarget : Prop

structure CertifiedLeftUnitorWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (source target : TraceObject ctx) where
  forward : TraceMorphism ctx source target
  inverse : TraceMorphism ctx target source
  forwardInverseTarget : Prop
  backwardInverseTarget : Prop

structure CertifiedRightUnitorWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (source target : TraceObject ctx) where
  forward : TraceMorphism ctx source target
  inverse : TraceMorphism ctx target source
  forwardInverseTarget : Prop
  backwardInverseTarget : Prop

structure CertifiedBraidingWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (source target : TraceObject ctx) where
  braiding : TraceMorphism ctx source target
  inverseBraiding : TraceMorphism ctx target source
  leftInverseTarget : Prop
  rightInverseTarget : Prop

structure CertifiedShiftMorphismWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : TraceObject ctx}
    (morphism : TraceMorphism ctx X Y) where
  sourceShiftWitness : TraceObject.ShiftWitness X
  targetShiftWitness : TraceObject.ShiftWitness Y
  shiftClosureWitness : CertifiedShiftClosureWitness ctx
  replayCompatibilityTarget : Prop

def shift
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : TraceObject ctx}
    (morphism : TraceMorphism ctx X Y)
    (witness : CertifiedShiftMorphismWitness morphism) :
    TraceMorphism ctx
      (TraceObject.shiftWith X witness.sourceShiftWitness)
      (TraceObject.shiftWith Y witness.targetShiftWitness) where
  closure := CertifiedTraceClosure.shift morphism.closure witness.shiftClosureWitness
  sourceRealizationWitness := witness.sourceShiftWitness.realizationDefined
  targetRealizationWitness := witness.targetShiftWitness.realizationDefined
  sourceAdmissibilityWitness := witness.sourceShiftWitness.geometricAdmissibility
  targetAdmissibilityWitness := witness.targetShiftWitness.geometricAdmissibility
  certifiedSoundness := CertifiedTraceClosure.soundnessShadow _

structure CertifiedShiftIdentityWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    {X : TraceObject ctx}
    (identityWitness : CertifiedIdentityTraceWitness X)
    (shiftWitness : CertifiedShiftMorphismWitness (id X identityWitness))
    (targetIdentity : CertifiedIdentityTraceWitness
      (TraceObject.shiftWith X shiftWitness.sourceShiftWitness)) where
  shiftIdEq : (shift (id X identityWitness) shiftWitness).closure = (id _ targetIdentity).closure

theorem shift_id
    {ctx : ClassicalComparisonContext.{u, v}}
    {X : TraceObject ctx}
    (identityWitness : CertifiedIdentityTraceWitness X)
    (shiftWitness : CertifiedShiftMorphismWitness (id X identityWitness))
    (targetIdentity : CertifiedIdentityTraceWitness
      (TraceObject.shiftWith X shiftWitness.sourceShiftWitness))
    (witness : CertifiedShiftIdentityWitness identityWitness shiftWitness targetIdentity) :
    (shift (id X identityWitness) shiftWitness).closure = (id _ targetIdentity).closure :=
  witness.shiftIdEq

structure CertifiedShiftCompositionWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y Z : TraceObject ctx}
    (f : TraceMorphism ctx X Y)
    (g : TraceMorphism ctx Y Z)
    (fgWitness : CertifiedCompositionWitness f g)
    (leftShiftWitness : CertifiedShiftMorphismWitness f)
    (rightShiftWitness : CertifiedShiftMorphismWitness g)
    (shiftCompClosureWitness : CertifiedComposeClosureWitness ctx)
    (compShiftClosureWitness : CertifiedShiftClosureWitness ctx) where
  shiftCompEq :
    CertifiedTraceClosure.compose
        (CertifiedTraceClosure.shift f.closure leftShiftWitness.shiftClosureWitness)
        (CertifiedTraceClosure.shift g.closure rightShiftWitness.shiftClosureWitness)
        shiftCompClosureWitness =
      CertifiedTraceClosure.shift
        (CertifiedTraceClosure.compose f.closure g.closure fgWitness.composeClosureWitness)
        compShiftClosureWitness

theorem shift_comp
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y Z : TraceObject ctx}
    (f : TraceMorphism ctx X Y)
    (g : TraceMorphism ctx Y Z)
    (fgWitness : CertifiedCompositionWitness f g)
    (leftShiftWitness : CertifiedShiftMorphismWitness f)
    (rightShiftWitness : CertifiedShiftMorphismWitness g)
    (shiftCompClosureWitness : CertifiedComposeClosureWitness ctx)
    (compShiftClosureWitness : CertifiedShiftClosureWitness ctx)
    (witness : CertifiedShiftCompositionWitness f g fgWitness leftShiftWitness rightShiftWitness
      shiftCompClosureWitness compShiftClosureWitness) :
    CertifiedTraceClosure.compose
        (CertifiedTraceClosure.shift f.closure leftShiftWitness.shiftClosureWitness)
        (CertifiedTraceClosure.shift g.closure rightShiftWitness.shiftClosureWitness)
        shiftCompClosureWitness =
      CertifiedTraceClosure.shift
        (CertifiedTraceClosure.compose f.closure g.closure fgWitness.composeClosureWitness)
        compShiftClosureWitness :=
  witness.shiftCompEq

structure CertifiedShiftTensorCompatibilityWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y X' Y' : TraceObject ctx}
    (left : TraceMorphism ctx X Y)
    (right : TraceMorphism ctx X' Y')
    (tensorWitness : CertifiedTensorMorphismWitness left right)
    (leftShiftWitness : CertifiedShiftMorphismWitness left)
    (rightShiftWitness : CertifiedShiftMorphismWitness right)
    (shiftedTensorWitness : CertifiedShiftMorphismWitness (tensor left right tensorWitness))
    (tensorShiftWitness : CertifiedTensorMorphismWitness
      (shift left leftShiftWitness)
      (shift right rightShiftWitness)) where
  shiftTensorEq :
    (shift (tensor left right tensorWitness) shiftedTensorWitness).closure =
      (tensor (shift left leftShiftWitness) (shift right rightShiftWitness) tensorShiftWitness).closure

theorem shift_tensor_compat
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y X' Y' : TraceObject ctx}
    (left : TraceMorphism ctx X Y)
    (right : TraceMorphism ctx X' Y')
    (tensorWitness : CertifiedTensorMorphismWitness left right)
    (leftShiftWitness : CertifiedShiftMorphismWitness left)
    (rightShiftWitness : CertifiedShiftMorphismWitness right)
    (shiftedTensorWitness : CertifiedShiftMorphismWitness (tensor left right tensorWitness))
    (tensorShiftWitness : CertifiedTensorMorphismWitness
      (shift left leftShiftWitness)
      (shift right rightShiftWitness))
    (witness : CertifiedShiftTensorCompatibilityWitness left right tensorWitness leftShiftWitness
      rightShiftWitness shiftedTensorWitness tensorShiftWitness) :
    (shift (tensor left right tensorWitness) shiftedTensorWitness).closure =
      (tensor (shift left leftShiftWitness) (shift right rightShiftWitness) tensorShiftWitness).closure :=
  witness.shiftTensorEq

structure CertifiedConeWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : TraceObject ctx}
    (morphism : TraceMorphism ctx X Y) where
  coneObject : TraceObject ctx
  coneClosureWitness : CertifiedConeClosureWitness ctx
  connectingMorphism : TraceMorphism ctx coneObject coneObject
  locReplayTarget : morphism.closure.soundnessShadowTarget
  triangleBoundaryWitness : Prop

def cone
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : TraceObject ctx}
    (morphism : TraceMorphism ctx X Y)
    (witness : CertifiedConeWitness morphism) :
    TraceMorphism ctx witness.coneObject witness.coneObject :=
  witness.connectingMorphism

theorem cone_soundness_from_Loc_replay
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : TraceObject ctx}
    (morphism : TraceMorphism ctx X Y)
    (witness : CertifiedConeWitness morphism) :
    witness.coneClosureWitness.connectingPacketComparisonTarget :=
  witness.coneClosureWitness.connectingPacketComparisonShadow

structure CertifiedConeTriangleWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : TraceObject ctx}
    (morphism : TraceMorphism ctx X Y)
    (witness : CertifiedConeWitness morphism) where
  coneTriangleTarget : Prop
  triangleCompatibility : witness.coneClosureWitness.triangleCompatibilityTarget

theorem cone_triangle
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : TraceObject ctx}
    (morphism : TraceMorphism ctx X Y)
    (witness : CertifiedConeWitness morphism)
    (triangleWitness : CertifiedConeTriangleWitness morphism witness) :
    witness.coneClosureWitness.triangleCompatibilityTarget :=
  triangleWitness.triangleCompatibility

structure CertifiedCofiberWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : TraceObject ctx}
    (morphism : TraceMorphism ctx X Y) where
  cofiberObject : TraceObject ctx
  cofiberClosureWitness : CertifiedCofiberClosureWitness ctx
  connectingMorphism : TraceMorphism ctx cofiberObject cofiberObject
  locReplayTarget : morphism.closure.soundnessShadowTarget
  cofiberBoundaryWitness : Prop

def cofiber
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : TraceObject ctx}
    (morphism : TraceMorphism ctx X Y)
    (witness : CertifiedCofiberWitness morphism) :
    TraceMorphism ctx witness.cofiberObject witness.cofiberObject :=
  witness.connectingMorphism

theorem cofiber_soundness_from_Loc_replay
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : TraceObject ctx}
    (morphism : TraceMorphism ctx X Y)
    (witness : CertifiedCofiberWitness morphism) :
    witness.cofiberClosureWitness.connectingPacketComparisonTarget :=
  witness.cofiberClosureWitness.connectingPacketComparisonShadow

structure CertifiedCofiberSequenceWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : TraceObject ctx}
    (morphism : TraceMorphism ctx X Y)
    (witness : CertifiedCofiberWitness morphism) where
  cofiberSequenceTarget : Prop
  triangleCompatibility : witness.cofiberClosureWitness.triangleCompatibilityTarget

theorem cofiber_sequence
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : TraceObject ctx}
    (morphism : TraceMorphism ctx X Y)
    (witness : CertifiedCofiberWitness morphism)
    (sequenceWitness : CertifiedCofiberSequenceWitness morphism witness) :
    witness.cofiberClosureWitness.triangleCompatibilityTarget :=
  sequenceWitness.triangleCompatibility

structure CertifiedConeShiftCompatibilityWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : TraceObject ctx}
    (morphism : TraceMorphism ctx X Y)
    (coneWitness : CertifiedConeWitness morphism)
    (shiftWitness : CertifiedShiftMorphismWitness (cone morphism coneWitness)) where
  coneShiftCompatibilityTarget : Prop
  compatibilityProof : coneShiftCompatibilityTarget

theorem cone_shift_compat
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : TraceObject ctx}
    (morphism : TraceMorphism ctx X Y)
    (coneWitness : CertifiedConeWitness morphism)
    (shiftWitness : CertifiedShiftMorphismWitness (cone morphism coneWitness))
    (witness : CertifiedConeShiftCompatibilityWitness morphism coneWitness shiftWitness) :
    witness.coneShiftCompatibilityTarget :=
  witness.compatibilityProof

structure CertifiedIdempotentWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    {X : TraceObject ctx}
    (e : TraceMorphism ctx X X)
    (compWitness : CertifiedCompositionWitness e e) where
  idempotentReplay : Equiv (comp e e compWitness) e

structure CertifiedRetractWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : TraceObject ctx}
    (r : TraceMorphism ctx X Y)
    (s : TraceMorphism ctx Y X)
    (rsWitness : CertifiedCompositionWitness r s)
    (srWitness : CertifiedCompositionWitness s r)
    (idYWitness : CertifiedIdentityTraceWitness Y) where
  retractClosureWitness : CertifiedRetractClosureWitness ctx
  sectionRetractWitness : Equiv (comp s r srWitness) (id Y idYWitness)
  idempotentCompWitness :
    CertifiedCompositionWitness (comp s r srWitness) (comp s r srWitness)
  idempotentWitness :
    CertifiedIdempotentWitness (comp s r srWitness) idempotentCompWitness

end TraceMorphism

structure TraceCategoryStructure
    (ctx : ClassicalComparisonContext.{u, v}) where
  package : PresentationAdmissibleClosureEquivalence ctx
  categoricalShadowTarget : Prop

namespace TraceCategoryStructure

def objectFromGeometric
    {ctx : ClassicalComparisonContext.{u, v}}
    (traceCategory : TraceCategoryStructure ctx) :
    GeometricPeriodObject ctx → TraceObject ctx :=
  TraceObject.ofPresentationPackage traceCategory.package

def fromCampaign8
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PresentationAdmissibleClosureEquivalence ctx) :
    TraceCategoryStructure ctx where
  package := package
  categoricalShadowTarget :=
    package.closureComparisonTarget ∧
      primitiveWitnessesSoundnessTarget package.primitiveWitnesses

theorem categoricalShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PresentationAdmissibleClosureEquivalence ctx) :
    (fromCampaign8 package).categoricalShadowTarget :=
  ⟨package.closureComparison, primitiveWitnessesSoundnessShadow package.primitiveWitnesses⟩

end TraceCategoryStructure

def traceCategoryStructure_from_campaign8
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PresentationAdmissibleClosureEquivalence ctx) :
    TraceCategoryStructure ctx :=
  TraceCategoryStructure.fromCampaign8 package

theorem traceCategoryStructure_from_campaign8_shadow
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : PresentationAdmissibleClosureEquivalence ctx) :
    (traceCategoryStructure_from_campaign8 package).categoricalShadowTarget :=
  TraceCategoryStructure.categoricalShadow package

end ClassicalPeriods
end TraceCalc
