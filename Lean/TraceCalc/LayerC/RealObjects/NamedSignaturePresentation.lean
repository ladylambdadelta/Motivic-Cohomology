import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Equiv.List
import TraceCalc.LayerB.Foundations.Occurrence

/-!
# Real-objects formalization: preferred named/free signature presentation

This file supplies a concrete named/free syntax layer for the intended
trace-calculus syntax. The guiding constraints are:

* do not prove arbitrary signatures legible;
* keep codes purely syntactic;
* avoid semantic orderings;
* stop before boundary-exposure data.

Accordingly, primitive carriers and operation symbols are presented by named
types, while sort, variable, hole, and expression codes are explicit
syntax-driven `Nat` encodings.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects

private theorem nat_pair_components_eq
    {a b c d : Nat} (h : Nat.pair a b = Nat.pair c d) :
    a = c ∧ b = d := by
  have h' : (a, b) = (c, d) := by
    simpa [Nat.unpair_pair] using congrArg Nat.unpair h
  exact ⟨by simpa using congrArg Prod.fst h', by simpa using congrArg Prod.snd h'⟩

/-- Preferred named/free primitive-interface presentation: primitive carriers
are identified by syntactic names, with constructor arities recorded as syntax
data. -/
structure NamedPrimitiveInterfacePresentation where
  PortName : Type u
  portName_encodable : Encodable PortName
  portName_linearOrder : LinearOrder PortName
  PacketName : Type u
  packetName_encodable : Encodable PacketName
  packetName_linearOrder : LinearOrder PacketName
  ConstructorName : Type u
  constructorName_encodable : Encodable ConstructorName
  constructorName_linearOrder : LinearOrder ConstructorName
  constructorArity : ConstructorName → Nat

attribute [instance]
  NamedPrimitiveInterfacePresentation.portName_encodable
  NamedPrimitiveInterfacePresentation.portName_linearOrder
  NamedPrimitiveInterfacePresentation.packetName_encodable
  NamedPrimitiveInterfacePresentation.packetName_linearOrder
  NamedPrimitiveInterfacePresentation.constructorName_encodable
  NamedPrimitiveInterfacePresentation.constructorName_linearOrder

namespace NamedPrimitiveInterfacePresentation

/-- The foundational primitive-interface data determined by a named primitive
presentation. -/
def toPrimitiveInterfaceData
  (presentation : NamedPrimitiveInterfacePresentation) :
    Foundations.PrimitiveInterfaceData.{u} where
  P0 := presentation.PortName
  PiPkt := presentation.PacketName
  CInt := presentation.ConstructorName
  arityIn := presentation.constructorArity

/-- Preferred concrete primitive carrier layer: all primitive names are natural
number identifiers. -/
def preferred (constructorArity : Nat → Nat) : NamedPrimitiveInterfacePresentation where
  PortName := Nat
  portName_encodable := inferInstance
  portName_linearOrder := inferInstance
  PacketName := Nat
  packetName_encodable := inferInstance
  packetName_linearOrder := inferInstance
  ConstructorName := Nat
  constructorName_encodable := inferInstance
  constructorName_linearOrder := inferInstance
  constructorArity := constructorArity

/-- Primitive carrier codes are the names themselves. -/
def portCode
    (presentation : NamedPrimitiveInterfacePresentation) :
    presentation.toPrimitiveInterfaceData.P0 → presentation.PortName :=
  id

/-- Primitive packet-generator codes are the names themselves. -/
def packetCode
    (presentation : NamedPrimitiveInterfacePresentation) :
    presentation.toPrimitiveInterfaceData.PiPkt → presentation.PacketName :=
  id

/-- Primitive constructor codes are the names themselves. -/
def constructorCode
    (presentation : NamedPrimitiveInterfacePresentation) :
    presentation.toPrimitiveInterfaceData.CInt → presentation.ConstructorName :=
  id

end NamedPrimitiveInterfacePresentation

/-- Preferred named/free signature presentation over a named primitive layer.
Variables, holes, and operation symbols are syntactic names, not semantic
values. -/
structure NamedSignaturePresentation
  (primitive : NamedPrimitiveInterfacePresentation) where
  VariableName : Type u
  variableName_encodable : Encodable VariableName
  variableName_linearOrder : LinearOrder VariableName
  HoleName : Type u
  holeName_encodable : Encodable HoleName
  holeName_linearOrder : LinearOrder HoleName
  OperationName : Type u
  operationName_encodable : Encodable OperationName
  operationName_linearOrder : LinearOrder OperationName
  operationArity : OperationName → Nat
  operationIn : (ω : OperationName) →
    Fin (operationArity ω) → Foundations.Sort_ primitive.toPrimitiveInterfaceData
  operationOut : OperationName → Foundations.Sort_ primitive.toPrimitiveInterfaceData

attribute [instance]
  NamedSignaturePresentation.variableName_encodable
  NamedSignaturePresentation.variableName_linearOrder
  NamedSignaturePresentation.holeName_encodable
  NamedSignaturePresentation.holeName_linearOrder
  NamedSignaturePresentation.operationName_encodable
  NamedSignaturePresentation.operationName_linearOrder

namespace NamedSignaturePresentation

/-- The foundational named/free signature determined by a named presentation. -/
def toSignature
  {primitive : NamedPrimitiveInterfacePresentation}
  (presentation : NamedSignaturePresentation primitive) :
    Foundations.Signature primitive.toPrimitiveInterfaceData where
  Var := fun _ => presentation.VariableName
  Hole := fun _ => presentation.HoleName
  Op := presentation.OperationName
  opArity := presentation.operationArity
  opIn := presentation.operationIn
  opOut := presentation.operationOut

/-- Preferred concrete signature layer: variables, holes, and operations are
all natural-number identifiers. -/
def preferred
  (primitive : NamedPrimitiveInterfacePresentation)
    (operationArity : Nat → Nat)
    (operationIn : (ω : Nat) →
      Fin (operationArity ω) → Foundations.Sort_ primitive.toPrimitiveInterfaceData)
    (operationOut : Nat → Foundations.Sort_ primitive.toPrimitiveInterfaceData) :
    NamedSignaturePresentation primitive where
  VariableName := Nat
  variableName_encodable := inferInstance
  variableName_linearOrder := inferInstance
  HoleName := Nat
  holeName_encodable := inferInstance
  holeName_linearOrder := inferInstance
  OperationName := Nat
  operationName_encodable := inferInstance
  operationName_linearOrder := inferInstance
  operationArity := operationArity
  operationIn := operationIn
  operationOut := operationOut

/-- Purely syntactic code for sorts. -/
def sortSyntaxCode
  {primitive : NamedPrimitiveInterfacePresentation}
  (presentation : NamedSignaturePresentation primitive) :
    Foundations.Sort_ primitive.toPrimitiveInterfaceData → Nat
  | .port p => Nat.pair 0 (Encodable.encode (α := primitive.PortName) p)
  | .gen π => Nat.pair 1 (Encodable.encode (α := primitive.PacketName) π)
  | .con c args =>
      Nat.pair 2
        (Nat.pair (Encodable.encode (α := primitive.ConstructorName) c)
          (Encodable.encode (List.ofFn fun i => presentation.sortSyntaxCode (args i))))

/-- Sort syntax codes are injective because they mirror the sort grammar. -/
theorem sortSyntaxCode_injective
  {primitive : NamedPrimitiveInterfacePresentation}
  (presentation : NamedSignaturePresentation primitive) :
    Function.Injective presentation.sortSyntaxCode := by
  intro s₁
  induction s₁ with
  | port p =>
      intro s₂ h
      cases s₂ with
      | port p' =>
          have hpair := nat_pair_components_eq h
          exact congrArg Foundations.Sort_.port
            (Encodable.encode_injective (α := primitive.PortName) (by simpa using hpair.2))
      | gen π' =>
          have hpair := nat_pair_components_eq h
          cases hpair.1
      | con _ _ =>
          have hpair := nat_pair_components_eq h
          cases hpair.1
  | gen π =>
      intro s₂ h
      cases s₂ with
      | port _ =>
          have hpair := nat_pair_components_eq h
          cases hpair.1.symm
      | gen π' =>
          have hpair := nat_pair_components_eq h
          exact congrArg Foundations.Sort_.gen
            (Encodable.encode_injective (α := primitive.PacketName) (by simpa using hpair.2))
      | con _ _ =>
          have hpair := nat_pair_components_eq h
          cases hpair.1
  | con c args ih =>
      intro s₂ h
      cases s₂ with
      | port _ =>
          have hpair := nat_pair_components_eq h
          cases hpair.1.symm
      | gen _ =>
          have hpair := nat_pair_components_eq h
          cases hpair.1.symm
      | con c' args' =>
          have houter := nat_pair_components_eq h
          have hinner := nat_pair_components_eq houter.2
          have hc : c = c' := by
            exact Encodable.encode_injective (α := primitive.ConstructorName) (by
              simpa using hinner.1 :
                Encodable.encode (α := primitive.ConstructorName) c =
                  Encodable.encode (α := primitive.ConstructorName) c')
          subst hc
          have hList :
              List.ofFn (fun i => presentation.sortSyntaxCode (args i)) =
                List.ofFn (fun i => presentation.sortSyntaxCode (args' i)) := by
            exact Encodable.encode_injective (α := List Nat) (by simpa using hinner.2)
          have hCodes :
              (fun i => presentation.sortSyntaxCode (args i)) =
                fun i => presentation.sortSyntaxCode (args' i) :=
            List.ofFn_injective hList
          have hArgs : args = args' := by
            funext i
            exact ih i (by simpa using congrArg (fun f => f i) hCodes)
          subst hArgs
          rfl

/-- Dependent variable codes are given by the ambient sort code and the chosen
variable name. -/
def varSyntaxCode
  {primitive : NamedPrimitiveInterfacePresentation}
  (presentation : NamedSignaturePresentation primitive)
    {s : Foundations.Sort_ primitive.toPrimitiveInterfaceData}
    (v : presentation.toSignature.Var s) : Nat :=
  Nat.pair (presentation.sortSyntaxCode s)
    (Encodable.encode (α := presentation.VariableName) v)

/-- Dependent hole codes are given by the ambient sort code and the chosen
hole name. -/
def holeSyntaxCode
  {primitive : NamedPrimitiveInterfacePresentation}
  (presentation : NamedSignaturePresentation primitive)
    {s : Foundations.Sort_ primitive.toPrimitiveInterfaceData}
    (h : presentation.toSignature.Hole s) : Nat :=
  Nat.pair (presentation.sortSyntaxCode s)
    (Encodable.encode (α := presentation.HoleName) h)

/-- Purely syntactic code for active expressions. -/
def exprSyntaxCode
  {primitive : NamedPrimitiveInterfacePresentation}
  (presentation : NamedSignaturePresentation primitive)
    {s : Foundations.Sort_ primitive.toPrimitiveInterfaceData} :
    Foundations.Expr presentation.toSignature s → Nat
  | .var v => Nat.pair 0 (presentation.varSyntaxCode v)
  | .op ω es =>
      Nat.pair 1
        (Nat.pair (Encodable.encode (α := presentation.OperationName) ω)
          (Encodable.encode (List.ofFn fun i => presentation.exprSyntaxCode (es i))))

/-- Variables of a fixed sort are determined by their syntax codes. -/
theorem varSyntaxCode_injective
  {primitive : NamedPrimitiveInterfacePresentation}
  (presentation : NamedSignaturePresentation primitive)
    (s : Foundations.Sort_ primitive.toPrimitiveInterfaceData) :
    Function.Injective (fun v : presentation.toSignature.Var s => presentation.varSyntaxCode v) := by
  intro v₁ v₂ h
  have hpair := nat_pair_components_eq h
  exact Encodable.encode_injective (α := presentation.VariableName) (by
    simpa using hpair.2 :
      Encodable.encode (α := presentation.VariableName) v₁ =
        Encodable.encode (α := presentation.VariableName) v₂)

/-- Holes of a fixed sort are determined by their syntax codes. -/
theorem holeSyntaxCode_injective
  {primitive : NamedPrimitiveInterfacePresentation}
  (presentation : NamedSignaturePresentation primitive)
    (s : Foundations.Sort_ primitive.toPrimitiveInterfaceData) :
    Function.Injective (fun h : presentation.toSignature.Hole s => presentation.holeSyntaxCode h) := by
  intro h₁ h₂ h
  have hpair := nat_pair_components_eq h
  exact Encodable.encode_injective (α := presentation.HoleName) (by
    simpa using hpair.2 :
      Encodable.encode (α := presentation.HoleName) h₁ =
        Encodable.encode (α := presentation.HoleName) h₂)

/-- Active expressions with equal syntax codes agree up to their sort index. -/
theorem exprSyntaxCode_heq
  {primitive : NamedPrimitiveInterfacePresentation}
  (presentation : NamedSignaturePresentation primitive) :
    ∀ {s t : Foundations.Sort_ primitive.toPrimitiveInterfaceData}
      (e₁ : Foundations.Expr presentation.toSignature s)
      (e₂ : Foundations.Expr presentation.toSignature t),
      presentation.exprSyntaxCode e₁ = presentation.exprSyntaxCode e₂ → HEq e₁ e₂ := by
  intro s t e₁
  revert t
  induction e₁ with
  | var v =>
      intro t e₂ h
      cases e₂ with
      | var v' =>
          have hpair := nat_pair_components_eq h
          have hvar := nat_pair_components_eq hpair.2
          have hs := presentation.sortSyntaxCode_injective (by simpa using hvar.1)
          cases hs
          have hv : v = v' := presentation.varSyntaxCode_injective _ (by simpa using hpair.2)
          cases hv
          exact HEq.rfl
      | op _ _ =>
          have hpair := nat_pair_components_eq h
          cases hpair.1
  | op ω es ih =>
      intro t e₂ h
      cases e₂ with
      | var _ =>
          have hpair := nat_pair_components_eq h
          cases hpair.1.symm
      | op ω' es' =>
          have houter := nat_pair_components_eq h
          have hinner := nat_pair_components_eq houter.2
          have hω : ω = ω' := by
            exact Encodable.encode_injective (α := presentation.OperationName) (by
              simpa using hinner.1 :
                Encodable.encode (α := presentation.OperationName) ω =
                  Encodable.encode (α := presentation.OperationName) ω')
          cases hω
          have hList :
              List.ofFn (fun i => presentation.exprSyntaxCode (es i)) =
                List.ofFn (fun i => presentation.exprSyntaxCode (es' i)) := by
            exact Encodable.encode_injective (α := List Nat) (by simpa using hinner.2)
          have hCodes :
              (fun i => presentation.exprSyntaxCode (es i)) =
                fun i => presentation.exprSyntaxCode (es' i) :=
            List.ofFn_injective hList
          have hArgs : es = es' := by
            funext i
            exact eq_of_heq (ih i (es' i) (by simpa using congrArg (fun f => f i) hCodes))
          cases hArgs
          rfl

/-- Active expressions of a fixed sort are determined by their syntax codes. -/
theorem exprCode_injective_fixed_sort
  {primitive : NamedPrimitiveInterfacePresentation}
  (presentation : NamedSignaturePresentation primitive)
    (s : Foundations.Sort_ primitive.toPrimitiveInterfaceData) :
    Function.Injective
      (fun e : Foundations.Expr presentation.toSignature s => presentation.exprSyntaxCode e) := by
  intro e₁ e₂ h
  exact eq_of_heq (presentation.exprSyntaxCode_heq e₁ e₂ h)

/-- Boundary-free code package determined by a named/free signature
presentation. This is the real syntax-side instance that exists before any
boundary-facing canonical-display data is supplied. -/
structure CoreCodeData
  {primitive : NamedPrimitiveInterfacePresentation.{u}}
  (presentation : NamedSignaturePresentation.{u} primitive) where
  PortCode : Type (u+1)
  portCode : primitive.toPrimitiveInterfaceData.P0 → PortCode
  portCode_injective : Function.Injective portCode
  portCode_linearOrder : LinearOrder PortCode
  PacketCode : Type (u+1)
  packetCode : primitive.toPrimitiveInterfaceData.PiPkt → PacketCode
  packetCode_injective : Function.Injective packetCode
  packetCode_linearOrder : LinearOrder PacketCode
  ConstructorCode : Type (u+1)
  constructorCode : primitive.toPrimitiveInterfaceData.CInt → ConstructorCode
  constructorCode_injective : Function.Injective constructorCode
  constructorCode_linearOrder : LinearOrder ConstructorCode
  SortCode : Type (u+1)
  sortCode : Foundations.Sort_ primitive.toPrimitiveInterfaceData → SortCode
  sortCode_injective : Function.Injective sortCode
  sortCode_linearOrder : LinearOrder SortCode
  VarCode : Type (u+1)
  varCode : {s : Foundations.Sort_ primitive.toPrimitiveInterfaceData} →
    presentation.toSignature.Var s → VarCode
  varCode_injective :
    ∀ s,
      Function.Injective (fun v : presentation.toSignature.Var s => varCode v)
  varCode_linearOrder : LinearOrder VarCode
  HoleCode : Type (u+1)
  holeCode : {s : Foundations.Sort_ primitive.toPrimitiveInterfaceData} →
    presentation.toSignature.Hole s → HoleCode
  holeCode_injective :
    ∀ s,
      Function.Injective (fun h : presentation.toSignature.Hole s => holeCode h)
  holeCode_linearOrder : LinearOrder HoleCode
  ExprCode : Type (u+1)
  exprCode : {s : Foundations.Sort_ primitive.toPrimitiveInterfaceData} →
    Foundations.Expr presentation.toSignature s → ExprCode
  exprCode_injective :
    ∀ s,
      Function.Injective (fun e : Foundations.Expr presentation.toSignature s => exprCode e)
  exprCode_linearOrder : LinearOrder ExprCode
  OpCode : Type (u+1)
  opCode : presentation.OperationName → OpCode
  opCode_injective : Function.Injective opCode
  opCode_linearOrder : LinearOrder OpCode

/-- The preferred named/free signature presentation supplies a genuine
boundary-free code package whose codes are syntactic names and syntax trees. -/
def toCoreCodeData
  {primitive : NamedPrimitiveInterfacePresentation.{u}}
  (presentation : NamedSignaturePresentation.{u} primitive) :
  CoreCodeData.{u} presentation where
  PortCode := ULift.{u+1, u} primitive.PortName
  portCode := fun p => ULift.up (primitive.portCode p)
  portCode_injective := by
    intro p₁ p₂ h
    exact congrArg ULift.down h
  portCode_linearOrder := inferInstance
  PacketCode := ULift.{u+1, u} primitive.PacketName
  packetCode := fun π => ULift.up (primitive.packetCode π)
  packetCode_injective := by
    intro π₁ π₂ h
    exact congrArg ULift.down h
  packetCode_linearOrder := inferInstance
  ConstructorCode := ULift.{u+1, u} primitive.ConstructorName
  constructorCode := fun c => ULift.up (primitive.constructorCode c)
  constructorCode_injective := by
    intro c₁ c₂ h
    exact congrArg ULift.down h
  constructorCode_linearOrder := inferInstance
  SortCode := ULift.{u+1} Nat
  sortCode := fun s => ULift.up (presentation.sortSyntaxCode s)
  sortCode_injective := by
    intro s₁ s₂ h
    exact presentation.sortSyntaxCode_injective (congrArg ULift.down h)
  sortCode_linearOrder := inferInstance
  VarCode := ULift.{u+1} Nat
  varCode := fun {s} v => ULift.up (presentation.varSyntaxCode v)
  varCode_injective := by
    intro s v₁ v₂ h
    exact presentation.varSyntaxCode_injective s (congrArg ULift.down h)
  varCode_linearOrder := inferInstance
  HoleCode := ULift.{u+1} Nat
  holeCode := fun {s} h => ULift.up (presentation.holeSyntaxCode h)
  holeCode_injective := by
    intro s h₁ h₂ h
    exact presentation.holeSyntaxCode_injective s (congrArg ULift.down h)
  holeCode_linearOrder := inferInstance
  ExprCode := ULift.{u+1} Nat
  exprCode := fun {s} e => ULift.up (presentation.exprSyntaxCode e)
  exprCode_injective := by
    intro s e₁ e₂ h
    exact presentation.exprCode_injective_fixed_sort s (congrArg ULift.down h)
  exprCode_linearOrder := inferInstance
  OpCode := ULift.{u+1, u} presentation.OperationName
  opCode := fun ω => ULift.up ω
  opCode_injective := by
    intro ω₁ ω₂ h
    exact congrArg ULift.down h
  opCode_linearOrder := inferInstance

end NamedSignaturePresentation

/-- Named/free doctrine presentation: adds named rule identifiers and an
admissibility predicate to a named signature presentation. -/
structure NamedDoctrinePresentation
  (primitive : NamedPrimitiveInterfacePresentation) where
  signaturePresentation : NamedSignaturePresentation primitive
  RuleName : Type u
  ruleName_encodable : Encodable RuleName
  ruleName_linearOrder : LinearOrder RuleName
  ruleName_fintype : Fintype RuleName
  rule : RuleName → Foundations.RewriteScheme signaturePresentation.toSignature
  admissible :
    RuleName → Foundations.LocalCirquentState signaturePresentation.toSignature → Prop
  admissible_decidable :
    ∀ (i : RuleName) (σ : Foundations.LocalCirquentState signaturePresentation.toSignature),
      Decidable (admissible i σ)

attribute [instance]
  NamedDoctrinePresentation.ruleName_encodable
  NamedDoctrinePresentation.ruleName_linearOrder
  NamedDoctrinePresentation.ruleName_fintype
  NamedDoctrinePresentation.admissible_decidable

namespace NamedDoctrinePresentation

/-- The doctrine determined by a named/free doctrine presentation. -/
def toDoctrine
  {primitive : NamedPrimitiveInterfacePresentation}
  (presentation : NamedDoctrinePresentation primitive) :
    Foundations.Doctrine primitive.toPrimitiveInterfaceData where
  sig := presentation.signaturePresentation.toSignature
  R_index := presentation.RuleName
  R_fintype := by
    classical
    infer_instance
  R := presentation.rule
  admissible := presentation.admissible
  admissible_decidable := presentation.admissible_decidable

end NamedDoctrinePresentation

end RealObjects
end LayerB
end TraceCalc