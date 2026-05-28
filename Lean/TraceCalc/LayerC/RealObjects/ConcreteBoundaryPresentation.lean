import Mathlib.Data.List.OfFn
import Mathlib.Data.Multiset.Sort
import TraceCalc.LayerC.RealObjects.Bridge
import TraceCalc.LayerB.RealObjects.CompletedRecord
import TraceCalc.LayerC.RealObjects.NamedSignaturePresentation
import TraceCalc.LayerB.RealObjects.SwapSquare
import TraceCalc.LayerC.RealObjects.SyntacticBoundary
import TraceCalc.LayerC.RealObjects.SyntacticHolography

/-!
# Real-objects formalization: concrete boundary-presentation scaffold

This file starts the internal **Boundary presentation theorem** on the Lean
side. The current `RewriteCalculusSetup` still leaves
`setup.BoundaryObject` abstract, so the genuine hard work remains the
`boundary_complete` theorem target. The purpose of this file is to pin down
the intended presentation interface as closely as possible to the concrete
surfaces already present in the bridge/foundations lane:

* ordered boundary profiles are represented in the foundations lane by
  `Foundations.Pat.boundaryProfile`;
* refined interfaces and external outputs already appear concretely as
  `setup.RefinedInterface` and `List setup.RefinedInterface`;
* boundary exposure data is already named at the setup level by
  `setup.boundaryOf` and `setup.exposeBoundaryUnderSinkDeletion`.

Because the generic setup is still abstract at the `BoundaryObject` carrier,
this file packages the intended boundary encoder into a scaffold structure.
The external-output side is no longer merely aspirational: once the refined
interface encoding is injective, the `List.Perm` completeness theorem follows
automatically.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

open CompletedReconstructionRecord

variable {setup : RewriteCalculusSetup.{u}}

/-- Role tag for the intended concrete boundary atoms. This keeps the atom
carrier close to the existing refined-interface data while leaving room for
source/exposed/target boundary roles in the eventual unconditional instance. -/
inductive ConcreteBoundaryRole where
  /-- Atom coming from source-side boundary profile data. -/
  | source
  /-- Atom exposed by a sink-deletion boundary step. -/
  | exposed
  /-- Atom used for refined interfaces and external outputs. -/
  | target
  deriving DecidableEq

/-- Intended presentation atom for the bridge/foundations boundary syntax.
The atom is a role-tagged refined interface.  Parametrized directly by the
interface type `RI` (rather than the full `RewriteCalculusSetup`) so that a
concrete setup can set `BoundaryObject := Multiset (ConcreteBoundaryAtom RI)`
without circularity. -/
structure ConcreteBoundaryAtom (RI : Type u) where
  /-- Which boundary role this atom is representing. -/
  role : ConcreteBoundaryRole
  /-- The underlying refined interface token. -/
  interface : RI

/-- `ConcreteBoundaryAtom` has decidable equality whenever the interface type does. -/
instance instDecidableEqConcreteBoundaryAtom {RI : Type u} [DecidableEq RI] :
    DecidableEq (ConcreteBoundaryAtom RI) := by
  intro ⟨r₁, i₁⟩ ⟨r₂, i₂⟩
  by_cases h1 : r₁ = r₂
  · by_cases h2 : i₁ = i₂
    · exact isTrue (congrArg₂ ConcreteBoundaryAtom.mk h1 h2)
    · exact isFalse fun h => h2 (congrArg ConcreteBoundaryAtom.interface h)
  · exact isFalse fun h => h1 (congrArg ConcreteBoundaryAtom.role h)

/-- Candidate encoder for refined interfaces into the intended boundary atom
syntax. External outputs use the `target` role. -/
def encodeRefinedInterfaceCandidate
    (I : setup.RefinedInterface) : ConcreteBoundaryAtom setup.RefinedInterface where
  role := .target
  interface := I

/-- The candidate refined-interface encoder is injective. -/
theorem encodeRefinedInterfaceCandidate_injective :
    Function.Injective (encodeRefinedInterfaceCandidate (setup := setup)) := by
  intro I₁ I₂ h
  cases h
  rfl

/-- Soundness target for a candidate boundary encoder. -/
def BoundarySoundTarget
    {Atom : Type u}
    (encodeBoundaryCandidate :
      setup.BoundaryObject → SyntacticBoundaryObject Atom) : Prop :=
  ∀ {Y₁ Y₂ : setup.BoundaryObject},
    BoundaryAdminEquiv Y₁ Y₂ →
      SyntacticBoundaryEquiv
        (encodeBoundaryCandidate Y₁)
        (encodeBoundaryCandidate Y₂)

/-- Completeness target for a candidate boundary encoder. This is the real
remaining theorem target for the intended boundary presentation. -/
def BoundaryCompleteTarget
    {Atom : Type u}
    (encodeBoundaryCandidate :
      setup.BoundaryObject → SyntacticBoundaryObject Atom) : Prop :=
  ∀ {Y₁ Y₂ : setup.BoundaryObject},
    SyntacticBoundaryEquiv
      (encodeBoundaryCandidate Y₁)
      (encodeBoundaryCandidate Y₂) →
        BoundaryAdminEquiv Y₁ Y₂

/-- Soundness target for a candidate refined-interface encoder. -/
def ExternalOutSoundTarget
    {Atom : Type u}
    (encodeRefinedInterfaceCandidate :
      setup.RefinedInterface → Atom) : Prop :=
  ∀ {L₁ L₂ : List setup.RefinedInterface},
    List.Perm L₁ L₂ →
      List.Perm
        (L₁.map encodeRefinedInterfaceCandidate)
        (L₂.map encodeRefinedInterfaceCandidate)

/-- Completeness target for a candidate refined-interface encoder. -/
def ExternalOutCompleteTarget
    {Atom : Type u}
    (encodeRefinedInterfaceCandidate :
      setup.RefinedInterface → Atom) : Prop :=
  ∀ {L₁ L₂ : List setup.RefinedInterface},
    List.Perm
      (L₁.map encodeRefinedInterfaceCandidate)
      (L₂.map encodeRefinedInterfaceCandidate) →
        List.Perm L₁ L₂

/-- Permutation soundness for mapped external outputs is automatic. -/
theorem externalOut_sound_of_encode
    {Atom : Type u}
    (encode : setup.RefinedInterface → Atom)
    {L₁ L₂ : List setup.RefinedInterface}
    (h : List.Perm L₁ L₂) :
    List.Perm (L₁.map encode) (L₂.map encode) := by
  simpa using h.map encode

/-- If the refined-interface encoding is injective, equality modulo
permutation of the encoded external-output lists reflects back to the source
lists. This discharges the external-output completeness half of the scaffold. -/
theorem externalOut_complete_of_injective
    {Atom : Type u}
    (encode : setup.RefinedInterface → Atom)
    (hinj : Function.Injective encode)
    {L₁ L₂ : List setup.RefinedInterface}
    (h : List.Perm (L₁.map encode) (L₂.map encode)) :
    List.Perm L₁ L₂ := by
  apply Multiset.coe_eq_coe.mp
  rw [← Multiset.map_eq_map hinj]
  exact Quot.sound h

/-- Boundary-presentation scaffold for the intended bridge/foundations syntax.
`boundary_complete` remains a field because it is the actual hard theorem
target; the external-output half is filled automatically from injectivity of
the refined-interface encoder. -/
structure ConcreteBoundaryPresentationScaffold
    (setup : RewriteCalculusSetup.{u}) where
  /-- Candidate encoding of generic boundary objects into the intended
  syntactic boundary carrier. -/
  encodeBoundaryCandidate :
    setup.BoundaryObject → SyntacticBoundaryObject (ConcreteBoundaryAtom setup.RefinedInterface)
  /-- Candidate encoding of refined interfaces into the intended boundary
  atoms. -/
  encodeRefinedInterfaceCandidate :
    setup.RefinedInterface → ConcreteBoundaryAtom setup.RefinedInterface :=
      RewriteCalculusSetup.encodeRefinedInterfaceCandidate (setup := setup)
  /-- Injectivity sufficient to make external-output completeness automatic. -/
  encodeRefinedInterface_injective :
    Function.Injective encodeRefinedInterfaceCandidate := by
      intro I₁ I₂ h
      cases h
      rfl
  /-- Boundary soundness for the candidate boundary encoder. -/
  boundary_sound : BoundarySoundTarget (setup := setup) encodeBoundaryCandidate
  /-- Boundary completeness for the candidate boundary encoder. This is the
  remaining substantive theorem target. -/
  boundary_complete : BoundaryCompleteTarget (setup := setup) encodeBoundaryCandidate
  /-- External-output soundness is automatic by `List.Perm.map`. -/
  externalOut_sound :
    ExternalOutSoundTarget (setup := setup) encodeRefinedInterfaceCandidate := by
      intro L₁ L₂ h
      exact externalOut_sound_of_encode encodeRefinedInterfaceCandidate h
  /-- External-output completeness is automatic from injectivity. -/
  externalOut_complete :
    ExternalOutCompleteTarget (setup := setup) encodeRefinedInterfaceCandidate := by
      intro L₁ L₂ h
      exact externalOut_complete_of_injective
        encodeRefinedInterfaceCandidate
        encodeRefinedInterface_injective
        h

namespace ConcreteBoundaryPresentationScaffold

/-- Package the scaffold into the existing Path B presentation interface. -/
def toSyntacticBoundaryPresentation
    (S : ConcreteBoundaryPresentationScaffold setup) :
    SyntacticBoundaryPresentation setup where
  Atom := ConcreteBoundaryAtom setup.RefinedInterface
  encodeBoundary := S.encodeBoundaryCandidate
  encodeRefinedInterface := S.encodeRefinedInterfaceCandidate
  boundary_sound := S.boundary_sound
  boundary_complete := S.boundary_complete
  externalOut_sound := S.externalOut_sound
  externalOut_complete := S.externalOut_complete

end ConcreteBoundaryPresentationScaffold

/-- Manuscript-facing alias: the concrete boundary-presentation scaffold type. -/
def theorem_concrete_boundary_presentation_scaffold
  (setup : RewriteCalculusSetup.{u}) :=
  ConcreteBoundaryPresentationScaffold setup

/-- Manuscript-facing alias: the remaining hard theorem target is the
boundary-completeness obligation for a chosen candidate boundary encoder. -/
def theorem_boundary_complete_remaining_target
    {Atom : Type u}
    (encodeBoundaryCandidate :
      setup.BoundaryObject → SyntacticBoundaryObject Atom) : Prop :=
  BoundaryCompleteTarget (setup := setup) encodeBoundaryCandidate

/-- Manuscript-facing alias: injectivity of the refined-interface encoding is
already sufficient for the external-output completeness half. -/
theorem theorem_refined_interface_encoding_injective_suffices_for_externalOut_complete
    {Atom : Type u}
    (encode : setup.RefinedInterface → Atom)
    (hinj : Function.Injective encode)
    {L₁ L₂ : List setup.RefinedInterface} :
    List.Perm (L₁.map encode) (L₂.map encode) →
      List.Perm L₁ L₂ :=
  externalOut_complete_of_injective encode hinj

/-! ## Bridge-specific concrete boundary syntax surface -/

/-- In the foundations lane, the actual source type carrying ordered boundary
profiles is `BoundaryCirquent`. This is the nearest real syntax object to use
for the concrete boundary encoder. -/
abbrev OrderedBoundaryProfileSource
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) : Type u :=
  Foundations.BoundaryCirquent Dc.sig

/-- Typed input-boundary entry carried by a foundations boundary cirquent. -/
abbrev BoundaryInputEntry
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) :=
  Σ s : Foundations.Sort_ D, Dc.sig.Var s

/-- Typed output-boundary entry carried by a foundations boundary cirquent. -/
abbrev BoundaryOutputEntry
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) :=
  Σ s : Foundations.Sort_ D, Foundations.Expr Dc.sig s

/-- Ordered list of typed input-boundary entries carried by a foundations
boundary cirquent. -/
def orderedInputBoundaryEntries
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (Y : OrderedBoundaryProfileSource Dc) :
    List (BoundaryInputEntry Dc) :=
  List.ofFn fun i => ⟨Y.inputProfile.get i, Y.inputVars i⟩

/-- Ordered list of typed output-boundary entries carried by a foundations
boundary cirquent. -/
def orderedOutputBoundaryEntries
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (Y : OrderedBoundaryProfileSource Dc) :
    List (BoundaryOutputEntry Dc) :=
  List.ofFn fun i => ⟨Y.outputProfile.get i, Y.outputs i⟩

@[simp] theorem orderedInputBoundaryEntries_map_fst
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (Y : OrderedBoundaryProfileSource Dc) :
    (orderedInputBoundaryEntries Y).map Sigma.fst = Y.inputProfile := by
  rw [orderedInputBoundaryEntries, List.map_ofFn]
  convert (List.ofFn_get (l := Y.inputProfile)) using 1

@[simp] theorem orderedOutputBoundaryEntries_map_fst
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (Y : OrderedBoundaryProfileSource Dc) :
    (orderedOutputBoundaryEntries Y).map Sigma.fst = Y.outputProfile := by
  rw [orderedOutputBoundaryEntries, List.map_ofFn]
  convert (List.ofFn_get (l := Y.outputProfile)) using 1

/-- Rebuild a foundations boundary cirquent from ordered lists of typed input
and output boundary entries. -/
def boundaryCirquentOfOrderedBoundaryEntries
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (inputs : List (BoundaryInputEntry Dc))
    (outputs : List (BoundaryOutputEntry Dc)) :
    OrderedBoundaryProfileSource Dc where
  inputProfile := List.ofFn (Sigma.fst ∘ inputs.get)
  outputProfile := List.ofFn (Sigma.fst ∘ outputs.get)
  inputVars := fun i => by
    simpa [Function.comp] using
      (inputs.get (Fin.cast (by simp) i)).2
  outputs := fun i => by
    simpa [Function.comp] using
      (outputs.get (Fin.cast (by simp) i)).2

/-- Coarse shadow boundary atoms for the bridge/foundations syntax. The
boundary side remembers only ordered sort profiles. Keep this only as a
profile-level code shadow; do not use it for completeness. -/
inductive FoundationsBoundaryProfileAtom
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) (aux : BridgeAuxiliaryData Dc) where
  /-- Input-boundary port in the ordered boundary syntax. -/
  | inputPort : Foundations.Sort_ D → FoundationsBoundaryProfileAtom Dc aux
  /-- Output-boundary port in the ordered boundary syntax. -/
  | outputPort : Foundations.Sort_ D → FoundationsBoundaryProfileAtom Dc aux
  /-- External-output/refined-interface atom from the bridge carrier. -/
  | refinedInterface : aux.RefinedInterface → FoundationsBoundaryProfileAtom Dc aux

/-- Coarse shadow boundary block determined only by the ordered boundary sort
profiles. Keep this only as a profile-level code shadow; do not use it for
completeness. -/
def encodeBoundaryProfileCirquentBlock
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) (aux : BridgeAuxiliaryData Dc)
    (C : OrderedBoundaryProfileSource Dc) :
    BoundaryBlock (FoundationsBoundaryProfileAtom Dc aux) :=
  (C.inputProfile.map
      (FoundationsBoundaryProfileAtom.inputPort (Dc := Dc) (aux := aux))) ++
    (C.outputProfile.map
      (FoundationsBoundaryProfileAtom.outputPort (Dc := Dc) (aux := aux)))

/-- Coarse shadow syntactic boundary encoder for the foundations boundary
syntax, retaining only ordered boundary sort profiles. -/
def encodeBoundaryProfileCirquentCandidate
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) (aux : BridgeAuxiliaryData Dc)
    (C : OrderedBoundaryProfileSource Dc) :
    SyntacticBoundaryObject (FoundationsBoundaryProfileAtom Dc aux) :=
  [encodeBoundaryProfileCirquentBlock Dc aux C]

/-- Boundary atoms for the bridge/foundations syntax. The strengthened
preferred boundary code records the full typed boundary entries, while the
external-output side still uses the concrete refined-interface carrier from the
bridge auxiliary data. -/
inductive FoundationsBoundaryAtom
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) (aux : BridgeAuxiliaryData Dc) where
  /-- Full typed input-boundary entry in the ordered boundary syntax. -/
  | inputEntry : BoundaryInputEntry Dc → FoundationsBoundaryAtom Dc aux
  /-- Full typed output-boundary entry in the ordered boundary syntax. -/
  | outputEntry : BoundaryOutputEntry Dc → FoundationsBoundaryAtom Dc aux
  /-- External-output/refined-interface atom from the bridge carrier. -/
  | refinedInterface : aux.RefinedInterface → FoundationsBoundaryAtom Dc aux

/-- Extract the ordered input-boundary entries encoded in a concrete boundary
block. -/
def boundaryBlockInputEntries
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : BridgeAuxiliaryData Dc} :
    BoundaryBlock (FoundationsBoundaryAtom Dc aux) → List (BoundaryInputEntry Dc)
  | [] => []
  | FoundationsBoundaryAtom.inputEntry entry :: rest =>
      entry :: boundaryBlockInputEntries rest
  | _ :: rest => boundaryBlockInputEntries rest

/-- Extract the ordered output-boundary entries encoded in a concrete boundary
block. -/
def boundaryBlockOutputEntries
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : BridgeAuxiliaryData Dc} :
    BoundaryBlock (FoundationsBoundaryAtom Dc aux) → List (BoundaryOutputEntry Dc)
  | [] => []
  | FoundationsBoundaryAtom.outputEntry entry :: rest =>
      entry :: boundaryBlockOutputEntries rest
  | _ :: rest => boundaryBlockOutputEntries rest

@[simp] theorem boundaryBlockInputEntries_append
  {D : Foundations.PrimitiveInterfaceData.{u}}
  {Dc : Foundations.Doctrine D}
  {aux : BridgeAuxiliaryData Dc}
  (left right : BoundaryBlock (FoundationsBoundaryAtom Dc aux)) :
  boundaryBlockInputEntries (left ++ right) =
    boundaryBlockInputEntries left ++ boundaryBlockInputEntries right := by
  induction left with
  | nil => rfl
  | cons atom rest ih =>
    cases atom <;> simp [boundaryBlockInputEntries, ih]

@[simp] theorem boundaryBlockOutputEntries_append
  {D : Foundations.PrimitiveInterfaceData.{u}}
  {Dc : Foundations.Doctrine D}
  {aux : BridgeAuxiliaryData Dc}
  (left right : BoundaryBlock (FoundationsBoundaryAtom Dc aux)) :
  boundaryBlockOutputEntries (left ++ right) =
    boundaryBlockOutputEntries left ++ boundaryBlockOutputEntries right := by
  induction left with
  | nil => rfl
  | cons atom rest ih =>
    cases atom <;> simp [boundaryBlockOutputEntries, ih]

@[simp] theorem boundaryBlockInputEntries_map_inputEntry
  {D : Foundations.PrimitiveInterfaceData.{u}}
  {Dc : Foundations.Doctrine D}
  {aux : BridgeAuxiliaryData Dc}
  (entries : List (BoundaryInputEntry Dc)) :
  boundaryBlockInputEntries
    (entries.map (FoundationsBoundaryAtom.inputEntry (Dc := Dc) (aux := aux))) =
    entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp [boundaryBlockInputEntries, ih]

@[simp] theorem boundaryBlockInputEntries_map_outputEntry
  {D : Foundations.PrimitiveInterfaceData.{u}}
  {Dc : Foundations.Doctrine D}
  {aux : BridgeAuxiliaryData Dc}
  (entries : List (BoundaryOutputEntry Dc)) :
  boundaryBlockInputEntries
    (entries.map (FoundationsBoundaryAtom.outputEntry (Dc := Dc) (aux := aux))) =
    [] := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp [boundaryBlockInputEntries, ih]

@[simp] theorem boundaryBlockOutputEntries_map_inputEntry
  {D : Foundations.PrimitiveInterfaceData.{u}}
  {Dc : Foundations.Doctrine D}
  {aux : BridgeAuxiliaryData Dc}
  (entries : List (BoundaryInputEntry Dc)) :
  boundaryBlockOutputEntries
    (entries.map (FoundationsBoundaryAtom.inputEntry (Dc := Dc) (aux := aux))) =
    [] := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp [boundaryBlockOutputEntries, ih]

@[simp] theorem boundaryBlockOutputEntries_map_outputEntry
  {D : Foundations.PrimitiveInterfaceData.{u}}
  {Dc : Foundations.Doctrine D}
  {aux : BridgeAuxiliaryData Dc}
  (entries : List (BoundaryOutputEntry Dc)) :
  boundaryBlockOutputEntries
    (entries.map (FoundationsBoundaryAtom.outputEntry (Dc := Dc) (aux := aux))) =
    entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp [boundaryBlockOutputEntries, ih]

/-- The concrete boundary block determined by a foundations boundary cirquent.
The strengthened preferred boundary code keeps the full typed boundary entries
in their actual syntactic order. -/
def encodeBoundaryCirquentBlock
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) (aux : BridgeAuxiliaryData Dc)
    (C : OrderedBoundaryProfileSource Dc) :
    BoundaryBlock (FoundationsBoundaryAtom Dc aux) :=
  (orderedInputBoundaryEntries C).map
      (FoundationsBoundaryAtom.inputEntry (Dc := Dc) (aux := aux)) ++
    (orderedOutputBoundaryEntries C).map
      (FoundationsBoundaryAtom.outputEntry (Dc := Dc) (aux := aux))

/-- Concrete syntactic boundary encoder for the foundations boundary syntax.
We use a singleton outer block so the ordered boundary profile is kept strict. -/
def encodeBoundaryCirquentCandidate
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) (aux : BridgeAuxiliaryData Dc)
    (C : OrderedBoundaryProfileSource Dc) :
    SyntacticBoundaryObject (FoundationsBoundaryAtom Dc aux) :=
  [encodeBoundaryCirquentBlock Dc aux C]

@[simp] theorem encodeBoundaryCirquentCandidate_def
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) (aux : BridgeAuxiliaryData Dc)
    (C : OrderedBoundaryProfileSource Dc) :
    encodeBoundaryCirquentCandidate Dc aux C =
      [encodeBoundaryCirquentBlock Dc aux C] :=
  rfl

@[simp] theorem encodeBoundaryCirquentBlock_length
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) (aux : BridgeAuxiliaryData Dc)
    (C : OrderedBoundaryProfileSource Dc) :
    (encodeBoundaryCirquentBlock Dc aux C).length =
      C.inputProfile.length + C.outputProfile.length := by
  simp [encodeBoundaryCirquentBlock, orderedInputBoundaryEntries,
    orderedOutputBoundaryEntries]

@[simp] theorem boundaryBlockInputEntries_encodeBoundaryCirquentBlock
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : BridgeAuxiliaryData Dc)
    (C : OrderedBoundaryProfileSource Dc) :
    boundaryBlockInputEntries (encodeBoundaryCirquentBlock Dc aux C) =
      orderedInputBoundaryEntries C := by
  simp [boundaryBlockInputEntries, encodeBoundaryCirquentBlock]

@[simp] theorem boundaryBlockOutputEntries_encodeBoundaryCirquentBlock
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : BridgeAuxiliaryData Dc)
    (C : OrderedBoundaryProfileSource Dc) :
    boundaryBlockOutputEntries (encodeBoundaryCirquentBlock Dc aux C) =
      orderedOutputBoundaryEntries C := by
  simp [boundaryBlockOutputEntries, encodeBoundaryCirquentBlock]

theorem orderedBoundaryEntries_ext
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {Y₁ Y₂ : OrderedBoundaryProfileSource Dc}
    (hinput : orderedInputBoundaryEntries Y₁ = orderedInputBoundaryEntries Y₂)
    (houtput : orderedOutputBoundaryEntries Y₁ = orderedOutputBoundaryEntries Y₂) :
    Y₁ = Y₂ := by
  cases Y₁ with
  | mk inputProfile₁ outputProfile₁ inputVars₁ outputs₁ =>
    cases Y₂ with
    | mk inputProfile₂ outputProfile₂ inputVars₂ outputs₂ =>
      have hinputProfile : inputProfile₁ = inputProfile₂ := by
        simpa using congrArg (List.map Sigma.fst) hinput
      have houtputProfile : outputProfile₁ = outputProfile₂ := by
        simpa using congrArg (List.map Sigma.fst) houtput
      subst hinputProfile
      subst houtputProfile
      have hinputFns : inputVars₁ = inputVars₂ := by
        apply funext
        intro i
        have hentries :
            (fun j => Sigma.mk (inputProfile₁.get j) (inputVars₁ j)) =
              (fun j => Sigma.mk (inputProfile₁.get j) (inputVars₂ j)) :=
          List.ofFn_inj.mp (by simpa [orderedInputBoundaryEntries] using hinput)
        have hentry := congrFun hentries i
        simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hentry
      have houtputFns : outputs₁ = outputs₂ := by
        apply funext
        intro i
        have hentries :
            (fun j => Sigma.mk (outputProfile₁.get j) (outputs₁ j)) =
              (fun j => Sigma.mk (outputProfile₁.get j) (outputs₂ j)) :=
          List.ofFn_inj.mp (by simpa [orderedOutputBoundaryEntries] using houtput)
        have hentry := congrFun hentries i
        simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hentry
      cases hinputFns
      cases houtputFns
      rfl

theorem encodeBoundaryCirquentBlock_injective
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : BridgeAuxiliaryData Dc) :
    Function.Injective (encodeBoundaryCirquentBlock Dc aux) := by
  intro Y₁ Y₂ h
  apply orderedBoundaryEntries_ext
  · have hinput := congrArg boundaryBlockInputEntries h
    simpa using hinput
  · have houtput := congrArg boundaryBlockOutputEntries h
    simpa using houtput

theorem encodeBoundaryCirquentCandidate_injective
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : BridgeAuxiliaryData Dc) :
    Function.Injective (encodeBoundaryCirquentCandidate Dc aux) := by
  intro Y₁ Y₂ h
  apply encodeBoundaryCirquentBlock_injective aux
  simpa [encodeBoundaryCirquentCandidate] using h

/-- The concrete bridge setup built from foundations data. -/
abbrev FoundationsBridgeSetup
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) (aux : BridgeAuxiliaryData Dc) :=
  TraceCalc.LayerB.RealObjects.ofFoundations Dc aux

/-- Partial instantiation of the generic boundary encoder: once a bridge from
the opaque `BoundaryObject` carrier back to the actual foundations boundary
syntax is supplied, the concrete encoder is fixed by `encodeBoundaryCirquentCandidate`.
This is the most concrete honest form currently available. -/
def encodeBoundaryCandidateOfBoundaryCirquentDecoder
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) (aux : BridgeAuxiliaryData Dc)
    (decodeBoundaryObject :
      (FoundationsBridgeSetup Dc aux).BoundaryObject → OrderedBoundaryProfileSource Dc) :
    (FoundationsBridgeSetup Dc aux).BoundaryObject →
      SyntacticBoundaryObject (FoundationsBoundaryAtom Dc aux) :=
  fun Y => encodeBoundaryCirquentCandidate Dc aux (decodeBoundaryObject Y)

@[simp] theorem encodeBoundaryCandidateOfBoundaryCirquentDecoder_apply
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) (aux : BridgeAuxiliaryData Dc)
    (decodeBoundaryObject :
      (FoundationsBridgeSetup Dc aux).BoundaryObject → OrderedBoundaryProfileSource Dc)
    (Y : (FoundationsBridgeSetup Dc aux).BoundaryObject) :
    encodeBoundaryCandidateOfBoundaryCirquentDecoder Dc aux decodeBoundaryObject Y =
      encodeBoundaryCirquentCandidate Dc aux (decodeBoundaryObject Y) :=
  rfl

/-- Concrete restatement of the remaining hard target: completeness of the
boundary encoder induced by a decoder from the bridge's opaque boundary carrier
to the actual foundations boundary syntax. -/
def theorem_boundary_complete_remaining_target_on_foundations_boundary_syntax
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) (aux : BridgeAuxiliaryData Dc)
    (decodeBoundaryObject :
      (FoundationsBridgeSetup Dc aux).BoundaryObject → OrderedBoundaryProfileSource Dc) : Prop :=
  theorem_boundary_complete_remaining_target
    (setup := FoundationsBridgeSetup Dc aux)
    (encodeBoundaryCandidateOfBoundaryCirquentDecoder Dc aux decodeBoundaryObject)

/-- Named bridge theorem target: the missing concrete ingredient is a decoder
from the bridge's opaque `BoundaryObject` carrier into the actual foundations
boundary syntax. Without this, the boundary-completeness theorem cannot even be
stated on a fully concrete encoder. -/
def theorem_boundary_object_foundations_decoder_target
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) (aux : BridgeAuxiliaryData Dc) : Type (u+1) :=
  (FoundationsBridgeSetup Dc aux).BoundaryObject → OrderedBoundaryProfileSource Dc

/-- Exact remaining completeness theorem on the concrete proof surface. The
existing `BoundaryAdminEquiv.generatedRec` eliminator is already sufficient for
recursion on the closure; the current blocker is the concrete decoder and the
resulting extensional completeness statement below. -/
def theorem_boundary_admin_equiv_complete_for_foundations_boundary_syntax
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) (aux : BridgeAuxiliaryData Dc)
    (decodeBoundaryObject :
      theorem_boundary_object_foundations_decoder_target Dc aux) : Prop :=
  theorem_boundary_complete_remaining_target_on_foundations_boundary_syntax
    Dc aux decodeBoundaryObject

/-- Boundary-object decoder layer at the concrete bridge surface. This is the
honest interface required when `BoundaryObject` is still an opaque field of
`BridgeAuxiliaryData`: provide a decoder into the actual foundations boundary
syntax, together with exactly the soundness/completeness obligations needed by
`BoundaryAdminEquiv`. -/
structure BoundaryObjectDecoder
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) (aux : BridgeAuxiliaryData Dc) where
  /-- Decode the bridge's opaque boundary carrier into the actual ordered
  boundary syntax from the foundations lane. -/
  decodeBoundary : theorem_boundary_object_foundations_decoder_target Dc aux
  /-- Soundness for the induced concrete boundary encoder. -/
  decode_sound :
    BoundarySoundTarget (setup := FoundationsBridgeSetup Dc aux)
      (encodeBoundaryCandidateOfBoundaryCirquentDecoder Dc aux decodeBoundary)
  /-- Completeness for the induced concrete boundary encoder. This is the
  exact `boundary_complete` obligation on the bridge-side decoder surface. -/
  decode_complete :
    theorem_boundary_admin_equiv_complete_for_foundations_boundary_syntax
      Dc aux decodeBoundary

namespace BoundaryObjectDecoder

/-- Forgetful projection to the decoder target isolated earlier. -/
def toDecoderTarget
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D} {aux : BridgeAuxiliaryData Dc}
    (decoder : BoundaryObjectDecoder Dc aux) :
    theorem_boundary_object_foundations_decoder_target Dc aux :=
  decoder.decodeBoundary

/-- A boundary-object decoder closes the concrete remaining target exactly when
its completeness field is supplied. -/
theorem closes_boundary_complete_target
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D} {aux : BridgeAuxiliaryData Dc}
    (decoder : BoundaryObjectDecoder Dc aux) :
    theorem_boundary_admin_equiv_complete_for_foundations_boundary_syntax
      Dc aux decoder.toDecoderTarget :=
  decoder.decode_complete

end BoundaryObjectDecoder

/-- Preferred bridge path: specialize the auxiliary bridge data so that the
bridge boundary carrier is the universe-correct lift of the foundations
boundary syntax. Because `BridgeAuxiliaryData` fixes
`BoundaryObject : Type (u+1)` while `Foundations.BoundaryCirquent Dc.sig`
lives in `Type u`, the faithful specialization is `ULift BoundaryCirquent`.
This removes all semantic decoder content; only `ULift.down` remains. -/
structure FoundationsBoundaryBridgeAuxiliaryData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) where
  /-- The carrier `𝒫 = {(p_k, I_k)}` of `def:carrier`. -/
  Carrier : Type (u+1)
  /-- The carrier under consideration. -/
  carrier : Carrier
  /-- The pattern-admission gate. -/
  sanctionedByPatternAdmissionGate :
    Carrier → (i : Dc.R_index) → (G : Foundations.Goal Dc.sig) →
      Foundations.Occurrence Dc (Dc.R i) G → Bool
  /-- Support data of primitive certified declarations. -/
  SupportData : Dc.R_index → Foundations.Goal Dc.sig → Type (u+1)
  /-- Named consumed semantic resources. -/
  consumes :
    {i : Dc.R_index} → {G : Foundations.Goal Dc.sig} →
      SupportData i G → Type (u+1)
  /-- Named exported semantic resources. -/
  exports :
    {i : Dc.R_index} → {G : Foundations.Goal Dc.sig} →
      SupportData i G → Type (u+1)
  /-- Replay certificate carrier. -/
  ReplayCertificate : Dc.R_index → Foundations.State Dc.sig → Type (u+1)
  /-- The boundary object of a state, now definitionally a foundations
  boundary cirquent. -/
  boundaryOf : Foundations.State Dc.sig → OrderedBoundaryProfileSource Dc
  /-- Refined interface labels. -/
  RefinedInterface : Type (u+1)
  /-- Reattachment / gluing witness data. -/
  GluingWitness : Type (u+1)
  /-- Boolean compatibility check for an attachment witness. -/
  attachmentCompatible :
    GluingWitness → OrderedBoundaryProfileSource Dc → OrderedBoundaryProfileSource Dc →
      List RefinedInterface → List RefinedInterface → Bool
  /-- Boundary exposure under sink deletion. -/
  exposeBoundaryUnderSinkDeletion :
    OrderedBoundaryProfileSource Dc → List RefinedInterface → List RefinedInterface →
      OrderedBoundaryProfileSource Dc
  /-- Boundary-level Glue. -/
  glueBoundary :
    OrderedBoundaryProfileSource Dc → List RefinedInterface → List RefinedInterface →
      GluingWitness → OrderedBoundaryProfileSource Dc
  /-- Geometric rewrite rules `R_geom`. -/
  GeometricRewriteRule : Type (u+1)
  /-- The canonical geometric rewrite rule for the sink-deletion/gluing inverse.
  Mirrors `RewriteCalculusSetup.sinkDeletionGeometricRule`. -/
  sinkDeletionGeometricRule :
    OrderedBoundaryProfileSource Dc → OrderedBoundaryProfileSource Dc →
    List RefinedInterface → List RefinedInterface →
    GeometricRewriteRule

namespace FoundationsBoundaryBridgeAuxiliaryData

/-- Convert the preferred specialized bridge data into the generic bridge data.
Here `BoundaryObject` is `ULift` of `Foundations.BoundaryCirquent`. -/
def toBridgeAuxiliaryData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) : BridgeAuxiliaryData Dc where
  Carrier := aux.Carrier
  carrier := aux.carrier
  sanctionedByPatternAdmissionGate := aux.sanctionedByPatternAdmissionGate
  SupportData := aux.SupportData
  consumes := aux.consumes
  exports := aux.exports
  ReplayCertificate := aux.ReplayCertificate
  BoundaryObject := ULift.{u+1, u} (OrderedBoundaryProfileSource Dc)
  boundaryOf := fun S => ULift.up (aux.boundaryOf S)
  RefinedInterface := aux.RefinedInterface
  GluingWitness := aux.GluingWitness
  attachmentCompatible := fun witness Y₁ Y₂ L₁ L₂ =>
    aux.attachmentCompatible witness Y₁.down Y₂.down L₁ L₂
  exposeBoundaryUnderSinkDeletion := fun Y L₁ L₂ =>
    ULift.up (aux.exposeBoundaryUnderSinkDeletion Y.down L₁ L₂)
  glueBoundary := fun Y L₁ L₂ witness =>
    ULift.up (aux.glueBoundary Y.down L₁ L₂ witness)
  GeometricRewriteRule := aux.GeometricRewriteRule
  sinkDeletionGeometricRule := fun expBdy tgtBdy rIn rOut =>
    aux.sinkDeletionGeometricRule expBdy.down tgtBdy.down rIn rOut

/-- In the preferred specialized bridge path, the decoder is just `ULift.down`
from the bridge boundary carrier to the foundations boundary syntax. -/
def preferredDecoder
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) :
    theorem_boundary_object_foundations_decoder_target Dc aux.toBridgeAuxiliaryData :=
  fun Y => Y.down

@[simp] theorem preferredDecoder_apply
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (Y : ULift.{u+1, u} (OrderedBoundaryProfileSource Dc)) :
    aux.preferredDecoder Y = Y.down :=
  rfl

/-- Preferred-layer data required to make boundary exposure concrete on the
specialized foundations bridge path, without adding any new field to the
global `RewriteCalculusSetup`. The two port maps record the minimum concrete
boundary-cirquent data needed to interpret refined interfaces as explicit
boundary entries; the concrete exposure operator is then required to agree
with the existing opaque preferred-layer field. -/
structure PreferredBoundaryExposureImplementationData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) where
  /-- Interpret a refined interface as a concrete input-boundary entry. -/
  refinedInterfaceAsInputBoundaryPort :
    aux.RefinedInterface → Σ s : Foundations.Sort_ D, Dc.sig.Var s
  /-- Interpret a refined interface as a concrete output-boundary entry. -/
  refinedInterfaceAsOutputBoundaryPort :
    aux.RefinedInterface → Σ s : Foundations.Sort_ D, Foundations.Expr Dc.sig s
  /-- Concrete preferred-layer implementation of boundary exposure. -/
  concreteExposeBoundaryUnderSinkDeletion :
    OrderedBoundaryProfileSource Dc → List aux.RefinedInterface →
      List aux.RefinedInterface → OrderedBoundaryProfileSource Dc
  /-- The concrete preferred-layer implementation agrees with the currently
  opaque preferred auxiliary field. -/
  concreteExposeBoundaryUnderSinkDeletion_spec :
    ∀ Y removed exposed,
      aux.exposeBoundaryUnderSinkDeletion Y removed exposed =
        concreteExposeBoundaryUnderSinkDeletion Y removed exposed
  /-- The concrete preferred-layer implementation commutes for successive sink
  exposures. This is the exact local law needed downstream. -/
  concreteExposeBoundaryUnderSinkDeletion_commutes :
    ∀ (Y : OrderedBoundaryProfileSource Dc)
      (removed₁ exposed₁ removed₂ exposed₂ : List aux.RefinedInterface),
      concreteExposeBoundaryUnderSinkDeletion
        (concreteExposeBoundaryUnderSinkDeletion Y removed₁ exposed₁)
        removed₂ exposed₂
      =
      concreteExposeBoundaryUnderSinkDeletion
        (concreteExposeBoundaryUnderSinkDeletion Y removed₂ exposed₂)
        removed₁ exposed₁

/-- Canonically sort unordered typed input-boundary entries by a chosen syntax
code and linear order on that code type. -/
def sortBoundaryInputEntriesByCode
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {Code : Type (u+1)}
    (code : BoundaryInputEntry Dc → Code)
    (code_injective : Function.Injective code)
    (order : LinearOrder Code)
    (entries : Multiset (BoundaryInputEntry Dc)) :
    List (BoundaryInputEntry Dc) := by
  letI : LinearOrder Code := order
  let rel : BoundaryInputEntry Dc → BoundaryInputEntry Dc → Prop :=
    fun a b => code a ≤ code b
  letI : DecidableRel rel := inferInstance
  letI : IsTrans (BoundaryInputEntry Dc) rel :=
    ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩
  letI : IsAntisymm (BoundaryInputEntry Dc) rel :=
    ⟨fun a b hab hba => code_injective (le_antisymm hab hba)⟩
  letI : IsTotal (BoundaryInputEntry Dc) rel := ⟨fun a b => le_total _ _⟩
  exact Multiset.sort rel entries

/-- Canonically sort unordered typed output-boundary entries by a chosen syntax
code and linear order on that code type. -/
def sortBoundaryOutputEntriesByCode
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {Code : Type (u+1)}
    (code : BoundaryOutputEntry Dc → Code)
    (code_injective : Function.Injective code)
    (order : LinearOrder Code)
    (entries : Multiset (BoundaryOutputEntry Dc)) :
    List (BoundaryOutputEntry Dc) := by
  letI : LinearOrder Code := order
  let rel : BoundaryOutputEntry Dc → BoundaryOutputEntry Dc → Prop :=
    fun a b => code a ≤ code b
  letI : DecidableRel rel := inferInstance
  letI : IsTrans (BoundaryOutputEntry Dc) rel :=
    ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩
  letI : IsAntisymm (BoundaryOutputEntry Dc) rel :=
    ⟨fun a b hab hba => code_injective (le_antisymm hab hba)⟩
  letI : IsTotal (BoundaryOutputEntry Dc) rel := ⟨fun a b => le_total _ _⟩
  exact Multiset.sort rel entries

/-- Order/key data needed to build a canonical display convention for
unordered typed boundary content. This is the exact local scaffold required
before any concrete order on typed variables or typed expressions is chosen. -/
structure BoundaryEntryCodeData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) where
  /-- Interpret a refined interface as a concrete input-boundary entry. -/
  refinedInterfaceAsInputBoundaryPort :
    aux.RefinedInterface → BoundaryInputEntry Dc
  /-- Interpret a refined interface as a concrete output-boundary entry. -/
  refinedInterfaceAsOutputBoundaryPort :
    aux.RefinedInterface → BoundaryOutputEntry Dc
  /-- Code type used to canonically order typed input-boundary entries. -/
  InputCode : Type (u+1)
  /-- Canonical syntax code for a typed input-boundary entry. -/
  inputEntryCode : BoundaryInputEntry Dc → InputCode
  /-- Input syntax codes determine the typed input-boundary entry uniquely. -/
  inputEntryCode_injective : Function.Injective inputEntryCode
  /-- The input-entry code type is linearly ordered. -/
  inputCode_linearOrder : LinearOrder InputCode
  /-- Existing ordered input boundaries are already sorted by the chosen input
  syntax code. -/
  orderedInputBoundaryEntries_sorted_by_code :
    ∀ Y,
      List.Sorted
        (fun a b => inputEntryCode a ≤ inputEntryCode b)
        (orderedInputBoundaryEntries Y)
  /-- Code type used to canonically order typed output-boundary entries. -/
  OutputCode : Type (u+1)
  /-- Canonical syntax code for a typed output-boundary entry. -/
  outputEntryCode : BoundaryOutputEntry Dc → OutputCode
  /-- Output syntax codes determine the typed output-boundary entry uniquely. -/
  outputEntryCode_injective : Function.Injective outputEntryCode
  /-- The output-entry code type is linearly ordered. -/
  outputCode_linearOrder : LinearOrder OutputCode
  /-- Existing ordered output boundaries are already sorted by the chosen
  output syntax code. -/
  orderedOutputBoundaryEntries_sorted_by_code :
    ∀ Y,
      List.Sorted
        (fun a b => outputEntryCode a ≤ outputEntryCode b)
        (orderedOutputBoundaryEntries Y)
  /-- Reconstructing from sorted presentations recovers the presented ordered
  input entries. This remains explicit because the generic dependent round-trip
  proof is intentionally not forced at this layer. -/
  orderedInputBoundaryEntries_linearize :
    ∀ I O,
      orderedInputBoundaryEntries
          (boundaryCirquentOfOrderedBoundaryEntries (Dc := Dc)
            (sortBoundaryInputEntriesByCode inputEntryCode inputEntryCode_injective inputCode_linearOrder I)
            (sortBoundaryOutputEntriesByCode outputEntryCode outputEntryCode_injective outputCode_linearOrder O))
        =
        sortBoundaryInputEntriesByCode inputEntryCode inputEntryCode_injective inputCode_linearOrder I
  /-- Reconstructing from sorted presentations recovers the presented ordered
  output entries. -/
  orderedOutputBoundaryEntries_linearize :
    ∀ I O,
      orderedOutputBoundaryEntries
          (boundaryCirquentOfOrderedBoundaryEntries (Dc := Dc)
            (sortBoundaryInputEntriesByCode inputEntryCode inputEntryCode_injective inputCode_linearOrder I)
            (sortBoundaryOutputEntriesByCode outputEntryCode outputEntryCode_injective outputCode_linearOrder O))
        =
        sortBoundaryOutputEntriesByCode outputEntryCode outputEntryCode_injective outputCode_linearOrder O
  /-- Linearizing the unordered summaries of an already-canonical boundary
  cirquent returns that boundary cirquent itself. -/
  linearizeBoundary_canonical :
    ∀ Y,
      boundaryCirquentOfOrderedBoundaryEntries (Dc := Dc)
          (sortBoundaryInputEntriesByCode inputEntryCode inputEntryCode_injective inputCode_linearOrder
            (↑(orderedInputBoundaryEntries Y)))
          (sortBoundaryOutputEntriesByCode outputEntryCode outputEntryCode_injective outputCode_linearOrder
            (↑(orderedOutputBoundaryEntries Y))) =
        Y
  /-- Commutative output-update law on unordered output content. -/
  removeSinkOutputs :
    Multiset (BoundaryOutputEntry Dc) →
      Multiset (BoundaryOutputEntry Dc) →
      Multiset (BoundaryOutputEntry Dc)
  /-- Successive output removals commute on unordered content. -/
  removeSinkOutputs_comm :
    ∀ O A B,
      removeSinkOutputs (removeSinkOutputs O A) B =
        removeSinkOutputs (removeSinkOutputs O B) A

structure BoundaryDisplayOrderData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) where
  /-- Interpret a refined interface as a concrete input-boundary entry. -/
  refinedInterfaceAsInputBoundaryPort :
    aux.RefinedInterface → BoundaryInputEntry Dc
  /-- Interpret a refined interface as a concrete output-boundary entry. -/
  refinedInterfaceAsOutputBoundaryPort :
    aux.RefinedInterface → BoundaryOutputEntry Dc
  /-- Chosen comparison on typed input-boundary entries. -/
  inputEntryRel : BoundaryInputEntry Dc → BoundaryInputEntry Dc → Prop
  /-- Decidability of the chosen input-entry comparison. -/
  inputEntryRel_decidable : DecidableRel inputEntryRel
  /-- Transitivity of the chosen input-entry comparison. -/
  inputEntryRel_trans : IsTrans (BoundaryInputEntry Dc) inputEntryRel
  /-- Antisymmetry of the chosen input-entry comparison. -/
  inputEntryRel_antisymm : IsAntisymm (BoundaryInputEntry Dc) inputEntryRel
  /-- Totality of the chosen input-entry comparison. -/
  inputEntryRel_total : IsTotal (BoundaryInputEntry Dc) inputEntryRel
  /-- Chosen comparison on typed output-boundary entries. -/
  outputEntryRel : BoundaryOutputEntry Dc → BoundaryOutputEntry Dc → Prop
  /-- Decidability of the chosen output-entry comparison. -/
  outputEntryRel_decidable : DecidableRel outputEntryRel
  /-- Transitivity of the chosen output-entry comparison. -/
  outputEntryRel_trans : IsTrans (BoundaryOutputEntry Dc) outputEntryRel
  /-- Antisymmetry of the chosen output-entry comparison. -/
  outputEntryRel_antisymm : IsAntisymm (BoundaryOutputEntry Dc) outputEntryRel
  /-- Totality of the chosen output-entry comparison. -/
  outputEntryRel_total : IsTotal (BoundaryOutputEntry Dc) outputEntryRel
  /-- Existing ordered input boundaries are already canonical for the chosen
  input-entry order. -/
  orderedInputBoundaryEntries_sorted :
    ∀ Y, List.Sorted inputEntryRel (orderedInputBoundaryEntries Y)
  /-- Existing ordered output boundaries are already canonical for the chosen
  output-entry order. -/
  orderedOutputBoundaryEntries_sorted :
    ∀ Y, List.Sorted outputEntryRel (orderedOutputBoundaryEntries Y)
  /-- Reconstructing from sorted presentations recovers the presented ordered
  input entries. -/
  orderedInputBoundaryEntries_linearize :
    ∀ I O,
      orderedInputBoundaryEntries
          (boundaryCirquentOfOrderedBoundaryEntries (Dc := Dc)
            (Multiset.sort inputEntryRel I)
            (Multiset.sort outputEntryRel O))
        =
        Multiset.sort inputEntryRel I
  /-- Reconstructing from sorted presentations recovers the presented ordered
  output entries. -/
  orderedOutputBoundaryEntries_linearize :
    ∀ I O,
      orderedOutputBoundaryEntries
          (boundaryCirquentOfOrderedBoundaryEntries (Dc := Dc)
            (Multiset.sort inputEntryRel I)
            (Multiset.sort outputEntryRel O))
        =
        Multiset.sort outputEntryRel O
  /-- Linearizing the unordered summaries of an already-canonical boundary
  cirquent returns that boundary cirquent itself. -/
  linearizeBoundary_canonical :
    ∀ Y,
      boundaryCirquentOfOrderedBoundaryEntries (Dc := Dc)
          (Multiset.sort inputEntryRel (↑(orderedInputBoundaryEntries Y)))
          (Multiset.sort outputEntryRel (↑(orderedOutputBoundaryEntries Y))) =
        Y
  /-- Commutative output-update law on unordered output content. -/
  removeSinkOutputs :
    Multiset (BoundaryOutputEntry Dc) →
      Multiset (BoundaryOutputEntry Dc) →
      Multiset (BoundaryOutputEntry Dc)
  /-- Successive output removals commute on unordered content. -/
  removeSinkOutputs_comm :
    ∀ O A B,
      removeSinkOutputs (removeSinkOutputs O A) B =
        removeSinkOutputs (removeSinkOutputs O B) A

/-- Local canonical display contract for a boundary cirquent: a chosen ordered
presentation of unordered boundary content, before any commitment to a
particular order key or sorting implementation. -/
structure BoundaryCanonicalDisplay
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) where
  /-- Interpret a refined interface as a concrete input-boundary entry. -/
  refinedInterfaceAsInputBoundaryPort :
    aux.RefinedInterface → Σ s : Foundations.Sort_ D, Dc.sig.Var s
  /-- Interpret a refined interface as a concrete output-boundary entry. -/
  refinedInterfaceAsOutputBoundaryPort :
    aux.RefinedInterface → Σ s : Foundations.Sort_ D, Foundations.Expr Dc.sig s
  /-- Chosen ordered presentation of unordered input-boundary content. -/
  inputPresentation :
    Multiset (Σ s : Foundations.Sort_ D, Dc.sig.Var s) →
      List (Σ s : Foundations.Sort_ D, Dc.sig.Var s)
  /-- Chosen ordered presentation of unordered output-boundary content. -/
  outputPresentation :
    Multiset (Σ s : Foundations.Sort_ D, Foundations.Expr Dc.sig s) →
      List (Σ s : Foundations.Sort_ D, Foundations.Expr Dc.sig s)
  /-- The chosen input presentation enumerates exactly the given unordered
  input content. -/
  inputPresentation_spec :
    ∀ I, ↑(inputPresentation I) = I
  /-- The chosen output presentation enumerates exactly the given unordered
  output content. -/
  outputPresentation_spec :
    ∀ O, ↑(outputPresentation O) = O
  /-- Reconstructing from the chosen presentations recovers those presented
  input entries exactly. -/
  orderedInputBoundaryEntries_linearize :
    ∀ I O,
      orderedInputBoundaryEntries
          (boundaryCirquentOfOrderedBoundaryEntries (Dc := Dc)
            (inputPresentation I) (outputPresentation O)) =
        inputPresentation I
  /-- Reconstructing from the chosen presentations recovers those presented
  output entries exactly. -/
  orderedOutputBoundaryEntries_linearize :
    ∀ I O,
      orderedOutputBoundaryEntries
          (boundaryCirquentOfOrderedBoundaryEntries (Dc := Dc)
            (inputPresentation I) (outputPresentation O)) =
        outputPresentation O
  /-- The chosen input presentation already matches any canonical ordered input
  boundary carried by a boundary cirquent. -/
  inputPresentation_canonical :
    ∀ Y,
      inputPresentation (↑(orderedInputBoundaryEntries Y)) =
        orderedInputBoundaryEntries Y
  /-- The chosen output presentation already matches any canonical ordered
  output boundary carried by a boundary cirquent. -/
  outputPresentation_canonical :
    ∀ Y,
      outputPresentation (↑(orderedOutputBoundaryEntries Y)) =
        orderedOutputBoundaryEntries Y
  /-- Linearizing the unordered summaries of an already-canonical boundary
  cirquent returns that boundary cirquent itself. -/
  linearizeBoundary_canonical :
    ∀ Y,
      boundaryCirquentOfOrderedBoundaryEntries (Dc := Dc)
          (inputPresentation (↑(orderedInputBoundaryEntries Y)))
          (outputPresentation (↑(orderedOutputBoundaryEntries Y))) =
        Y
  /-- Commutative output-update law on unordered output content. -/
  removeSinkOutputs :
    Multiset (Σ s : Foundations.Sort_ D, Foundations.Expr Dc.sig s) →
      Multiset (Σ s : Foundations.Sort_ D, Foundations.Expr Dc.sig s) →
      Multiset (Σ s : Foundations.Sort_ D, Foundations.Expr Dc.sig s)
  /-- Successive output removals commute on unordered content. -/
  removeSinkOutputs_comm :
    ∀ O A B,
      removeSinkOutputs (removeSinkOutputs O A) B =
        removeSinkOutputs (removeSinkOutputs O B) A

/-- Local canonical-linearization contract for the preferred path: boundary
cirquents are treated as ordered presentations of unordered boundary content.
The contract supplies summary maps into multiset-valued boundary content and a
chosen canonical linearization back into ordered syntax, together with the
laws needed to transport commutative multiset updates into the existing local
preferred design interface. -/
structure BoundaryCanonicalLinearization
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) where
  /-- Interpret a refined interface as a concrete input-boundary entry. -/
  refinedInterfaceAsInputBoundaryPort :
    aux.RefinedInterface → Σ s : Foundations.Sort_ D, Dc.sig.Var s
  /-- Interpret a refined interface as a concrete output-boundary entry. -/
  refinedInterfaceAsOutputBoundaryPort :
    aux.RefinedInterface → Σ s : Foundations.Sort_ D, Foundations.Expr Dc.sig s
  /-- Summarize the input boundary of an ordered boundary cirquent as
  commutative content. -/
  summarizeInputBoundary :
    OrderedBoundaryProfileSource Dc →
      Multiset (Σ s : Foundations.Sort_ D, Dc.sig.Var s)
  /-- Summarize the output boundary of an ordered boundary cirquent as
  commutative content. -/
  summarizeOutputBoundary :
    OrderedBoundaryProfileSource Dc →
      Multiset (Σ s : Foundations.Sort_ D, Foundations.Expr Dc.sig s)
  /-- Canonically linearize unordered boundary content back into ordered
  boundary syntax. -/
  linearizeBoundary :
    Multiset (Σ s : Foundations.Sort_ D, Dc.sig.Var s) →
      Multiset (Σ s : Foundations.Sort_ D, Foundations.Expr Dc.sig s) →
      OrderedBoundaryProfileSource Dc
  /-- Summarizing a canonical linearization recovers the input summary. -/
  summarizeInput_linearizeBoundary :
    ∀ I O,
      summarizeInputBoundary (linearizeBoundary I O) = I
  /-- Summarizing a canonical linearization recovers the output summary. -/
  summarizeOutput_linearizeBoundary :
    ∀ I O,
      summarizeOutputBoundary (linearizeBoundary I O) = O
  /-- Canonical linearization fixes already-canonical boundary cirquents. -/
  linearizeBoundary_summarizeBoundary :
    ∀ Y,
      linearizeBoundary (summarizeInputBoundary Y) (summarizeOutputBoundary Y) = Y
  /-- Commutative output-update law on unordered boundary content. This keeps
  the contract honest even before committing to a concrete removal operation. -/
  removeSinkOutputs :
    Multiset (Σ s : Foundations.Sort_ D, Foundations.Expr Dc.sig s) →
      Multiset (Σ s : Foundations.Sort_ D, Foundations.Expr Dc.sig s) →
      Multiset (Σ s : Foundations.Sort_ D, Foundations.Expr Dc.sig s)
  /-- Successive output removals commute on unordered content. -/
  removeSinkOutputs_comm :
    ∀ O A B,
      removeSinkOutputs (removeSinkOutputs O A) B =
        removeSinkOutputs (removeSinkOutputs O B) A

namespace BoundaryCanonicalDisplay

/-- A canonical display convention yields the corresponding canonical
linearization contract: summarize a boundary cirquent by forgetting order down
to multisets, then rebuild ordered syntax using the chosen presentation maps. -/
def toBoundaryCanonicalLinearization
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (display : BoundaryCanonicalDisplay aux) :
    BoundaryCanonicalLinearization aux where
  refinedInterfaceAsInputBoundaryPort := display.refinedInterfaceAsInputBoundaryPort
  refinedInterfaceAsOutputBoundaryPort := display.refinedInterfaceAsOutputBoundaryPort
  summarizeInputBoundary := fun Y => ↑(orderedInputBoundaryEntries Y)
  summarizeOutputBoundary := fun Y => ↑(orderedOutputBoundaryEntries Y)
  linearizeBoundary := fun I O =>
    boundaryCirquentOfOrderedBoundaryEntries (Dc := Dc)
      (display.inputPresentation I) (display.outputPresentation O)
  summarizeInput_linearizeBoundary := by
    intro I O
    simpa [display.orderedInputBoundaryEntries_linearize] using
      display.inputPresentation_spec I
  summarizeOutput_linearizeBoundary := by
    intro I O
    simpa [display.orderedOutputBoundaryEntries_linearize] using
      display.outputPresentation_spec O
  linearizeBoundary_summarizeBoundary := by
    intro Y
    exact display.linearizeBoundary_canonical Y
  removeSinkOutputs := display.removeSinkOutputs
  removeSinkOutputs_comm := display.removeSinkOutputs_comm

end BoundaryCanonicalDisplay

namespace BoundaryDisplayOrderData

/-- Boundary display order data yields a canonical display convention by
sorting unordered boundary content with the chosen total orders and recording
the exact canonicality laws those orders are required to satisfy. -/
def toBoundaryCanonicalDisplay
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (data : BoundaryDisplayOrderData aux) :
    BoundaryCanonicalDisplay aux := by
  letI : DecidableRel data.inputEntryRel := data.inputEntryRel_decidable
  letI : IsTrans (BoundaryInputEntry Dc) data.inputEntryRel :=
    data.inputEntryRel_trans
  letI : IsAntisymm (BoundaryInputEntry Dc) data.inputEntryRel :=
    data.inputEntryRel_antisymm
  letI : IsTotal (BoundaryInputEntry Dc) data.inputEntryRel :=
    data.inputEntryRel_total
  letI : DecidableRel data.outputEntryRel := data.outputEntryRel_decidable
  letI : IsTrans (BoundaryOutputEntry Dc) data.outputEntryRel :=
    data.outputEntryRel_trans
  letI : IsAntisymm (BoundaryOutputEntry Dc) data.outputEntryRel :=
    data.outputEntryRel_antisymm
  letI : IsTotal (BoundaryOutputEntry Dc) data.outputEntryRel :=
    data.outputEntryRel_total
  refine
    { refinedInterfaceAsInputBoundaryPort := data.refinedInterfaceAsInputBoundaryPort
      refinedInterfaceAsOutputBoundaryPort := data.refinedInterfaceAsOutputBoundaryPort
      inputPresentation := fun I => Multiset.sort data.inputEntryRel I
      outputPresentation := fun O => Multiset.sort data.outputEntryRel O
      inputPresentation_spec := ?_
      outputPresentation_spec := ?_
      orderedInputBoundaryEntries_linearize := data.orderedInputBoundaryEntries_linearize
      orderedOutputBoundaryEntries_linearize := data.orderedOutputBoundaryEntries_linearize
      inputPresentation_canonical := ?_
      outputPresentation_canonical := ?_
      linearizeBoundary_canonical := data.linearizeBoundary_canonical
      removeSinkOutputs := data.removeSinkOutputs
      removeSinkOutputs_comm := data.removeSinkOutputs_comm }
  · intro I
    simpa using (Multiset.sort_eq data.inputEntryRel I)
  · intro O
    simpa using (Multiset.sort_eq data.outputEntryRel O)
  · intro Y
    refine @List.eq_of_perm_of_sorted (BoundaryInputEntry Dc) data.inputEntryRel
      data.inputEntryRel_antisymm
      (Multiset.sort data.inputEntryRel
        (↑(orderedInputBoundaryEntries Y) : Multiset (BoundaryInputEntry Dc)))
      (orderedInputBoundaryEntries Y)
      ?_ ?_ (data.orderedInputBoundaryEntries_sorted Y)
    · apply Multiset.coe_eq_coe.mp
      simpa using
        (Multiset.sort_eq data.inputEntryRel
          (↑(orderedInputBoundaryEntries Y) : Multiset (BoundaryInputEntry Dc)))
    · simpa using
        (Multiset.sort_sorted data.inputEntryRel
          (↑(orderedInputBoundaryEntries Y) : Multiset (BoundaryInputEntry Dc)))
  · intro Y
    refine @List.eq_of_perm_of_sorted (BoundaryOutputEntry Dc) data.outputEntryRel
      data.outputEntryRel_antisymm
      (Multiset.sort data.outputEntryRel
        (↑(orderedOutputBoundaryEntries Y) : Multiset (BoundaryOutputEntry Dc)))
      (orderedOutputBoundaryEntries Y)
      ?_ ?_ (data.orderedOutputBoundaryEntries_sorted Y)
    · apply Multiset.coe_eq_coe.mp
      simpa using
        (Multiset.sort_eq data.outputEntryRel
          (↑(orderedOutputBoundaryEntries Y) : Multiset (BoundaryOutputEntry Dc)))
    · simpa using
        (Multiset.sort_sorted data.outputEntryRel
          (↑(orderedOutputBoundaryEntries Y) : Multiset (BoundaryOutputEntry Dc)))

end BoundaryDisplayOrderData

/-- Explicit relation on typed input-boundary entries induced by a chosen code
type and linear order on codes. -/
def boundaryInputEntryCodeRel
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {Code : Type (u+1)}
    (code : BoundaryInputEntry Dc → Code)
    (order : LinearOrder Code) :
    BoundaryInputEntry Dc → BoundaryInputEntry Dc → Prop := by
  letI : LinearOrder Code := order
  exact fun a b => code a ≤ code b

/-- Explicit relation on typed output-boundary entries induced by a chosen code
type and linear order on codes. -/
def boundaryOutputEntryCodeRel
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {Code : Type (u+1)}
    (code : BoundaryOutputEntry Dc → Code)
    (order : LinearOrder Code) :
    BoundaryOutputEntry Dc → BoundaryOutputEntry Dc → Prop := by
  letI : LinearOrder Code := order
  exact fun a b => code a ≤ code b

 /-- Primitive interface carrier code data for a syntactic signature. This is
the first genuinely missing legibility layer: if ports, packet generators, or
structural constructors are opaque, then no canonical syntax-tree code for
sorts can be derived. -/
structure LegiblePrimitiveInterfacePresentation
    (D : Foundations.PrimitiveInterfaceData.{u}) where
  /-- Legible name/code type for primitive boundary-port labels. -/
  PortName : Type (u+1)
  /-- Canonical display name/code for primitive boundary-port labels. -/
  portName : D.P0 → PortName
  /-- Primitive boundary-port labels are determined uniquely by their display
  names/codes. -/
  portName_injective : Function.Injective portName
  /-- The primitive boundary-port name/code type is linearly ordered. -/
  portName_linearOrder : LinearOrder PortName
  /-- Legible name/code type for primitive packet-interface generators. -/
  PacketName : Type (u+1)
  /-- Canonical display name/code for primitive packet-interface generators. -/
  packetName : D.PiPkt → PacketName
  /-- Primitive packet-interface generators are determined uniquely by their
  display names/codes. -/
  packetName_injective : Function.Injective packetName
  /-- The primitive packet-generator name/code type is linearly ordered. -/
  packetName_linearOrder : LinearOrder PacketName
  /-- Legible name/code type for structural interface constructors. -/
  ConstructorName : Type (u+1)
  /-- Canonical display name/code for structural interface constructors. -/
  constructorName : D.CInt → ConstructorName
  /-- Structural interface constructors are determined uniquely by their
  display names/codes. -/
  constructorName_injective : Function.Injective constructorName
  /-- The structural-constructor name/code type is linearly ordered. -/
  constructorName_linearOrder : LinearOrder ConstructorName

 /-- Primitive interface carrier code data for a syntactic signature. This is
the first genuinely missing legibility layer: if ports, packet generators, or
structural constructors are opaque, then no canonical syntax-tree code for
sorts can be derived. -/
structure PrimitiveInterfaceCarrierCodeData
    (D : Foundations.PrimitiveInterfaceData.{u}) where
  /-- Canonical code type for primitive boundary-port labels. -/
  PortCode : Type (u+1)
  /-- Canonical syntax code for primitive boundary-port labels. -/
  portCode : D.P0 → PortCode
  /-- Primitive boundary-port labels are determined uniquely by their codes. -/
  portCode_injective : Function.Injective portCode
  /-- The primitive boundary-port code type is linearly ordered. -/
  portCode_linearOrder : LinearOrder PortCode
  /-- Canonical code type for primitive packet-interface generators. -/
  PacketCode : Type (u+1)
  /-- Canonical syntax code for primitive packet-interface generators. -/
  packetCode : D.PiPkt → PacketCode
  /-- Primitive packet-interface generators are determined uniquely by their
  codes. -/
  packetCode_injective : Function.Injective packetCode
  /-- The primitive packet-interface generator code type is linearly ordered. -/
  packetCode_linearOrder : LinearOrder PacketCode
  /-- Canonical code type for structural interface constructors. -/
  ConstructorCode : Type (u+1)
  /-- Canonical syntax code for structural interface constructors. -/
  constructorCode : D.CInt → ConstructorCode
  /-- Structural constructors are determined uniquely by their codes. -/
  constructorCode_injective : Function.Injective constructorCode
  /-- The structural-constructor code type is linearly ordered. -/
  constructorCode_linearOrder : LinearOrder ConstructorCode

namespace LegiblePrimitiveInterfacePresentation

/-- A legible presentation of the primitive interface carriers forgets to the
raw carrier-code data required by the signature-code pipeline. -/
def toPrimitiveInterfaceCarrierCodeData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (presentation : LegiblePrimitiveInterfacePresentation D) :
    PrimitiveInterfaceCarrierCodeData D where
  PortCode := presentation.PortName
  portCode := presentation.portName
  portCode_injective := presentation.portName_injective
  portCode_linearOrder := presentation.portName_linearOrder
  PacketCode := presentation.PacketName
  packetCode := presentation.packetName
  packetCode_injective := presentation.packetName_injective
  packetCode_linearOrder := presentation.packetName_linearOrder
  ConstructorCode := presentation.ConstructorName
  constructorCode := presentation.constructorName
  constructorCode_injective := presentation.constructorName_injective
  constructorCode_linearOrder := presentation.constructorName_linearOrder

end LegiblePrimitiveInterfacePresentation

/-- Signature-level syntax-code data for boundary entries. This is the precise
missing scaffold when the foundations lane still treats variables and the
primitive signature carriers as opaque: it records canonical display codes for
sorts, variables, and expressions, together with the induced boundary-entry
codes and the remaining canonical-display obligations. -/
structure SignatureBoundaryCodeData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D)
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) where
  /-- Interpret a refined interface as a concrete input-boundary entry. -/
  refinedInterfaceAsInputBoundaryPort :
    aux.RefinedInterface → BoundaryInputEntry Dc
  /-- Interpret a refined interface as a concrete output-boundary entry. -/
  refinedInterfaceAsOutputBoundaryPort :
    aux.RefinedInterface → BoundaryOutputEntry Dc
  /-- Canonical code type for sorts. -/
  SortCode : Type (u+1)
  /-- Canonical syntax code for sorts. -/
  sortCode : Foundations.Sort_ D → SortCode
  /-- Sort codes determine sorts uniquely. -/
  sortCode_injective : Function.Injective sortCode
  /-- The sort-code type is linearly ordered. -/
  sortCode_linearOrder : LinearOrder SortCode
  /-- Canonical code type for variables. -/
  VarCode : Type (u+1)
  /-- Canonical syntax code for variables. -/
  varCode : {s : Foundations.Sort_ D} → Dc.sig.Var s → VarCode
  /-- Variables of a fixed sort are determined uniquely by their codes. -/
  varCode_injective : ∀ s, Function.Injective (fun v : Dc.sig.Var s => varCode v)
  /-- The variable-code type is linearly ordered. -/
  varCode_linearOrder : LinearOrder VarCode
  /-- Canonical code type for active expressions. -/
  ExprCode : Type (u+1)
  /-- Canonical syntax code for active expressions. -/
  exprCode : {s : Foundations.Sort_ D} → Foundations.Expr Dc.sig s → ExprCode
  /-- Active expressions of a fixed sort are determined uniquely by their
  codes. -/
  exprCode_injective :
    ∀ s,
      Function.Injective (fun e : Foundations.Expr Dc.sig s => exprCode e)
  /-- The expression-code type is linearly ordered. -/
  exprCode_linearOrder : LinearOrder ExprCode
  /-- Linearly ordered code type for typed input-boundary entries. -/
  inputEntryCode_linearOrder : LinearOrder (SortCode × VarCode)
  /-- The derived typed input-boundary entry code is injective. -/
  inputEntryCode_injective :
    Function.Injective
      (fun entry : BoundaryInputEntry Dc =>
        (sortCode entry.1, varCode entry.2))
  /-- Linearly ordered code type for typed output-boundary entries. -/
  outputEntryCode_linearOrder : LinearOrder (SortCode × ExprCode)
  /-- The derived typed output-boundary entry code is injective. -/
  outputEntryCode_injective :
    Function.Injective
      (fun entry : BoundaryOutputEntry Dc =>
        (sortCode entry.1, exprCode entry.2))
  /-- Existing ordered input boundaries are already sorted by the derived input
  syntax code. -/
  orderedInputBoundaryEntries_sorted_by_code :
    ∀ Y,
      List.Sorted
        (boundaryInputEntryCodeRel
          (fun entry : BoundaryInputEntry Dc =>
            (sortCode entry.1, varCode entry.2))
          inputEntryCode_linearOrder)
        (orderedInputBoundaryEntries Y)
  /-- Existing ordered output boundaries are already sorted by the derived
  output syntax code. -/
  orderedOutputBoundaryEntries_sorted_by_code :
    ∀ Y,
      List.Sorted
        (boundaryOutputEntryCodeRel
          (fun entry : BoundaryOutputEntry Dc =>
            (sortCode entry.1, exprCode entry.2))
          outputEntryCode_linearOrder)
        (orderedOutputBoundaryEntries Y)
  /-- Reconstructing from the code-sorted presentations recovers the presented
  ordered input entries. -/
  orderedInputBoundaryEntries_linearize :
    ∀ I O,
      orderedInputBoundaryEntries
          (boundaryCirquentOfOrderedBoundaryEntries (Dc := Dc)
            (sortBoundaryInputEntriesByCode
              (fun entry : BoundaryInputEntry Dc =>
                (sortCode entry.1, varCode entry.2))
              inputEntryCode_injective inputEntryCode_linearOrder I)
            (sortBoundaryOutputEntriesByCode
              (fun entry : BoundaryOutputEntry Dc =>
                (sortCode entry.1, exprCode entry.2))
              outputEntryCode_injective outputEntryCode_linearOrder O))
        =
        sortBoundaryInputEntriesByCode
          (fun entry : BoundaryInputEntry Dc =>
            (sortCode entry.1, varCode entry.2))
          inputEntryCode_injective inputEntryCode_linearOrder I
  /-- Reconstructing from the code-sorted presentations recovers the presented
  ordered output entries. -/
  orderedOutputBoundaryEntries_linearize :
    ∀ I O,
      orderedOutputBoundaryEntries
          (boundaryCirquentOfOrderedBoundaryEntries (Dc := Dc)
            (sortBoundaryInputEntriesByCode
              (fun entry : BoundaryInputEntry Dc =>
                (sortCode entry.1, varCode entry.2))
              inputEntryCode_injective inputEntryCode_linearOrder I)
            (sortBoundaryOutputEntriesByCode
              (fun entry : BoundaryOutputEntry Dc =>
                (sortCode entry.1, exprCode entry.2))
              outputEntryCode_injective outputEntryCode_linearOrder O))
        =
        sortBoundaryOutputEntriesByCode
          (fun entry : BoundaryOutputEntry Dc =>
            (sortCode entry.1, exprCode entry.2))
          outputEntryCode_injective outputEntryCode_linearOrder O
  /-- Linearizing the unordered summaries of an already-canonical boundary
  cirquent returns that boundary cirquent itself. -/
  linearizeBoundary_canonical :
    ∀ Y,
      boundaryCirquentOfOrderedBoundaryEntries (Dc := Dc)
          (sortBoundaryInputEntriesByCode
            (fun entry : BoundaryInputEntry Dc =>
              (sortCode entry.1, varCode entry.2))
            inputEntryCode_injective inputEntryCode_linearOrder
            (↑(orderedInputBoundaryEntries Y)))
          (sortBoundaryOutputEntriesByCode
            (fun entry : BoundaryOutputEntry Dc =>
              (sortCode entry.1, exprCode entry.2))
            outputEntryCode_injective outputEntryCode_linearOrder
            (↑(orderedOutputBoundaryEntries Y))) =
        Y
  /-- Commutative output-update law on unordered output content. -/
  removeSinkOutputs :
    Multiset (BoundaryOutputEntry Dc) →
      Multiset (BoundaryOutputEntry Dc) →
      Multiset (BoundaryOutputEntry Dc)
  /-- The preferred auxiliary exposure field is the canonical summarize,
  update, and linearize operator determined by this boundary-code package. -/
  exposeBoundaryUnderSinkDeletion_canonical :
    ∀ Y removed exposed,
      aux.exposeBoundaryUnderSinkDeletion Y removed exposed =
        boundaryCirquentOfOrderedBoundaryEntries (Dc := Dc)
          (sortBoundaryInputEntriesByCode
            (fun entry : BoundaryInputEntry Dc =>
              (sortCode entry.1, varCode entry.2))
            inputEntryCode_injective inputEntryCode_linearOrder
            ((↑(orderedInputBoundaryEntries Y) : Multiset (BoundaryInputEntry Dc)) +
              ↑(exposed.map refinedInterfaceAsInputBoundaryPort)))
          (sortBoundaryOutputEntriesByCode
            (fun entry : BoundaryOutputEntry Dc =>
              (sortCode entry.1, exprCode entry.2))
            outputEntryCode_injective outputEntryCode_linearOrder
            (removeSinkOutputs
              (↑(orderedOutputBoundaryEntries Y) : Multiset (BoundaryOutputEntry Dc))
              ↑(removed.map refinedInterfaceAsOutputBoundaryPort)))
  /-- Successive output removals commute on unordered content. -/
  removeSinkOutputs_comm :
    ∀ O A B,
      removeSinkOutputs (removeSinkOutputs O A) B =
        removeSinkOutputs (removeSinkOutputs O B) A

/-- Packet-reference retagging data carried by the concrete preferred gluing
witness. `localIndex` is the packet index inside one component record, while
`ambientIndex` is its tagged ambient image. -/
structure PreferredPacketReferenceRetagging where
  localIndex : Nat
  ambientIndex : Nat

namespace PreferredPacketReferenceRetagging

/-- Retag a packet-reference witness datum by shifting its ambient index. -/
def retag (offset : Nat) (datum : PreferredPacketReferenceRetagging) :
    PreferredPacketReferenceRetagging where
  localIndex := datum.localIndex
  ambientIndex := offset + datum.ambientIndex

end PreferredPacketReferenceRetagging

/-- Boundary side remembered by a boundary-summand retagging entry. -/
inductive PreferredBoundarySummandSide where
  | input
  | output

/-- Boundary-summand retagging data carried by the concrete preferred gluing
witness. -/
structure PreferredBoundarySummandRetagging where
  side : PreferredBoundarySummandSide
  localIndex : Nat
  ambientIndex : Nat

namespace PreferredBoundarySummandRetagging

/-- Retag a boundary-summand witness datum by shifting its ambient index. -/
def retag (offset : Nat) (datum : PreferredBoundarySummandRetagging) :
    PreferredBoundarySummandRetagging where
  side := datum.side
  localIndex := datum.localIndex
  ambientIndex := offset + datum.ambientIndex

end PreferredBoundarySummandRetagging

/-- Concrete preferred gluing witness carrier for the tensor lane.

This witness is intentionally proof-relevant and metadata-carrying. It keeps:

- packet-reference retagging data;
- boundary-summand retagging data;
- a concrete glued-boundary proposal;
- a boolean attachment-compatibility projection;
- proof slots for attachment/gluing compatibility facts.

The current preferred tensor lane only needs concrete carrier operations on
this type; the theorem surfaces that would consume the proof slots remain
separate. -/
structure ConcretePreferredGluingWitness
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) where
  packetRetaggings : List PreferredPacketReferenceRetagging
  boundarySummandRetaggings : List PreferredBoundarySummandRetagging
  attachmentCompatibleValue : Bool
  gluedBoundary : OrderedBoundaryProfileSource Dc

/-- Universe-correct preferred gluing-witness carrier used by the concrete
preferred auxiliary object. -/
abbrev ConcretePreferredGluingWitnessCarrier
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) :=
  ULift.{u+1, u} (ConcretePreferredGluingWitness Dc)

/-- Replace the opaque gluing-witness carrier of a preferred foundations bridge
auxiliary object by the concrete preferred witness carrier above, while keeping
all non-gluing fields unchanged.

This is the smallest honest concrete auxiliary object for the tensor lane: the
attachment-compatibility check and boundary glue now read directly from the
concrete witness data, rather than from an opaque witness type. -/
def concretePreferredBoundaryBridgeAuxiliaryData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) :
    FoundationsBoundaryBridgeAuxiliaryData Dc where
  Carrier := aux.Carrier
  carrier := aux.carrier
  sanctionedByPatternAdmissionGate := aux.sanctionedByPatternAdmissionGate
  SupportData := aux.SupportData
  consumes := aux.consumes
  exports := aux.exports
  ReplayCertificate := aux.ReplayCertificate
  boundaryOf := aux.boundaryOf
  RefinedInterface := aux.RefinedInterface
  GluingWitness := ConcretePreferredGluingWitnessCarrier Dc
  attachmentCompatible :=
    fun (witness : ConcretePreferredGluingWitnessCarrier Dc) _ _ _ _ =>
      witness.down.attachmentCompatibleValue
  exposeBoundaryUnderSinkDeletion := aux.exposeBoundaryUnderSinkDeletion
  glueBoundary :=
    fun _ _ _ (witness : ConcretePreferredGluingWitnessCarrier Dc) =>
      witness.down.gluedBoundary
  GeometricRewriteRule := aux.GeometricRewriteRule
  sinkDeletionGeometricRule := aux.sinkDeletionGeometricRule

namespace SignatureBoundaryCodeData

/-- Transport a preferred boundary-code package to the concrete preferred
auxiliary object. This is fieldwise because the concrete auxiliary object keeps
the same boundary carrier, refined-interface carrier, and exposure operator; it
only replaces the gluing-witness carrier and its attachment/glue projections. -/
def toConcretePreferredAuxiliaryData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (codes : SignatureBoundaryCodeData Dc aux) :
    SignatureBoundaryCodeData Dc (concretePreferredBoundaryBridgeAuxiliaryData aux) where
  refinedInterfaceAsInputBoundaryPort := codes.refinedInterfaceAsInputBoundaryPort
  refinedInterfaceAsOutputBoundaryPort := codes.refinedInterfaceAsOutputBoundaryPort
  SortCode := codes.SortCode
  sortCode := codes.sortCode
  sortCode_injective := codes.sortCode_injective
  sortCode_linearOrder := codes.sortCode_linearOrder
  VarCode := codes.VarCode
  varCode := codes.varCode
  varCode_injective := codes.varCode_injective
  varCode_linearOrder := codes.varCode_linearOrder
  ExprCode := codes.ExprCode
  exprCode := codes.exprCode
  exprCode_injective := codes.exprCode_injective
  exprCode_linearOrder := codes.exprCode_linearOrder
  inputEntryCode_linearOrder := codes.inputEntryCode_linearOrder
  inputEntryCode_injective := codes.inputEntryCode_injective
  outputEntryCode_linearOrder := codes.outputEntryCode_linearOrder
  outputEntryCode_injective := codes.outputEntryCode_injective
  orderedInputBoundaryEntries_sorted_by_code :=
    codes.orderedInputBoundaryEntries_sorted_by_code
  orderedOutputBoundaryEntries_sorted_by_code :=
    codes.orderedOutputBoundaryEntries_sorted_by_code
  orderedInputBoundaryEntries_linearize :=
    codes.orderedInputBoundaryEntries_linearize
  orderedOutputBoundaryEntries_linearize :=
    codes.orderedOutputBoundaryEntries_linearize
  linearizeBoundary_canonical := codes.linearizeBoundary_canonical
  removeSinkOutputs := codes.removeSinkOutputs
  exposeBoundaryUnderSinkDeletion_canonical := by
    intro Y removed exposed
    simpa [concretePreferredBoundaryBridgeAuxiliaryData] using
      codes.exposeBoundaryUnderSinkDeletion_canonical Y removed exposed
  removeSinkOutputs_comm := codes.removeSinkOutputs_comm

/-- Signature-level syntax codes yield the boundary-entry code data required by
the canonical display pipeline. -/
def toBoundaryEntryCodeData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (codes : SignatureBoundaryCodeData Dc aux) :
    BoundaryEntryCodeData aux where
  refinedInterfaceAsInputBoundaryPort := codes.refinedInterfaceAsInputBoundaryPort
  refinedInterfaceAsOutputBoundaryPort := codes.refinedInterfaceAsOutputBoundaryPort
  InputCode := codes.SortCode × codes.VarCode
  inputEntryCode := fun entry =>
    (codes.sortCode entry.1, codes.varCode entry.2)
  inputEntryCode_injective := codes.inputEntryCode_injective
  inputCode_linearOrder := codes.inputEntryCode_linearOrder
  orderedInputBoundaryEntries_sorted_by_code :=
    codes.orderedInputBoundaryEntries_sorted_by_code
  OutputCode := codes.SortCode × codes.ExprCode
  outputEntryCode := fun entry =>
    (codes.sortCode entry.1, codes.exprCode entry.2)
  outputEntryCode_injective := codes.outputEntryCode_injective
  outputCode_linearOrder := codes.outputEntryCode_linearOrder
  orderedOutputBoundaryEntries_sorted_by_code :=
    codes.orderedOutputBoundaryEntries_sorted_by_code
  orderedInputBoundaryEntries_linearize :=
    codes.orderedInputBoundaryEntries_linearize
  orderedOutputBoundaryEntries_linearize :=
    codes.orderedOutputBoundaryEntries_linearize
  linearizeBoundary_canonical := codes.linearizeBoundary_canonical
  removeSinkOutputs := codes.removeSinkOutputs
  removeSinkOutputs_comm := codes.removeSinkOutputs_comm

end SignatureBoundaryCodeData

/-- Legible presentation of the intended syntactic signature. This is the
manuscript-faithful theorem target immediately above `SyntacticSignatureCodeData`:
it asks not merely for abstract codes, but for explicit legible names/codes for
primitive carriers, operations, sorts, variables, and typed expressions. -/
structure LegibleSignaturePresentation
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D)
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    extends SignatureBoundaryCodeData Dc aux where
  /-- Legible presentation of the primitive interface carriers. -/
  primitivePresentation : LegiblePrimitiveInterfacePresentation D
  /-- Legible name/code type for operation symbols. -/
  OpName : Type (u+1)
  /-- Canonical display name/code for operation symbols. -/
  opName : Dc.sig.Op → OpName
  /-- Operation symbols are determined uniquely by their display names/codes. -/
  opName_injective : Function.Injective opName
  /-- The operation-symbol name/code type is linearly ordered. -/
  opName_linearOrder : LinearOrder OpName

/-- Richer syntactic-signature code package: a `SignatureBoundaryCodeData`
plus explicit code data for the primitive interface carriers and operation
symbols. This is the natural extension point when one wants canonical syntax
codes to be visibly rooted in the concrete signature data instead of merely
postulated at the sort / variable / expression layers. -/
structure SyntacticSignatureCodeData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D)
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    extends SignatureBoundaryCodeData Dc aux where
  /-- Canonical code data for the primitive interface carriers of `D`. -/
  primitiveCarrierCodes : PrimitiveInterfaceCarrierCodeData D
  /-- Canonical code type for operation symbols. -/
  OpCode : Type (u+1)
  /-- Canonical syntax code for operation symbols. -/
  opCode : Dc.sig.Op → OpCode
  /-- Operation symbols are determined uniquely by their codes. -/
  opCode_injective : Function.Injective opCode
  /-- The operation-symbol code type is linearly ordered. -/
  opCode_linearOrder : LinearOrder OpCode

namespace LegibleSignaturePresentation

/-- A legible signature presentation forgets to the richer syntactic-signature
code package used by the boundary-display pipeline. -/
def toSyntacticSignatureCodeData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (presentation : LegibleSignaturePresentation Dc aux) :
    SyntacticSignatureCodeData Dc aux :=
  { presentation.toSignatureBoundaryCodeData with
    primitiveCarrierCodes :=
      presentation.primitivePresentation.toPrimitiveInterfaceCarrierCodeData
    OpCode := presentation.OpName
    opCode := presentation.opName
    opCode_injective := presentation.opName_injective
    opCode_linearOrder := presentation.opName_linearOrder }

end LegibleSignaturePresentation

namespace NamedFreeBoundaryAdapter

def coreCodes
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive) :
    NamedSignaturePresentation.CoreCodeData presentation.signaturePresentation :=
  presentation.signaturePresentation.toCoreCodeData

namespace Core

variable {primitive : NamedPrimitiveInterfacePresentation}
variable (presentation : NamedDoctrinePresentation primitive)

abbrev SortCode : Type (u+1) :=
  (NamedFreeBoundaryAdapter.coreCodes presentation).SortCode

abbrev VarCode : Type (u+1) :=
  (NamedFreeBoundaryAdapter.coreCodes presentation).VarCode

abbrev ExprCode : Type (u+1) :=
  (NamedFreeBoundaryAdapter.coreCodes presentation).ExprCode

abbrev PortCode : Type (u+1) :=
  (NamedFreeBoundaryAdapter.coreCodes presentation).PortCode

abbrev PacketCode : Type (u+1) :=
  (NamedFreeBoundaryAdapter.coreCodes presentation).PacketCode

abbrev ConstructorCode : Type (u+1) :=
  (NamedFreeBoundaryAdapter.coreCodes presentation).ConstructorCode

abbrev OpCode : Type (u+1) :=
  (NamedFreeBoundaryAdapter.coreCodes presentation).OpCode

abbrev InputCode : Type (u+1) :=
  SortCode presentation × VarCode presentation

abbrev OutputCode : Type (u+1) :=
  SortCode presentation × ExprCode presentation

def sortCode :
    Foundations.Sort_ primitive.toPrimitiveInterfaceData → SortCode presentation :=
  (NamedFreeBoundaryAdapter.coreCodes presentation).sortCode

def varCode :
    {s : Foundations.Sort_ primitive.toPrimitiveInterfaceData} →
      presentation.toDoctrine.sig.Var s → VarCode presentation :=
  @(NamedFreeBoundaryAdapter.coreCodes presentation).varCode

def exprCode :
    {s : Foundations.Sort_ primitive.toPrimitiveInterfaceData} →
      Foundations.Expr presentation.toDoctrine.sig s → ExprCode presentation :=
  @(NamedFreeBoundaryAdapter.coreCodes presentation).exprCode

def portCode :
    primitive.toPrimitiveInterfaceData.P0 → PortCode presentation :=
  (NamedFreeBoundaryAdapter.coreCodes presentation).portCode

def packetCode :
    primitive.toPrimitiveInterfaceData.PiPkt → PacketCode presentation :=
  (NamedFreeBoundaryAdapter.coreCodes presentation).packetCode

def constructorCode :
    primitive.toPrimitiveInterfaceData.CInt → ConstructorCode presentation :=
  (NamedFreeBoundaryAdapter.coreCodes presentation).constructorCode

def opCode :
    presentation.toDoctrine.sig.Op → OpCode presentation :=
  (NamedFreeBoundaryAdapter.coreCodes presentation).opCode

theorem sortCode_injective :
    Function.Injective (sortCode presentation) :=
  (NamedFreeBoundaryAdapter.coreCodes presentation).sortCode_injective

theorem varCode_injective
    (s : Foundations.Sort_ primitive.toPrimitiveInterfaceData) :
    Function.Injective
      (fun v : presentation.toDoctrine.sig.Var s => varCode presentation v) := by
  simpa [varCode] using (NamedFreeBoundaryAdapter.coreCodes presentation).varCode_injective s

theorem exprCode_injective
    (s : Foundations.Sort_ primitive.toPrimitiveInterfaceData) :
    Function.Injective
      (fun e : Foundations.Expr presentation.toDoctrine.sig s => exprCode presentation e) := by
  simpa [exprCode] using (NamedFreeBoundaryAdapter.coreCodes presentation).exprCode_injective s

theorem portCode_injective :
    Function.Injective (portCode presentation) :=
  (NamedFreeBoundaryAdapter.coreCodes presentation).portCode_injective

theorem packetCode_injective :
    Function.Injective (packetCode presentation) :=
  (NamedFreeBoundaryAdapter.coreCodes presentation).packetCode_injective

theorem constructorCode_injective :
    Function.Injective (constructorCode presentation) :=
  (NamedFreeBoundaryAdapter.coreCodes presentation).constructorCode_injective

theorem opCode_injective :
    Function.Injective (opCode presentation) :=
  (NamedFreeBoundaryAdapter.coreCodes presentation).opCode_injective

def inputEntryCode :
    BoundaryInputEntry presentation.toDoctrine → InputCode presentation :=
  fun entry =>
    (sortCode presentation entry.1, varCode presentation entry.2)

def outputEntryCode :
    BoundaryOutputEntry presentation.toDoctrine → OutputCode presentation :=
  fun entry =>
    (sortCode presentation entry.1, exprCode presentation entry.2)

theorem inputEntryCode_injective :
    Function.Injective (inputEntryCode presentation) := by
  let coreCodes := NamedFreeBoundaryAdapter.coreCodes presentation
  rintro ⟨s₁, v₁⟩ ⟨s₂, v₂⟩ h
  dsimp [inputEntryCode, sortCode, varCode] at h
  rcases Prod.mk.inj h with ⟨hs, hv⟩
  have hs' : s₁ = s₂ := coreCodes.sortCode_injective hs
  subst hs'
  have hv' : v₁ = v₂ := coreCodes.varCode_injective s₁ hv
  subst hv'
  rfl

theorem outputEntryCode_injective :
    Function.Injective (outputEntryCode presentation) := by
  let coreCodes := NamedFreeBoundaryAdapter.coreCodes presentation
  rintro ⟨s₁, e₁⟩ ⟨s₂, e₂⟩ h
  dsimp [outputEntryCode, sortCode, exprCode] at h
  rcases Prod.mk.inj h with ⟨hs, he⟩
  have hs' : s₁ = s₂ := coreCodes.sortCode_injective hs
  subst hs'
  have he' : e₁ = e₂ := coreCodes.exprCode_injective s₁ he
  subst he'
  rfl

def inputRel
    (order : LinearOrder (InputCode presentation)) :
    BoundaryInputEntry presentation.toDoctrine →
      BoundaryInputEntry presentation.toDoctrine → Prop := by
  letI : LinearOrder (InputCode presentation) := order
  exact fun a b => inputEntryCode presentation a ≤ inputEntryCode presentation b

def outputRel
    (order : LinearOrder (OutputCode presentation)) :
    BoundaryOutputEntry presentation.toDoctrine →
      BoundaryOutputEntry presentation.toDoctrine → Prop := by
  letI : LinearOrder (OutputCode presentation) := order
  exact fun a b => outputEntryCode presentation a ≤ outputEntryCode presentation b

def sortInputEntriesByCode
    (order : LinearOrder (InputCode presentation))
    (entries : Multiset (BoundaryInputEntry presentation.toDoctrine)) :
    List (BoundaryInputEntry presentation.toDoctrine) := by
  letI : LinearOrder (InputCode presentation) := order
  let rel : BoundaryInputEntry presentation.toDoctrine →
      BoundaryInputEntry presentation.toDoctrine → Prop :=
    fun a b => inputEntryCode presentation a ≤ inputEntryCode presentation b
  letI : DecidableRel rel := inferInstance
  letI : IsTrans (BoundaryInputEntry presentation.toDoctrine) rel :=
    ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩
  letI : IsAntisymm (BoundaryInputEntry presentation.toDoctrine) rel :=
    ⟨fun a b hab hba => inputEntryCode_injective presentation (le_antisymm hab hba)⟩
  letI : IsTotal (BoundaryInputEntry presentation.toDoctrine) rel :=
    ⟨fun a b => le_total _ _⟩
  exact Multiset.sort rel entries

def sortOutputEntriesByCode
    (order : LinearOrder (OutputCode presentation))
    (entries : Multiset (BoundaryOutputEntry presentation.toDoctrine)) :
    List (BoundaryOutputEntry presentation.toDoctrine) := by
  letI : LinearOrder (OutputCode presentation) := order
  let rel : BoundaryOutputEntry presentation.toDoctrine →
      BoundaryOutputEntry presentation.toDoctrine → Prop :=
    fun a b => outputEntryCode presentation a ≤ outputEntryCode presentation b
  letI : DecidableRel rel := inferInstance
  letI : IsTrans (BoundaryOutputEntry presentation.toDoctrine) rel :=
    ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩
  letI : IsAntisymm (BoundaryOutputEntry presentation.toDoctrine) rel :=
    ⟨fun a b hab hba => outputEntryCode_injective presentation (le_antisymm hab hba)⟩
  letI : IsTotal (BoundaryOutputEntry presentation.toDoctrine) rel :=
    ⟨fun a b => le_total _ _⟩
  exact Multiset.sort rel entries

end Core

theorem inputEntryCode_injective
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive) :
    Function.Injective
      (fun entry : BoundaryInputEntry presentation.toDoctrine =>
        ((NamedFreeBoundaryAdapter.coreCodes presentation).sortCode entry.1,
          (NamedFreeBoundaryAdapter.coreCodes presentation).varCode
            (s := entry.1) entry.2)) := by
  simpa [Core.inputEntryCode, Core.sortCode, Core.varCode] using
    (Core.inputEntryCode_injective presentation)

theorem outputEntryCode_injective
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive) :
    Function.Injective
      (fun entry : BoundaryOutputEntry presentation.toDoctrine =>
        ((NamedFreeBoundaryAdapter.coreCodes presentation).sortCode entry.1,
          (NamedFreeBoundaryAdapter.coreCodes presentation).exprCode
            (s := entry.1) entry.2)) := by
  simpa [Core.outputEntryCode, Core.sortCode, Core.exprCode] using
    (Core.outputEntryCode_injective presentation)

structure BoundaryProofs
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive) where
  inputCode_linearOrder : LinearOrder
    (Core.InputCode presentation)
  outputCode_linearOrder : LinearOrder
    (Core.OutputCode presentation)
  orderedInputBoundaryEntries_sorted_by_code :
    ∀ Y,
      List.Sorted
        (fun a b =>
          (fun entry : BoundaryInputEntry presentation.toDoctrine =>
            ((NamedFreeBoundaryAdapter.coreCodes presentation).sortCode entry.1,
              (NamedFreeBoundaryAdapter.coreCodes presentation).varCode
                (s := entry.1) entry.2)) a
            ≤
          (fun entry : BoundaryInputEntry presentation.toDoctrine =>
            ((NamedFreeBoundaryAdapter.coreCodes presentation).sortCode entry.1,
              (NamedFreeBoundaryAdapter.coreCodes presentation).varCode
                (s := entry.1) entry.2)) b)
        (orderedInputBoundaryEntries Y)
  orderedOutputBoundaryEntries_sorted_by_code :
    ∀ Y,
      List.Sorted
        (fun a b =>
          (fun entry : BoundaryOutputEntry presentation.toDoctrine =>
            ((NamedFreeBoundaryAdapter.coreCodes presentation).sortCode entry.1,
              (NamedFreeBoundaryAdapter.coreCodes presentation).exprCode
                (s := entry.1) entry.2)) a
            ≤
          (fun entry : BoundaryOutputEntry presentation.toDoctrine =>
            ((NamedFreeBoundaryAdapter.coreCodes presentation).sortCode entry.1,
              (NamedFreeBoundaryAdapter.coreCodes presentation).exprCode
                (s := entry.1) entry.2)) b)
        (orderedOutputBoundaryEntries Y)
  orderedInputBoundaryEntries_linearize :
    ∀ I O,
      orderedInputBoundaryEntries
          (boundaryCirquentOfOrderedBoundaryEntries (Dc := presentation.toDoctrine)
            (sortBoundaryInputEntriesByCode (Dc := presentation.toDoctrine)
              (Code := Core.InputCode presentation)
              (fun entry : BoundaryInputEntry presentation.toDoctrine =>
                ((NamedFreeBoundaryAdapter.coreCodes presentation).sortCode entry.1,
                  (NamedFreeBoundaryAdapter.coreCodes presentation).varCode
                    (s := entry.1) entry.2))
              (NamedFreeBoundaryAdapter.inputEntryCode_injective presentation)
              inputCode_linearOrder I)
            (sortBoundaryOutputEntriesByCode (Dc := presentation.toDoctrine)
              (Code := Core.OutputCode presentation)
              (fun entry : BoundaryOutputEntry presentation.toDoctrine =>
                ((NamedFreeBoundaryAdapter.coreCodes presentation).sortCode entry.1,
                  (NamedFreeBoundaryAdapter.coreCodes presentation).exprCode
                    (s := entry.1) entry.2))
              (NamedFreeBoundaryAdapter.outputEntryCode_injective presentation)
              outputCode_linearOrder O))
        =
        sortBoundaryInputEntriesByCode (Dc := presentation.toDoctrine)
          (Code := Core.InputCode presentation)
          (fun entry : BoundaryInputEntry presentation.toDoctrine =>
            ((NamedFreeBoundaryAdapter.coreCodes presentation).sortCode entry.1,
              (NamedFreeBoundaryAdapter.coreCodes presentation).varCode
                (s := entry.1) entry.2))
          (NamedFreeBoundaryAdapter.inputEntryCode_injective presentation)
          inputCode_linearOrder I
  orderedOutputBoundaryEntries_linearize :
    ∀ I O,
      orderedOutputBoundaryEntries
          (boundaryCirquentOfOrderedBoundaryEntries (Dc := presentation.toDoctrine)
            (sortBoundaryInputEntriesByCode (Dc := presentation.toDoctrine)
              (Code := Core.InputCode presentation)
              (fun entry : BoundaryInputEntry presentation.toDoctrine =>
                ((NamedFreeBoundaryAdapter.coreCodes presentation).sortCode entry.1,
                  (NamedFreeBoundaryAdapter.coreCodes presentation).varCode
                    (s := entry.1) entry.2))
              (NamedFreeBoundaryAdapter.inputEntryCode_injective presentation)
              inputCode_linearOrder I)
            (sortBoundaryOutputEntriesByCode (Dc := presentation.toDoctrine)
              (Code := Core.OutputCode presentation)
              (fun entry : BoundaryOutputEntry presentation.toDoctrine =>
                ((NamedFreeBoundaryAdapter.coreCodes presentation).sortCode entry.1,
                  (NamedFreeBoundaryAdapter.coreCodes presentation).exprCode
                    (s := entry.1) entry.2))
              (NamedFreeBoundaryAdapter.outputEntryCode_injective presentation)
              outputCode_linearOrder O))
        =
        sortBoundaryOutputEntriesByCode (Dc := presentation.toDoctrine)
          (Code := Core.OutputCode presentation)
          (fun entry : BoundaryOutputEntry presentation.toDoctrine =>
            ((NamedFreeBoundaryAdapter.coreCodes presentation).sortCode entry.1,
              (NamedFreeBoundaryAdapter.coreCodes presentation).exprCode
                (s := entry.1) entry.2))
          (NamedFreeBoundaryAdapter.outputEntryCode_injective presentation)
          outputCode_linearOrder O
  linearizeBoundary_canonical :
    ∀ Y,
      boundaryCirquentOfOrderedBoundaryEntries (Dc := presentation.toDoctrine)
          (sortBoundaryInputEntriesByCode (Dc := presentation.toDoctrine)
            (Code := Core.InputCode presentation)
            (fun entry : BoundaryInputEntry presentation.toDoctrine =>
              ((NamedFreeBoundaryAdapter.coreCodes presentation).sortCode entry.1,
                (NamedFreeBoundaryAdapter.coreCodes presentation).varCode
                  (s := entry.1) entry.2))
            (NamedFreeBoundaryAdapter.inputEntryCode_injective presentation)
            inputCode_linearOrder
            (↑(orderedInputBoundaryEntries Y)))
          (sortBoundaryOutputEntriesByCode (Dc := presentation.toDoctrine)
            (Code := Core.OutputCode presentation)
            (fun entry : BoundaryOutputEntry presentation.toDoctrine =>
              ((NamedFreeBoundaryAdapter.coreCodes presentation).sortCode entry.1,
                (NamedFreeBoundaryAdapter.coreCodes presentation).exprCode
                  (s := entry.1) entry.2))
            (NamedFreeBoundaryAdapter.outputEntryCode_injective presentation)
            outputCode_linearOrder
            (↑(orderedOutputBoundaryEntries Y))) =
        Y
  /-- The preferred auxiliary exposure field agrees with the named/free
  canonical summarize-update-linearize operator induced by the core-code
  presentation. This is the exact extra theorem needed to feed the named/free
  linearization package into the preferred witness layer. -/
  exposeBoundaryUnderSinkDeletion_canonical :
    ∀ {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
      (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
      Y removed exposed,
      aux.exposeBoundaryUnderSinkDeletion Y removed exposed =
        boundaryCirquentOfOrderedBoundaryEntries (Dc := presentation.toDoctrine)
          (sortBoundaryInputEntriesByCode (Dc := presentation.toDoctrine)
            (Code := Core.InputCode presentation)
            (fun entry : BoundaryInputEntry presentation.toDoctrine =>
              ((NamedFreeBoundaryAdapter.coreCodes presentation).sortCode entry.1,
                (NamedFreeBoundaryAdapter.coreCodes presentation).varCode
                  (s := entry.1) entry.2))
            (NamedFreeBoundaryAdapter.inputEntryCode_injective presentation)
            inputCode_linearOrder
            ((↑(orderedInputBoundaryEntries Y) :
              Multiset (BoundaryInputEntry presentation.toDoctrine)) +
              ↑(exposed.map boundaryCodes.refinedInterfaceAsInputBoundaryPort)))
          (sortBoundaryOutputEntriesByCode (Dc := presentation.toDoctrine)
            (Code := Core.OutputCode presentation)
            (fun entry : BoundaryOutputEntry presentation.toDoctrine =>
              ((NamedFreeBoundaryAdapter.coreCodes presentation).sortCode entry.1,
                (NamedFreeBoundaryAdapter.coreCodes presentation).exprCode
                  (s := entry.1) entry.2))
            (NamedFreeBoundaryAdapter.outputEntryCode_injective presentation)
            outputCode_linearOrder
            (boundaryCodes.removeSinkOutputs
              (↑(orderedOutputBoundaryEntries Y) :
                Multiset (BoundaryOutputEntry presentation.toDoctrine))
              ↑(removed.map boundaryCodes.refinedInterfaceAsOutputBoundaryPort)))

def primitivePresentation
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive) :
    LegiblePrimitiveInterfacePresentation primitive.toPrimitiveInterfaceData where
  PortName := ULift.{u+1, u} (primitive.PortName)
  portName := fun p => ULift.up (primitive.portCode p)
  portName_injective := by
    intro p₁ p₂ h
    exact congrArg ULift.down h
  portName_linearOrder := inferInstance
  PacketName := ULift.{u+1, u} (primitive.PacketName)
  packetName := fun π => ULift.up (primitive.packetCode π)
  packetName_injective := by
    intro π₁ π₂ h
    exact congrArg ULift.down h
  packetName_linearOrder := inferInstance
  ConstructorName := ULift.{u+1, u} (primitive.ConstructorName)
  constructorName := fun c => ULift.up (primitive.constructorCode c)
  constructorName_injective := by
    intro c₁ c₂ h
    exact congrArg ULift.down h
  constructorName_linearOrder := inferInstance

def primitiveCarrierCodes
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive) :
    PrimitiveInterfaceCarrierCodeData primitive.toPrimitiveInterfaceData :=
  (primitivePresentation presentation).toPrimitiveInterfaceCarrierCodeData

def opCodeType
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive) : Type (u+1) :=
  (NamedFreeBoundaryAdapter.coreCodes presentation).OpCode

def opCode
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive) :
    presentation.toDoctrine.sig.Op → opCodeType presentation :=
  fun ω => (NamedFreeBoundaryAdapter.coreCodes presentation).opCode ω

theorem opCode_injective
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive) :
    Function.Injective (opCode presentation) :=
  (NamedFreeBoundaryAdapter.coreCodes presentation).opCode_injective

def opCode_linearOrder
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive) :
    LinearOrder (opCodeType presentation) :=
  (NamedFreeBoundaryAdapter.coreCodes presentation).opCode_linearOrder

def toSignatureBoundaryCodeData
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : BoundaryProofs presentation) :
    SignatureBoundaryCodeData presentation.toDoctrine aux := by
  let coreCodes := NamedFreeBoundaryAdapter.coreCodes presentation
  exact
  { refinedInterfaceAsInputBoundaryPort :=
      boundaryCodes.refinedInterfaceAsInputBoundaryPort
    refinedInterfaceAsOutputBoundaryPort :=
      boundaryCodes.refinedInterfaceAsOutputBoundaryPort
    SortCode := coreCodes.SortCode
    sortCode := coreCodes.sortCode
    sortCode_injective := coreCodes.sortCode_injective
    sortCode_linearOrder := coreCodes.sortCode_linearOrder
    VarCode := coreCodes.VarCode
    varCode := coreCodes.varCode
    varCode_injective := coreCodes.varCode_injective
    varCode_linearOrder := coreCodes.varCode_linearOrder
    ExprCode := coreCodes.ExprCode
    exprCode := coreCodes.exprCode
    exprCode_injective := coreCodes.exprCode_injective
    exprCode_linearOrder := coreCodes.exprCode_linearOrder
    inputEntryCode_linearOrder := proofs.inputCode_linearOrder
    inputEntryCode_injective := by
      intro entry₁ entry₂ h
      rcases entry₁ with ⟨s₁, v₁⟩
      rcases entry₂ with ⟨s₂, v₂⟩
      have hs := congrArg Prod.fst h
      change coreCodes.sortCode s₁ = coreCodes.sortCode s₂ at hs
      have hv := congrArg Prod.snd h
      change coreCodes.varCode (s := s₁) v₁ = coreCodes.varCode (s := s₂) v₂ at hv
      have hs' : s₁ = s₂ := coreCodes.sortCode_injective hs
      subst hs'
      have hv' : v₁ = v₂ := coreCodes.varCode_injective s₁ hv
      subst hv'
      rfl
    outputEntryCode_linearOrder := proofs.outputCode_linearOrder
    outputEntryCode_injective := by
      intro entry₁ entry₂ h
      rcases entry₁ with ⟨s₁, e₁⟩
      rcases entry₂ with ⟨s₂, e₂⟩
      have hs := congrArg Prod.fst h
      change coreCodes.sortCode s₁ = coreCodes.sortCode s₂ at hs
      have he := congrArg Prod.snd h
      change coreCodes.exprCode (s := s₁) e₁ = coreCodes.exprCode (s := s₂) e₂ at he
      have hs' : s₁ = s₂ := coreCodes.sortCode_injective hs
      subst hs'
      have he' : e₁ = e₂ := coreCodes.exprCode_injective s₁ he
      subst he'
      rfl
    orderedInputBoundaryEntries_sorted_by_code :=
      proofs.orderedInputBoundaryEntries_sorted_by_code
    orderedOutputBoundaryEntries_sorted_by_code :=
      proofs.orderedOutputBoundaryEntries_sorted_by_code
    orderedInputBoundaryEntries_linearize :=
      proofs.orderedInputBoundaryEntries_linearize
    orderedOutputBoundaryEntries_linearize :=
      proofs.orderedOutputBoundaryEntries_linearize
    linearizeBoundary_canonical :=
      proofs.linearizeBoundary_canonical
    removeSinkOutputs := boundaryCodes.removeSinkOutputs
    exposeBoundaryUnderSinkDeletion_canonical := by
      intro Y removed exposed
      exact proofs.exposeBoundaryUnderSinkDeletion_canonical
        boundaryCodes Y removed exposed
    removeSinkOutputs_comm := boundaryCodes.removeSinkOutputs_comm }

end NamedFreeBoundaryAdapter

def namedFreeSyntax_toSignatureBoundaryCodeData
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    SignatureBoundaryCodeData presentation.toDoctrine aux :=
  NamedFreeBoundaryAdapter.toSignatureBoundaryCodeData
    presentation
    boundaryCodes
    proofs

/-- Local bridge from the named/free syntax package into the boundary-display
pipeline. The boundary-facing fields are staged through
`SignatureBoundaryCodeData`; this extension only adds the primitive-carrier and
operation-symbol code payload from the named syntax layer. -/
def namedFreeSyntax_toSyntacticSignatureCodeData
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    SyntacticSignatureCodeData presentation.toDoctrine aux := by
  let parent : SignatureBoundaryCodeData presentation.toDoctrine aux :=
    namedFreeSyntax_toSignatureBoundaryCodeData presentation boundaryCodes proofs
  let primitiveCarrierCodes :
      PrimitiveInterfaceCarrierCodeData primitive.toPrimitiveInterfaceData :=
    NamedFreeBoundaryAdapter.primitiveCarrierCodes presentation
  let childOpCode := NamedFreeBoundaryAdapter.opCodeType presentation
  let childOpEncode := NamedFreeBoundaryAdapter.opCode presentation
  let childOpEncode_injective := NamedFreeBoundaryAdapter.opCode_injective presentation
  let childOpOrder := NamedFreeBoundaryAdapter.opCode_linearOrder presentation
  exact
    { refinedInterfaceAsInputBoundaryPort := parent.refinedInterfaceAsInputBoundaryPort
      refinedInterfaceAsOutputBoundaryPort := parent.refinedInterfaceAsOutputBoundaryPort
      SortCode := parent.SortCode
      sortCode := parent.sortCode
      sortCode_injective := parent.sortCode_injective
      sortCode_linearOrder := parent.sortCode_linearOrder
      VarCode := parent.VarCode
      varCode := parent.varCode
      varCode_injective := parent.varCode_injective
      varCode_linearOrder := parent.varCode_linearOrder
      ExprCode := parent.ExprCode
      exprCode := parent.exprCode
      exprCode_injective := parent.exprCode_injective
      exprCode_linearOrder := parent.exprCode_linearOrder
      inputEntryCode_linearOrder := parent.inputEntryCode_linearOrder
      inputEntryCode_injective := parent.inputEntryCode_injective
      outputEntryCode_linearOrder := parent.outputEntryCode_linearOrder
      outputEntryCode_injective := parent.outputEntryCode_injective
      orderedInputBoundaryEntries_sorted_by_code := parent.orderedInputBoundaryEntries_sorted_by_code
      orderedOutputBoundaryEntries_sorted_by_code := parent.orderedOutputBoundaryEntries_sorted_by_code
      orderedInputBoundaryEntries_linearize := parent.orderedInputBoundaryEntries_linearize
      orderedOutputBoundaryEntries_linearize := parent.orderedOutputBoundaryEntries_linearize
      linearizeBoundary_canonical := parent.linearizeBoundary_canonical
      removeSinkOutputs := parent.removeSinkOutputs
      exposeBoundaryUnderSinkDeletion_canonical :=
        parent.exposeBoundaryUnderSinkDeletion_canonical
      removeSinkOutputs_comm := parent.removeSinkOutputs_comm
      primitiveCarrierCodes := primitiveCarrierCodes
      OpCode := childOpCode
      opCode := childOpEncode
      opCode_injective := childOpEncode_injective
      opCode_linearOrder := childOpOrder }

namespace SyntacticSignatureCodeData

/-- Forget the extra primitive-carrier and operation-symbol code data down to
the boundary-facing syntax-code interface. -/
def forgetToSignatureBoundaryCodeData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (codes : SyntacticSignatureCodeData Dc aux) :
    SignatureBoundaryCodeData Dc aux :=
  { refinedInterfaceAsInputBoundaryPort := codes.refinedInterfaceAsInputBoundaryPort
    refinedInterfaceAsOutputBoundaryPort := codes.refinedInterfaceAsOutputBoundaryPort
    SortCode := codes.SortCode
    sortCode := codes.sortCode
    sortCode_injective := codes.sortCode_injective
    sortCode_linearOrder := codes.sortCode_linearOrder
    VarCode := codes.VarCode
    varCode := codes.varCode
    varCode_injective := codes.varCode_injective
    varCode_linearOrder := codes.varCode_linearOrder
    ExprCode := codes.ExprCode
    exprCode := codes.exprCode
    exprCode_injective := codes.exprCode_injective
    exprCode_linearOrder := codes.exprCode_linearOrder
    inputEntryCode_linearOrder := codes.inputEntryCode_linearOrder
    inputEntryCode_injective := codes.inputEntryCode_injective
    outputEntryCode_linearOrder := codes.outputEntryCode_linearOrder
    outputEntryCode_injective := codes.outputEntryCode_injective
    orderedInputBoundaryEntries_sorted_by_code :=
      codes.orderedInputBoundaryEntries_sorted_by_code
    orderedOutputBoundaryEntries_sorted_by_code :=
      codes.orderedOutputBoundaryEntries_sorted_by_code
    orderedInputBoundaryEntries_linearize :=
      codes.orderedInputBoundaryEntries_linearize
    orderedOutputBoundaryEntries_linearize :=
      codes.orderedOutputBoundaryEntries_linearize
    linearizeBoundary_canonical := codes.linearizeBoundary_canonical
    removeSinkOutputs := codes.removeSinkOutputs
    exposeBoundaryUnderSinkDeletion_canonical :=
      codes.exposeBoundaryUnderSinkDeletion_canonical
    removeSinkOutputs_comm := codes.removeSinkOutputs_comm }

end SyntacticSignatureCodeData

namespace BoundaryEntryCodeData

/-- Syntax-code data yields the order/key data required for canonical display.
This isolates the remaining concrete task to constructing canonical syntax
codes for typed boundary entries. -/
def toBoundaryDisplayOrderData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (codes : BoundaryEntryCodeData aux) :
    BoundaryDisplayOrderData aux := by
  letI : LinearOrder codes.InputCode := codes.inputCode_linearOrder
  letI : LinearOrder codes.OutputCode := codes.outputCode_linearOrder
  refine
    { refinedInterfaceAsInputBoundaryPort := codes.refinedInterfaceAsInputBoundaryPort
      refinedInterfaceAsOutputBoundaryPort := codes.refinedInterfaceAsOutputBoundaryPort
      inputEntryRel := fun a b => codes.inputEntryCode a ≤ codes.inputEntryCode b
      inputEntryRel_decidable := inferInstance
      inputEntryRel_trans := ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩
      inputEntryRel_antisymm := ⟨fun a b hab hba =>
        codes.inputEntryCode_injective (le_antisymm hab hba)⟩
      inputEntryRel_total := ⟨fun a b => le_total _ _⟩
      outputEntryRel := fun a b => codes.outputEntryCode a ≤ codes.outputEntryCode b
      outputEntryRel_decidable := inferInstance
      outputEntryRel_trans := ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩
      outputEntryRel_antisymm := ⟨fun a b hab hba =>
        codes.outputEntryCode_injective (le_antisymm hab hba)⟩
      outputEntryRel_total := ⟨fun a b => le_total _ _⟩
      orderedInputBoundaryEntries_sorted := codes.orderedInputBoundaryEntries_sorted_by_code
      orderedOutputBoundaryEntries_sorted :=
        codes.orderedOutputBoundaryEntries_sorted_by_code
      orderedInputBoundaryEntries_linearize := codes.orderedInputBoundaryEntries_linearize
      orderedOutputBoundaryEntries_linearize :=
        codes.orderedOutputBoundaryEntries_linearize
      linearizeBoundary_canonical := codes.linearizeBoundary_canonical
      removeSinkOutputs := codes.removeSinkOutputs
      removeSinkOutputs_comm := codes.removeSinkOutputs_comm }

end BoundaryEntryCodeData

/-- Assemble the named/free syntax adapter directly into the boundary-entry code
data used by the canonical-display pipeline. -/
def namedFreeSyntax_toBoundaryEntryCodeData
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    BoundaryEntryCodeData aux :=
  SignatureBoundaryCodeData.toBoundaryEntryCodeData
    (namedFreeSyntax_toSignatureBoundaryCodeData presentation boundaryCodes proofs)

/-- Named/free syntax code data determines the order/key data required for a
canonical boundary display. -/
def namedFreeSyntax_toBoundaryDisplayOrderData
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    BoundaryDisplayOrderData aux :=
  BoundaryEntryCodeData.toBoundaryDisplayOrderData
    (namedFreeSyntax_toBoundaryEntryCodeData presentation boundaryCodes proofs)

/-- Named/free syntax code data gives a canonical boundary display convention. -/
def namedFreeSyntax_toBoundaryCanonicalDisplay
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    BoundaryCanonicalDisplay aux :=
  BoundaryDisplayOrderData.toBoundaryCanonicalDisplay
    (namedFreeSyntax_toBoundaryDisplayOrderData presentation boundaryCodes proofs)

/-- Named/free syntax code data therefore yields the corresponding canonical
boundary linearization contract. -/
def namedFreeSyntax_toBoundaryCanonicalLinearization
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    BoundaryCanonicalLinearization aux :=
  BoundaryCanonicalDisplay.toBoundaryCanonicalLinearization
    (namedFreeSyntax_toBoundaryCanonicalDisplay presentation boundaryCodes proofs)

/-- Manuscript-facing alias for the first resumed theorem package on the main
lane: named/free syntax code data gives canonical boundary display. -/
def theorem_named_free_syntax_code_data_gives_canonical_boundary_display
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    BoundaryCanonicalDisplay aux :=
  namedFreeSyntax_toBoundaryCanonicalDisplay presentation boundaryCodes proofs

/-- Manuscript-facing alias for the next immediate corollary: the same
named/free syntax package gives canonical boundary linearization. -/
def theorem_named_free_syntax_code_data_gives_canonical_boundary_linearization
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    BoundaryCanonicalLinearization aux :=
  namedFreeSyntax_toBoundaryCanonicalLinearization presentation boundaryCodes proofs

/-- Stronger preferred-layer design contract for a genuinely commutative
boundary-exposure implementation. It records a commutative summary of the
input- and output-boundary information of a boundary cirquent, together with a
derived concrete exposure operator. This is the smallest local layer at which a
non-fake commutative implementation can currently be described. -/
structure PreferredCommutativeBoundaryExposureDesign
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) where
  /-- Interpret a refined interface as a concrete input-boundary entry. -/
  refinedInterfaceAsInputBoundaryPort :
    aux.RefinedInterface → Σ s : Foundations.Sort_ D, Dc.sig.Var s
  /-- Interpret a refined interface as a concrete output-boundary entry. -/
  refinedInterfaceAsOutputBoundaryPort :
    aux.RefinedInterface → Σ s : Foundations.Sort_ D, Foundations.Expr Dc.sig s
  /-- Commutative summary of input-boundary data. -/
  InputBoundarySummary : Type (u+1)
  /-- Commutative summary of output-boundary data. -/
  OutputBoundarySummary : Type (u+1)
  /-- Summarize the input boundary carried by a boundary cirquent. -/
  inputSummaryOfBoundary : OrderedBoundaryProfileSource Dc → InputBoundarySummary
  /-- Summarize the output boundary carried by a boundary cirquent. -/
  outputSummaryOfBoundary : OrderedBoundaryProfileSource Dc → OutputBoundarySummary
  /-- Summarize the newly exposed input-boundary contribution of a list of
  refined interfaces. -/
  exposedInputSummary : List aux.RefinedInterface → InputBoundarySummary
  /-- Summarize the sink-output contribution to be removed from the output
  boundary. -/
  removedOutputSummary : List aux.RefinedInterface → OutputBoundarySummary
  /-- Add an exposed-input summary to the current input boundary summary. -/
  addExposedInputs : InputBoundarySummary → InputBoundarySummary → InputBoundarySummary
  /-- Remove a sink-output summary from the current output boundary summary. -/
  removeSinkOutputs : OutputBoundarySummary → OutputBoundarySummary → OutputBoundarySummary
  /-- Rebuild a boundary cirquent from the two commutative summaries. -/
  realizeBoundaryFromSummaries :
    InputBoundarySummary → OutputBoundarySummary → OrderedBoundaryProfileSource Dc
  /-- Taking the input summary of a rebuilt boundary recovers the original
  input summary. -/
  inputSummary_realizeBoundaryFromSummaries :
    ∀ I O,
      inputSummaryOfBoundary (realizeBoundaryFromSummaries I O) = I
  /-- Taking the output summary of a rebuilt boundary recovers the original
  output summary. -/
  outputSummary_realizeBoundaryFromSummaries :
    ∀ I O,
      outputSummaryOfBoundary (realizeBoundaryFromSummaries I O) = O
  /-- Successive exposed-input updates commute. -/
  addExposedInputs_comm :
    ∀ I A B,
      addExposedInputs (addExposedInputs I A) B =
        addExposedInputs (addExposedInputs I B) A
  /-- Successive sink-output removals commute. -/
  removeSinkOutputs_comm :
    ∀ O A B,
      removeSinkOutputs (removeSinkOutputs O A) B =
        removeSinkOutputs (removeSinkOutputs O B) A

namespace PreferredCommutativeBoundaryExposureDesign

/-- The concrete preferred-layer exposure operator derived from the summary
operations of a commutative preferred boundary-exposure design. -/
def concreteExposeBoundaryUnderSinkDeletion
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (design : PreferredCommutativeBoundaryExposureDesign aux) :
    OrderedBoundaryProfileSource Dc → List aux.RefinedInterface →
      List aux.RefinedInterface → OrderedBoundaryProfileSource Dc :=
  fun Y removed exposed =>
    design.realizeBoundaryFromSummaries
      (design.addExposedInputs (design.inputSummaryOfBoundary Y)
        (design.exposedInputSummary exposed))
      (design.removeSinkOutputs (design.outputSummaryOfBoundary Y)
        (design.removedOutputSummary removed))

/-- The derived concrete exposure operator commutes for successive sink
exposures. -/
theorem concreteExposeBoundaryUnderSinkDeletion_commutes
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (design : PreferredCommutativeBoundaryExposureDesign aux) :
    ∀ (Y : OrderedBoundaryProfileSource Dc)
      (removed₁ exposed₁ removed₂ exposed₂ : List aux.RefinedInterface),
      design.concreteExposeBoundaryUnderSinkDeletion
        (design.concreteExposeBoundaryUnderSinkDeletion Y removed₁ exposed₁)
        removed₂ exposed₂
      =
      design.concreteExposeBoundaryUnderSinkDeletion
        (design.concreteExposeBoundaryUnderSinkDeletion Y removed₂ exposed₂)
        removed₁ exposed₁ := by
  intro Y removed₁ exposed₁ removed₂ exposed₂
  simp [PreferredCommutativeBoundaryExposureDesign.concreteExposeBoundaryUnderSinkDeletion]
  rw [design.inputSummary_realizeBoundaryFromSummaries,
    design.outputSummary_realizeBoundaryFromSummaries,
    design.inputSummary_realizeBoundaryFromSummaries,
    design.outputSummary_realizeBoundaryFromSummaries]
  rw [design.addExposedInputs_comm, design.removeSinkOutputs_comm]

/-- Package a commutative preferred-layer design as the simpler local
implementation-data contract, provided the preferred auxiliary field is chosen
to agree with the derived concrete exposure operator. -/
def toImplementationData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (design : PreferredCommutativeBoundaryExposureDesign aux)
    (hspec : ∀ Y removed exposed,
      aux.exposeBoundaryUnderSinkDeletion Y removed exposed =
        design.concreteExposeBoundaryUnderSinkDeletion Y removed exposed) :
    PreferredBoundaryExposureImplementationData aux where
  refinedInterfaceAsInputBoundaryPort := design.refinedInterfaceAsInputBoundaryPort
  refinedInterfaceAsOutputBoundaryPort := design.refinedInterfaceAsOutputBoundaryPort
  concreteExposeBoundaryUnderSinkDeletion := design.concreteExposeBoundaryUnderSinkDeletion
  concreteExposeBoundaryUnderSinkDeletion_spec := hspec
  concreteExposeBoundaryUnderSinkDeletion_commutes :=
    design.concreteExposeBoundaryUnderSinkDeletion_commutes

end PreferredCommutativeBoundaryExposureDesign

open PreferredBoundaryExposureImplementationData

/-- A preferred-path witness that the commutative boundary-exposure design is
actually supplied and agrees with the current opaque preferred auxiliary field.
This is the local obligation surface for the next concrete instantiation step. -/
structure PreferredCommutativeBoundaryExposureDesignWitness
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) where
  /-- The commutative preferred boundary-exposure design. -/
  design : PreferredCommutativeBoundaryExposureDesign aux
  /-- The preferred auxiliary field agrees with the design-derived concrete
  exposure operator. -/
  exposeBoundaryUnderSinkDeletion_spec :
    ∀ Y removed exposed,
      aux.exposeBoundaryUnderSinkDeletion Y removed exposed =
        design.concreteExposeBoundaryUnderSinkDeletion Y removed exposed

namespace PreferredCommutativeBoundaryExposureDesignWitness

/-- Forget a preferred commutative design witness down to the simpler
implementation-data contract. -/
def toImplementationData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (witness : PreferredCommutativeBoundaryExposureDesignWitness aux) :
    PreferredBoundaryExposureImplementationData aux :=
  witness.design.toImplementationData witness.exposeBoundaryUnderSinkDeletion_spec

end PreferredCommutativeBoundaryExposureDesignWitness

namespace BoundaryCanonicalLinearization

/-- A canonical linearization contract yields the preferred commutative design:
summarize ordered boundary syntax into unordered content, update there, then
linearize back into ordered syntax. -/
def toPreferredCommutativeBoundaryExposureDesign
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (lin : BoundaryCanonicalLinearization aux) :
    PreferredCommutativeBoundaryExposureDesign aux where
  refinedInterfaceAsInputBoundaryPort := lin.refinedInterfaceAsInputBoundaryPort
  refinedInterfaceAsOutputBoundaryPort := lin.refinedInterfaceAsOutputBoundaryPort
  InputBoundarySummary :=
    ULift.{u+1, u} (Multiset (Σ s : Foundations.Sort_ D, Dc.sig.Var s))
  OutputBoundarySummary :=
    ULift.{u+1, u}
      (Multiset (Σ s : Foundations.Sort_ D, Foundations.Expr Dc.sig s))
  inputSummaryOfBoundary := fun Y => ULift.up (lin.summarizeInputBoundary Y)
  outputSummaryOfBoundary := fun Y => ULift.up (lin.summarizeOutputBoundary Y)
  exposedInputSummary := fun exposed =>
    ULift.up ↑(exposed.map lin.refinedInterfaceAsInputBoundaryPort)
  removedOutputSummary := fun removed =>
    ULift.up ↑(removed.map lin.refinedInterfaceAsOutputBoundaryPort)
  addExposedInputs := fun I A => ULift.up (I.down + A.down)
  removeSinkOutputs := fun O A => ULift.up (lin.removeSinkOutputs O.down A.down)
  realizeBoundaryFromSummaries := fun I O => lin.linearizeBoundary I.down O.down
  inputSummary_realizeBoundaryFromSummaries :=
    fun I O => by
      exact congrArg ULift.up (lin.summarizeInput_linearizeBoundary I.down O.down)
  outputSummary_realizeBoundaryFromSummaries :=
    fun I O => by
      exact congrArg ULift.up (lin.summarizeOutput_linearizeBoundary I.down O.down)
  addExposedInputs_comm := by
    intro I A B
    apply ULift.down_injective
    simpa [add_assoc, add_left_comm, add_comm]
  removeSinkOutputs_comm := by
    intro O A B
    apply ULift.down_injective
    exact lin.removeSinkOutputs_comm O.down A.down B.down

/-- If the existing preferred auxiliary field is instantiated by the exposure
operator induced from a canonical linearization contract, then that contract
immediately yields the desired preferred commutative-design witness. -/
def toPreferredCommutativeBoundaryExposureDesignWitness
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (lin : BoundaryCanonicalLinearization aux)
    (hspec :
      let design :=
        BoundaryCanonicalLinearization.toPreferredCommutativeBoundaryExposureDesign lin
      ∀ Y removed exposed,
        aux.exposeBoundaryUnderSinkDeletion Y removed exposed =
          design.concreteExposeBoundaryUnderSinkDeletion Y removed exposed) :
    PreferredCommutativeBoundaryExposureDesignWitness aux where
  design :=
    BoundaryCanonicalLinearization.toPreferredCommutativeBoundaryExposureDesign lin
  exposeBoundaryUnderSinkDeletion_spec := by
    simpa using hspec

end BoundaryCanonicalLinearization

namespace SignatureBoundaryCodeData

/-- The canonical boundary-code package already determines the preferred
exposure operator used by the preferred commutative design induced from its
canonical linearization. -/
theorem exposeBoundaryUnderSinkDeletion_agrees_with_preferredDesign
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (codes : SignatureBoundaryCodeData Dc aux) :
    ∀ Y removed exposed,
      aux.exposeBoundaryUnderSinkDeletion Y removed exposed =
        PreferredCommutativeBoundaryExposureDesign.concreteExposeBoundaryUnderSinkDeletion
          (BoundaryCanonicalLinearization.toPreferredCommutativeBoundaryExposureDesign
            (BoundaryCanonicalDisplay.toBoundaryCanonicalLinearization
              (BoundaryDisplayOrderData.toBoundaryCanonicalDisplay
                (BoundaryEntryCodeData.toBoundaryDisplayOrderData
                  (SignatureBoundaryCodeData.toBoundaryEntryCodeData codes)))))
          Y removed exposed := by
  intro Y removed exposed
  simpa [SignatureBoundaryCodeData.toBoundaryEntryCodeData,
    BoundaryEntryCodeData.toBoundaryDisplayOrderData,
    BoundaryDisplayOrderData.toBoundaryCanonicalDisplay,
    BoundaryCanonicalDisplay.toBoundaryCanonicalLinearization,
    BoundaryCanonicalLinearization.toPreferredCommutativeBoundaryExposureDesign,
    PreferredCommutativeBoundaryExposureDesign.concreteExposeBoundaryUnderSinkDeletion,
    sortBoundaryInputEntriesByCode,
    sortBoundaryOutputEntriesByCode] using
    codes.exposeBoundaryUnderSinkDeletion_canonical Y removed exposed

end SignatureBoundaryCodeData

/-- The named/free syntax linearization package induces the preferred
commutative boundary-exposure design on the preferred path. -/
def namedFreeSyntax_toPreferredCommutativeBoundaryExposureDesign
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    PreferredCommutativeBoundaryExposureDesign aux :=
  BoundaryCanonicalLinearization.toPreferredCommutativeBoundaryExposureDesign
    (namedFreeSyntax_toBoundaryCanonicalLinearization
      presentation boundaryCodes proofs)

/-- The named/free canonical linearization package yields the preferred
commutative boundary-exposure witness, using the agreement theorem already
recorded in the named/free proof package. -/
def namedFreeSyntax_toPreferredCommutativeBoundaryExposureDesignWitness
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    PreferredCommutativeBoundaryExposureDesignWitness aux :=
  BoundaryCanonicalLinearization.toPreferredCommutativeBoundaryExposureDesignWitness
    (namedFreeSyntax_toBoundaryCanonicalLinearization
      presentation boundaryCodes proofs)
    (by
      simpa [namedFreeSyntax_toPreferredCommutativeBoundaryExposureDesign,
        namedFreeSyntax_toBoundaryCanonicalLinearization,
        namedFreeSyntax_toBoundaryCanonicalDisplay,
        namedFreeSyntax_toBoundaryDisplayOrderData,
        namedFreeSyntax_toBoundaryEntryCodeData,
        namedFreeSyntax_toSignatureBoundaryCodeData,
        NamedFreeBoundaryAdapter.toSignatureBoundaryCodeData] using
        (SignatureBoundaryCodeData.exposeBoundaryUnderSinkDeletion_agrees_with_preferredDesign
          (namedFreeSyntax_toSignatureBoundaryCodeData
            presentation boundaryCodes proofs)))

/-- Manuscript-facing alias: named/free syntax yields the preferred
commutative boundary-exposure witness. -/
def theorem_named_free_syntax_gives_preferred_boundary_witness
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    PreferredCommutativeBoundaryExposureDesignWitness aux :=
  namedFreeSyntax_toPreferredCommutativeBoundaryExposureDesignWitness
    presentation boundaryCodes proofs

/-- The named/free syntax package proves the preferred exposure agreement
target from the canonical exposure law already carried by the boundary-code
package. -/
theorem namedFreeSyntax_preferredExposure_agrees
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    ∀ Y removed exposed,
      aux.exposeBoundaryUnderSinkDeletion Y removed exposed =
        PreferredCommutativeBoundaryExposureDesign.concreteExposeBoundaryUnderSinkDeletion
          (namedFreeSyntax_toPreferredCommutativeBoundaryExposureDesign
            presentation boundaryCodes proofs)
          Y removed exposed := by
  simpa [namedFreeSyntax_toPreferredCommutativeBoundaryExposureDesign,
    namedFreeSyntax_toBoundaryCanonicalLinearization,
    namedFreeSyntax_toBoundaryCanonicalDisplay,
    namedFreeSyntax_toBoundaryDisplayOrderData,
    namedFreeSyntax_toBoundaryEntryCodeData,
    namedFreeSyntax_toSignatureBoundaryCodeData,
    NamedFreeBoundaryAdapter.toSignatureBoundaryCodeData] using
    (SignatureBoundaryCodeData.exposeBoundaryUnderSinkDeletion_agrees_with_preferredDesign
      (namedFreeSyntax_toSignatureBoundaryCodeData
        presentation boundaryCodes proofs))

/-- Preferred bridge setup after specializing the boundary carrier to
`ULift (Foundations.BoundaryCirquent Dc.sig)`. -/
abbrev PreferredFoundationsBridgeSetup
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D) (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) :=
  FoundationsBridgeSetup Dc aux.toBridgeAuxiliaryData

/-- Preferred-path proof-relevant tensor reassembly data for a completed record
and a family of replayed tensor-component records.

This is the preferred auxiliary-data layer that sits strictly below the
internal holography bridge: it already knows the concrete preferred boundary
carrier, gluing-witness carrier, and admin-equivalence relation, but it does
not mention quotient-visible boundary values or internal holography interfaces.
-/
structure PreferredTensorReassemblyData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (R : CompletedReconstructionRecord (PreferredFoundationsBridgeSetup Dc aux))
    (componentReplay :
      Fin R.tensor.blocks.length →
        CompletedReconstructionRecord (PreferredFoundationsBridgeSetup Dc aux)) where
  tensorRecord : CompletedReconstructionRecord
    (PreferredFoundationsBridgeSetup Dc aux)
  componentEmbeddings :
    ∀ i : Fin R.tensor.blocks.length,
      Fin (componentReplay i).n → Fin tensorRecord.n
  recordEquiv_to_original : RecordStructEquiv
    (@BoundaryAdminEquiv (PreferredFoundationsBridgeSetup Dc aux))
    tensorRecord R

/-- Concrete preferred empty boundary object for the tensor lane: the empty
ordered boundary cirquent. -/
def preferredEmptyTensorBoundary
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D} :
    OrderedBoundaryProfileSource Dc :=
  boundaryCirquentOfOrderedBoundaryEntries (Dc := Dc) [] []

/-- Concrete preferred binary tensor boundary operation: concatenate the
ordered input/output boundary entries of the two component boundaries and
rebuild the resulting boundary cirquent. -/
def preferredTensorBoundary₂
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D} :
    OrderedBoundaryProfileSource Dc →
      OrderedBoundaryProfileSource Dc → OrderedBoundaryProfileSource Dc
  | Y₁, Y₂ =>
      boundaryCirquentOfOrderedBoundaryEntries (Dc := Dc)
        (orderedInputBoundaryEntries Y₁ ++ orderedInputBoundaryEntries Y₂)
        (orderedOutputBoundaryEntries Y₁ ++ orderedOutputBoundaryEntries Y₂)

/-- Preferred implementation data for the tensor lane once the concrete
boundary constructors are fixed on the specialized foundations bridge path.

This is the actual carrier-level seam left after making boundary tensoring
concrete: the gluing-witness monoidal structure and the proof slots that track
its intended semantics. The proof-relevant tensor reassembly constructor stays
separate and is supplied explicitly when building the full auxiliary record. -/
structure PreferredTensorBoundaryGluingImplementationData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D)
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) where
  emptyGluingWitness : aux.GluingWitness
  tensorGluingWitness₂ :
    aux.GluingWitness → aux.GluingWitness → aux.GluingWitness
  retagGluingWitness : Nat → aux.GluingWitness → aux.GluingWitness
  tensorBoundary_sound : Prop
  tensorGluingWitness_sound : Prop
  retagGluingWitness_sound : Prop
  visibleBoundary_tensor_sound : Prop
  adminEquiv_tensor_sound : Prop

/-- Preferred auxiliary extension adding the missing monoidal tensor operations
on boundary objects and gluing witnesses.

This is kept separate from `FoundationsBoundaryBridgeAuxiliaryData` so that the
existing preferred bridge users do not need to change. The extension carries:

- empty and binary tensor operations for preferred boundary objects;
- empty and binary tensor operations for preferred gluing witnesses;
- the current retagging operation for gluing witnesses;
- soundness slots recording the intended ordered-concatenation / disjoint-union
  semantics;
- the proof-relevant preferred tensor reassembly constructor. -/
structure FoundationsTensorBoundaryGluingAuxiliaryData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D)
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) where
  emptyBoundary : OrderedBoundaryProfileSource Dc
  tensorBoundary₂ :
    OrderedBoundaryProfileSource Dc →
      OrderedBoundaryProfileSource Dc → OrderedBoundaryProfileSource Dc
  emptyGluingWitness : aux.GluingWitness
  tensorGluingWitness₂ :
    aux.GluingWitness → aux.GluingWitness → aux.GluingWitness
  retagGluingWitness : Nat → aux.GluingWitness → aux.GluingWitness
  tensorBoundary_sound : Prop
  tensorGluingWitness_sound : Prop
  retagGluingWitness_sound : Prop
  visibleBoundary_tensor_sound : Prop
  adminEquiv_tensor_sound : Prop
  buildPreferredTensorReassembly :
    ∀ (R : CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup Dc aux))
        (_hCompleted : R.IsCompleted) (_hTensor : 1 < R.tensor.blocks.length)
        (componentReplay :
          Fin R.tensor.blocks.length →
            CompletedReconstructionRecord (PreferredFoundationsBridgeSetup Dc aux)),
      Nonempty (PreferredTensorReassemblyData aux R componentReplay)

/-- Build the full preferred tensor auxiliary record from the concrete
preferred boundary tensor constructors, the gluing-witness implementation
data, and the separate proof-relevant tensor reassembly constructor. -/
def preferredTensorBoundaryGluingAuxiliaryData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (impl : PreferredTensorBoundaryGluingImplementationData Dc aux)
    (buildPreferredTensorReassembly :
      ∀ (R : CompletedReconstructionRecord
            (PreferredFoundationsBridgeSetup Dc aux))
          (_hCompleted : R.IsCompleted) (_hTensor : 1 < R.tensor.blocks.length)
          (componentReplay :
            Fin R.tensor.blocks.length →
              CompletedReconstructionRecord (PreferredFoundationsBridgeSetup Dc aux)),
        Nonempty (PreferredTensorReassemblyData aux R componentReplay)) :
    FoundationsTensorBoundaryGluingAuxiliaryData Dc aux where
  emptyBoundary := preferredEmptyTensorBoundary (Dc := Dc)
  tensorBoundary₂ := preferredTensorBoundary₂ (Dc := Dc)
  emptyGluingWitness := impl.emptyGluingWitness
  tensorGluingWitness₂ := impl.tensorGluingWitness₂
  retagGluingWitness := impl.retagGluingWitness
  tensorBoundary_sound := impl.tensorBoundary_sound
  tensorGluingWitness_sound := impl.tensorGluingWitness_sound
  retagGluingWitness_sound := impl.retagGluingWitness_sound
  visibleBoundary_tensor_sound := impl.visibleBoundary_tensor_sound
  adminEquiv_tensor_sound := impl.adminEquiv_tensor_sound
  buildPreferredTensorReassembly := buildPreferredTensorReassembly

/-- Concrete preferred empty gluing witness for the tensor lane. -/
def concretePreferredEmptyGluingWitness
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D} :
    ConcretePreferredGluingWitness Dc where
  packetRetaggings := []
  boundarySummandRetaggings := []
  attachmentCompatibleValue := true
  gluedBoundary := preferredEmptyTensorBoundary (Dc := Dc)

/-- Concrete preferred binary tensor operation on gluing witnesses. The
metadata lists concatenate, compatibility booleans conjoin, proof slots conjoin,
and the proposed glued boundary tensors by ordered concatenation. -/
def concretePreferredTensorGluingWitness₂
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D} :
    ConcretePreferredGluingWitness Dc →
      ConcretePreferredGluingWitness Dc → ConcretePreferredGluingWitness Dc
  | w₁, w₂ =>
      { packetRetaggings := w₁.packetRetaggings ++ w₂.packetRetaggings
        boundarySummandRetaggings :=
          w₁.boundarySummandRetaggings ++ w₂.boundarySummandRetaggings
        attachmentCompatibleValue :=
          w₁.attachmentCompatibleValue && w₂.attachmentCompatibleValue
        gluedBoundary :=
          preferredTensorBoundary₂ (Dc := Dc) w₁.gluedBoundary w₂.gluedBoundary }

/-- Concrete preferred retagging operation on gluing witnesses. Retagging only
updates the ambient packet/summand indices; the proposed glued boundary and the
compatibility projections are preserved. -/
def concretePreferredRetagGluingWitness
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (offset : Nat) :
    ConcretePreferredGluingWitness Dc → ConcretePreferredGluingWitness Dc
  | w =>
      { packetRetaggings :=
          w.packetRetaggings.map
            (PreferredPacketReferenceRetagging.retag offset)
        boundarySummandRetaggings :=
          w.boundarySummandRetaggings.map
            (PreferredBoundarySummandRetagging.retag offset)
        attachmentCompatibleValue := w.attachmentCompatibleValue
        gluedBoundary := w.gluedBoundary }

/-- Empty witness in the universe-correct carrier used by the concrete
preferred auxiliary object. -/
def concretePreferredEmptyGluingWitnessCarrier
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D} :
    ConcretePreferredGluingWitnessCarrier Dc :=
  ULift.up (concretePreferredEmptyGluingWitness (Dc := Dc))

/-- Binary tensor on the universe-correct preferred witness carrier. -/
def concretePreferredTensorGluingWitness₂Carrier
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D} :
    ConcretePreferredGluingWitnessCarrier Dc →
      ConcretePreferredGluingWitnessCarrier Dc →
        ConcretePreferredGluingWitnessCarrier Dc
  | w₁, w₂ =>
      ULift.up
        (concretePreferredTensorGluingWitness₂ (Dc := Dc) w₁.down w₂.down)

/-- Retagging on the universe-correct preferred witness carrier. -/
def concretePreferredRetagGluingWitnessCarrier
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (offset : Nat) :
    ConcretePreferredGluingWitnessCarrier Dc →
      ConcretePreferredGluingWitnessCarrier Dc
  | w => ULift.up (concretePreferredRetagGluingWitness (D := D) (Dc := Dc) offset w.down)

/-- The preferred tensor boundary is concretely the ordered-boundary rebuild of
the concatenated input/output boundary entries. -/
theorem preferredTensorBoundary₂_spec
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D} :
    ∀ Y₁ Y₂,
      preferredTensorBoundary₂ (Dc := Dc) Y₁ Y₂ =
        boundaryCirquentOfOrderedBoundaryEntries (Dc := Dc)
          (orderedInputBoundaryEntries Y₁ ++ orderedInputBoundaryEntries Y₂)
          (orderedOutputBoundaryEntries Y₁ ++ orderedOutputBoundaryEntries Y₂) := by
  intro Y₁ Y₂
  rfl

/-- Tensoring concrete preferred gluing witnesses tensors their proposed glued
boundaries by the preferred ordered-concatenation constructor. -/
theorem concretePreferredTensorGluingWitness₂_boundary_sound
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D} :
    ∀ (w₁ w₂ : ConcretePreferredGluingWitness Dc),
      (concretePreferredTensorGluingWitness₂ (Dc := Dc) w₁ w₂).gluedBoundary =
        preferredTensorBoundary₂ (Dc := Dc) w₁.gluedBoundary w₂.gluedBoundary := by
  intro w₁ w₂
  rfl

/-- Retagging concrete preferred gluing witnesses preserves the proposed glued
boundary. -/
theorem concretePreferredRetagGluingWitness_boundary_sound
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D} :
    ∀ (offset : Nat) (w : ConcretePreferredGluingWitness Dc),
      (concretePreferredRetagGluingWitness (D := D) (Dc := Dc) offset w).gluedBoundary =
        w.gluedBoundary := by
  intro offset w
  rfl

/-- Retagging concrete preferred gluing witnesses preserves the projected
attachment-compatibility boolean. -/
theorem concretePreferredRetagGluingWitness_attachment_sound
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D} :
    ∀ (offset : Nat) (w : ConcretePreferredGluingWitness Dc),
      (concretePreferredRetagGluingWitness (D := D) (Dc := Dc) offset w).attachmentCompatibleValue =
        w.attachmentCompatibleValue := by
  intro offset w
  rfl

/-- The preferred tensor implementation package is now concretely inhabited on
the concrete preferred gluing-witness auxiliary object. -/
def concretePreferredTensorBoundaryGluingImplementationData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D)
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) :
    PreferredTensorBoundaryGluingImplementationData Dc
      (concretePreferredBoundaryBridgeAuxiliaryData aux) where
  emptyGluingWitness := concretePreferredEmptyGluingWitnessCarrier (Dc := Dc)
  tensorGluingWitness₂ := concretePreferredTensorGluingWitness₂Carrier (Dc := Dc)
  retagGluingWitness := concretePreferredRetagGluingWitnessCarrier (D := D) (Dc := Dc)
  tensorBoundary_sound :=
    ∀ Y₁ Y₂,
      preferredTensorBoundary₂ (Dc := Dc) Y₁ Y₂ =
        boundaryCirquentOfOrderedBoundaryEntries (Dc := Dc)
          (orderedInputBoundaryEntries Y₁ ++ orderedInputBoundaryEntries Y₂)
          (orderedOutputBoundaryEntries Y₁ ++ orderedOutputBoundaryEntries Y₂)
  tensorGluingWitness_sound :=
    ∀ (w₁ w₂ : ConcretePreferredGluingWitnessCarrier Dc),
      (concretePreferredTensorGluingWitness₂Carrier (Dc := Dc) w₁ w₂).down.gluedBoundary =
        preferredTensorBoundary₂ (Dc := Dc) w₁.down.gluedBoundary w₂.down.gluedBoundary
  retagGluingWitness_sound :=
    ∀ (offset : Nat) (w : ConcretePreferredGluingWitnessCarrier Dc),
      (concretePreferredRetagGluingWitnessCarrier (D := D) (Dc := Dc) offset w).down.gluedBoundary =
        w.down.gluedBoundary
  visibleBoundary_tensor_sound :=
    ∀ (w₁ w₂ : ConcretePreferredGluingWitnessCarrier Dc),
      (concretePreferredTensorGluingWitness₂Carrier (Dc := Dc) w₁ w₂).down.gluedBoundary =
        preferredTensorBoundary₂ (Dc := Dc) w₁.down.gluedBoundary w₂.down.gluedBoundary
  adminEquiv_tensor_sound :=
    ∀ (offset : Nat) (w : ConcretePreferredGluingWitnessCarrier Dc),
      (concretePreferredRetagGluingWitnessCarrier (D := D) (Dc := Dc) offset w).down.attachmentCompatibleValue =
        w.down.attachmentCompatibleValue

/-- Build the full preferred tensor auxiliary extension on the concrete
preferred gluing-witness auxiliary object once the separate proof-relevant
tensor reassembly constructor is supplied. -/
def concretePreferredTensorBoundaryGluingAuxiliaryData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (buildPreferredTensorReassembly :
      ∀ (R : CompletedReconstructionRecord
            (PreferredFoundationsBridgeSetup Dc
              (concretePreferredBoundaryBridgeAuxiliaryData aux)))
          (_hCompleted : R.IsCompleted) (_hTensor : 1 < R.tensor.blocks.length)
          (componentReplay :
            Fin R.tensor.blocks.length →
              CompletedReconstructionRecord
                (PreferredFoundationsBridgeSetup Dc
                  (concretePreferredBoundaryBridgeAuxiliaryData aux))),
        Nonempty
          (PreferredTensorReassemblyData
            (concretePreferredBoundaryBridgeAuxiliaryData aux) R componentReplay)) :
    FoundationsTensorBoundaryGluingAuxiliaryData Dc
      (concretePreferredBoundaryBridgeAuxiliaryData aux) :=
  preferredTensorBoundaryGluingAuxiliaryData
    (Dc := Dc)
    (impl := concretePreferredTensorBoundaryGluingImplementationData Dc aux)
    buildPreferredTensorReassembly

/-- Fold the preferred binary tensor boundary operation into the total list
operation required by `TensorBoundaryGluingStructure`. -/
def tensorBoundaryList
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (T : FoundationsTensorBoundaryGluingAuxiliaryData Dc aux) :
    List (OrderedBoundaryProfileSource Dc) → OrderedBoundaryProfileSource Dc :=
  List.foldr T.tensorBoundary₂ T.emptyBoundary

/-- Fold the preferred binary gluing-witness tensor operation into the total
list operation required by `TensorBoundaryGluingStructure`. -/
def tensorGluingWitnessList
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (T : FoundationsTensorBoundaryGluingAuxiliaryData Dc aux) :
    List aux.GluingWitness → aux.GluingWitness :=
  List.foldr T.tensorGluingWitness₂ T.emptyGluingWitness

/-- Preferred auxiliary-data package whose tensor boundary/gluing operations are
strong enough to build the proof-relevant tensor reassembly data from replayed
component records.

This is the exact constructive input still missing from the preferred
foundations bridge setup. Once instantiated, it feeds the existing tensor
constructor target without adding new holography-specific obligations. -/
structure PreferredFoundationsTensorBoundaryGluingData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    (Dc : Foundations.Doctrine D)
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) where
  base : TensorBoundaryGluingStructure
    (setup := PreferredFoundationsBridgeSetup Dc aux)
  buildPreferredTensorReassembly :
    ∀ (R : CompletedReconstructionRecord
          (PreferredFoundationsBridgeSetup Dc aux))
        (_hCompleted : R.IsCompleted) (_hTensor : 1 < R.tensor.blocks.length)
        (componentReplay :
          Fin R.tensor.blocks.length →
            CompletedReconstructionRecord (PreferredFoundationsBridgeSetup Dc aux)),
      Nonempty (PreferredTensorReassemblyData aux R componentReplay)

/-- The preferred tensor auxiliary extension fills the total list operations of
`TensorBoundaryGluingStructure` by folding its binary tensor operations. The
stronger preferred reassembly constructor is preserved unchanged. -/
def FoundationsTensorBoundaryGluingAuxiliaryData.toPreferredFoundationsTensorBoundaryGluingData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (T : FoundationsTensorBoundaryGluingAuxiliaryData Dc aux) :
    PreferredFoundationsTensorBoundaryGluingData Dc aux where
  base := {
    tensorBoundary := fun boundaries =>
      ULift.up (tensorBoundaryList T (boundaries.map ULift.down))
    retagGluingWitness := T.retagGluingWitness
    tensorGluingWitness := tensorGluingWitnessList T
    visibleBoundary_tensor := T.visibleBoundary_tensor_sound
    adminEquiv_tensorReassembly := T.adminEquiv_tensor_sound
    buildTensorReassembly := by
      intro R _ _
      exact ⟨R⟩
  }
  buildPreferredTensorReassembly := T.buildPreferredTensorReassembly

/-- Direct preferred tensor boundary/gluing package on the concrete preferred
owner path. This is the B1 tensor input expected downstream, instantiated from
the concrete preferred auxiliary data without an extra conversion step at the
call site. -/
def concretePreferredFoundationsTensorBoundaryGluingData
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (buildPreferredTensorReassembly :
      ∀ (R : CompletedReconstructionRecord
            (PreferredFoundationsBridgeSetup Dc
              (concretePreferredBoundaryBridgeAuxiliaryData aux)))
          (_hCompleted : R.IsCompleted) (_hTensor : 1 < R.tensor.blocks.length)
          (componentReplay :
            Fin R.tensor.blocks.length →
              CompletedReconstructionRecord
                (PreferredFoundationsBridgeSetup Dc
                  (concretePreferredBoundaryBridgeAuxiliaryData aux))),
        Nonempty
          (PreferredTensorReassemblyData
            (concretePreferredBoundaryBridgeAuxiliaryData aux) R componentReplay)) :
    PreferredFoundationsTensorBoundaryGluingData Dc
      (concretePreferredBoundaryBridgeAuxiliaryData aux) :=
  FoundationsTensorBoundaryGluingAuxiliaryData.toPreferredFoundationsTensorBoundaryGluingData
    (concretePreferredTensorBoundaryGluingAuxiliaryData aux buildPreferredTensorReassembly)

/-- The preferred refined-interface encoder on the specialized bridge path. -/
def preferredEncodeRefinedInterface
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) :
    (PreferredFoundationsBridgeSetup Dc aux).RefinedInterface →
      FoundationsBoundaryAtom Dc aux.toBridgeAuxiliaryData :=
  FoundationsBoundaryAtom.refinedInterface (Dc := Dc) (aux := aux.toBridgeAuxiliaryData)

/-- The preferred refined-interface encoder is injective. -/
theorem preferredEncodeRefinedInterface_injective
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) :
    Function.Injective aux.preferredEncodeRefinedInterface := by
  intro I₁ I₂ h
  cases h
  rfl

/-- Generator-level soundness target for the preferred `ULift.down` decoder:
every local two-step swap should preserve the concrete syntactic boundary code
obtained from the decoded foundations boundary cirquents. -/
def preferredDecoder_twoStepSwap_sound_target
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) : Prop :=
  ∀ {R : CompletedReconstructionRecord (PreferredFoundationsBridgeSetup Dc aux)}
    {s t : Fin R.n} {h : IndependentSinks R s t}
    {Y₁ Y₂ : (PreferredFoundationsBridgeSetup Dc aux).BoundaryObject},
    BoundaryTwoStepSwap h Y₁ Y₂ →
      SyntacticBoundaryEquiv
        (encodeBoundaryCandidateOfBoundaryCirquentDecoder
          Dc aux.toBridgeAuxiliaryData aux.preferredDecoder Y₁)
        (encodeBoundaryCandidateOfBoundaryCirquentDecoder
          Dc aux.toBridgeAuxiliaryData aux.preferredDecoder Y₂)

/-- Full soundness theorem for the preferred `ULift.down` decoder, assuming the
generator-level two-step swap soundness target. The closure constructors of
`BoundaryAdminEquiv` are already sufficient to lift this to the full relation. -/
theorem preferredDecoder_sound_of_twoStepSwap_sound
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (hgen : preferredDecoder_twoStepSwap_sound_target aux) :
    BoundarySoundTarget (setup := PreferredFoundationsBridgeSetup Dc aux)
      (encodeBoundaryCandidateOfBoundaryCirquentDecoder
        Dc aux.toBridgeAuxiliaryData aux.preferredDecoder) := by
  intro Y₁ Y₂ h
  induction h with
  | refl Y =>
      exact SyntacticBoundaryEquiv.refl _
  | symm h ih =>
      exact SyntacticBoundaryEquiv.symm ih
  | trans h₁ h₂ ih₁ ih₂ =>
      exact SyntacticBoundaryEquiv.trans ih₁ ih₂
  | ofTwoStepSwap hSwap =>
      exact hgen hSwap

/-- On the preferred path, the decoder/encoder combination reduces to the
direct foundations-boundary encoder. -/
@[simp] theorem preferredDecode_encodeBoundary_apply
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (Y : (PreferredFoundationsBridgeSetup Dc aux).BoundaryObject) :
    encodeBoundaryCandidateOfBoundaryCirquentDecoder
      Dc aux.toBridgeAuxiliaryData aux.preferredDecoder Y =
        encodeBoundaryCirquentCandidate Dc aux.toBridgeAuxiliaryData Y.down :=
  rfl

/-- Proof-relevant certificate that boundary reconstruction followed by
boundary encoding returns the original boundary syntax object. -/
structure BoundaryReconstructionCertificate
    {BoundarySyntax : Type _} {BoundaryRecord : Type _}
    (boundary : BoundarySyntax → BoundaryRecord)
    (reconstruct : BoundaryRecord → BoundarySyntax)
    (X : BoundarySyntax) where
  reconstructed : BoundarySyntax := reconstruct (boundary X)
  agrees : reconstructed = X

/-- Proof-relevant certificate that replaying a boundary record through the
reconstruction interface returns the original boundary record. -/
structure BoundaryReplayCertificate
    {BoundarySyntax : Type _} {BoundaryRecord : Type _}
    (boundary : BoundarySyntax → BoundaryRecord)
    (reconstruct : BoundaryRecord → BoundarySyntax)
    (b : BoundaryRecord) where
  replayedBoundary : BoundaryRecord := boundary (reconstruct b)
  agrees : replayedBoundary = b

/-- Smallest proof-relevant internal boundary equivalence interface that the
current preferred boundary lane can populate honestly: an actual boundary
carrier, an actual syntax carrier, conversion maps in both directions, and
proof-relevant unit/counit certificates. -/
structure BoundaryReconstructionInterface where
  BoundaryRecord : Type _
  BoundarySyntax : Type _
  boundary : BoundarySyntax → BoundaryRecord
  reconstruct : BoundaryRecord → BoundarySyntax
  reconstructionTrace :
    ∀ X, BoundaryReconstructionCertificate boundary reconstruct X
  boundaryReplay :
    ∀ b, BoundaryReplayCertificate boundary reconstruct b
  boundary_congr :
    ∀ {X₁ X₂ : BoundarySyntax}, X₁ = X₂ → boundary X₁ = boundary X₂
  reconstruct_congr :
    ∀ {b₁ b₂ : BoundaryRecord}, b₁ = b₂ → reconstruct b₁ = reconstruct b₂

/-- The preferred `ULift` boundary carrier and the preferred decoder already
form a proof-relevant boundary reconstruction interface: `ULift.up` gives the
boundary map, `ULift.down` gives the reconstruction map, and both unit/counit
certificates are definitional. -/
def preferredBoundaryReconstructionInterface
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) :
    BoundaryReconstructionInterface where
  BoundaryRecord := (PreferredFoundationsBridgeSetup Dc aux).BoundaryObject
  BoundarySyntax := OrderedBoundaryProfileSource Dc
  boundary := ULift.up
  reconstruct := aux.preferredDecoder
  reconstructionTrace := by
    intro X
    exact { agrees := rfl }
  boundaryReplay := by
    intro b
    cases b
    exact { agrees := rfl }
  boundary_congr := by
    intro X₁ X₂ h
    cases h
    rfl
  reconstruct_congr := by
    intro b₁ b₂ h
    cases h
    rfl

@[simp] theorem preferredBoundaryReconstructionInterface_reconstruct_boundary
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (X : OrderedBoundaryProfileSource Dc) :
    (preferredBoundaryReconstructionInterface aux).reconstruct
        ((preferredBoundaryReconstructionInterface aux).boundary X) =
      X :=
  ((preferredBoundaryReconstructionInterface aux).reconstructionTrace X).agrees

@[simp] theorem preferredBoundaryReconstructionInterface_boundary_reconstruct
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (b : (PreferredFoundationsBridgeSetup Dc aux).BoundaryObject) :
    (preferredBoundaryReconstructionInterface aux).boundary
        ((preferredBoundaryReconstructionInterface aux).reconstruct b) =
      b :=
  ((preferredBoundaryReconstructionInterface aux).boundaryReplay b).agrees

/-- Exact local boundary-exposure theorem needed to close the preferred-path
generator soundness target. Since `encodeBoundaryCirquentCandidate` produces a
singleton outer block, syntactic equivalence here is as strong as equality of
the encoded boundary block. The missing content is therefore entirely local to
how the preferred boundary exposure data behaves under one independent two-step
swap. -/
def theorem_preferred_local_two_step_boundary_exposure_encodes_equally
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) : Prop :=
  ∀ {R : CompletedReconstructionRecord (PreferredFoundationsBridgeSetup Dc aux)}
    {s t : Fin R.n} (h : IndependentSinks R s t),
    encodeBoundaryCirquentCandidate Dc aux.toBridgeAuxiliaryData
      ((peelSink (peelSink R s)
        (peelSinkOtherIdx s t (Ne.symm h.s_ne_t))).Y.down)
    =
    encodeBoundaryCirquentCandidate Dc aux.toBridgeAuxiliaryData
      ((peelSink (peelSink R t)
        (peelSinkOtherIdx t s h.s_ne_t)).Y.down)

/-- Exact commutation theorem needed to prove the preferred local two-step
boundary-exposure equality. After unfolding `peelSink` and `restrictedY`, the
two opposite two-step peel expressions differ only by the order in which
`aux.exposeBoundaryUnderSinkDeletion` is applied. Since the preferred encoder
is strict on ordered boundary profiles, equality is the right target here. -/
def exposeBoundaryUnderSinkDeletion_commutes_for_independent_sinks
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) : Prop :=
  ∀ {R : CompletedReconstructionRecord (PreferredFoundationsBridgeSetup Dc aux)}
    {s t : Fin R.n} (h : IndependentSinks R s t),
    ((peelSink (peelSink R s)
      (peelSinkOtherIdx s t (Ne.symm h.s_ne_t))).Y.down)
    =
    ((peelSink (peelSink R t)
      (peelSinkOtherIdx t s h.s_ne_t)).Y.down)

namespace PreferredBoundaryExposureImplementationData

/-- Supplying a concrete preferred-layer boundary exposure implementation
discharges the local commutation target for the existing opaque preferred
auxiliary field. -/
theorem discharges_boundaryExposure_commutes
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (impl : PreferredBoundaryExposureImplementationData aux) :
    exposeBoundaryUnderSinkDeletion_commutes_for_independent_sinks aux := by
  intro R s t h
  change
    aux.exposeBoundaryUnderSinkDeletion
      (aux.exposeBoundaryUnderSinkDeletion R.Y.down
        (R.ports.packetOut s) (R.ports.packetIn s))
      (R.ports.packetOut (embedSkip s (peelSinkOtherIdx s t (Ne.symm h.s_ne_t))))
      (R.ports.packetIn (embedSkip s (peelSinkOtherIdx s t (Ne.symm h.s_ne_t))))
    =
    aux.exposeBoundaryUnderSinkDeletion
      (aux.exposeBoundaryUnderSinkDeletion R.Y.down
        (R.ports.packetOut t) (R.ports.packetIn t))
      (R.ports.packetOut (embedSkip t (peelSinkOtherIdx t s h.s_ne_t)))
      (R.ports.packetIn (embedSkip t (peelSinkOtherIdx t s h.s_ne_t)))
  rw [embedSkip_peelSinkOtherIdx, embedSkip_peelSinkOtherIdx]
  rw [impl.concreteExposeBoundaryUnderSinkDeletion_spec,
    impl.concreteExposeBoundaryUnderSinkDeletion_spec,
    impl.concreteExposeBoundaryUnderSinkDeletion_spec,
    impl.concreteExposeBoundaryUnderSinkDeletion_spec]
  exact impl.concreteExposeBoundaryUnderSinkDeletion_commutes
    R.Y.down (R.ports.packetOut s) (R.ports.packetIn s)
    (R.ports.packetOut t) (R.ports.packetIn t)

end PreferredBoundaryExposureImplementationData

/-- The preferred local encoder-equality target follows immediately from the
boundary-exposure commutation theorem above. -/
theorem preferred_local_two_step_boundary_exposure_encodes_equally_of_commutes
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (hcomm : exposeBoundaryUnderSinkDeletion_commutes_for_independent_sinks aux) :
    theorem_preferred_local_two_step_boundary_exposure_encodes_equally aux := by
  intro R s t h
  exact congrArg (encodeBoundaryCirquentCandidate Dc aux.toBridgeAuxiliaryData) (hcomm h)

/-- The local preferred commutation target follows from a preferred
commutative-design witness. -/
theorem preferred_boundaryExposure_commutes_of_design_witness
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (witness : PreferredCommutativeBoundaryExposureDesignWitness aux) :
    exposeBoundaryUnderSinkDeletion_commutes_for_independent_sinks aux :=
  PreferredBoundaryExposureImplementationData.discharges_boundaryExposure_commutes
    witness.toImplementationData

/-- The preferred-path generator soundness target follows from the single local
boundary-exposure equality theorem above. No change to the generator relation
or to syntactic equivalence is needed. -/
theorem preferredDecoder_twoStepSwap_sound_of_local_boundary_exposure
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (hlocal : theorem_preferred_local_two_step_boundary_exposure_encodes_equally aux) :
    preferredDecoder_twoStepSwap_sound_target aux := by
  intro R s t h Y₁ Y₂ hSwap
  cases hSwap with
  | swap =>
      rw [preferredDecode_encodeBoundary_apply, preferredDecode_encodeBoundary_apply]
      rw [hlocal h]
      exact SyntacticBoundaryEquiv.refl _

/-- Preferred-path generator soundness follows directly from the local
foundations-bridge commutation target for `exposeBoundaryUnderSinkDeletion`. -/
theorem preferredDecoder_twoStepSwap_sound_of_boundaryExposure_commutes
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (hcomm : exposeBoundaryUnderSinkDeletion_commutes_for_independent_sinks aux) :
    preferredDecoder_twoStepSwap_sound_target aux :=
  preferredDecoder_twoStepSwap_sound_of_local_boundary_exposure aux
    (preferred_local_two_step_boundary_exposure_encodes_equally_of_commutes aux hcomm)

/-- Completeness target on the preferred `ULift` path. This is the precise
remaining theorem if syntactic equivalence of decoded boundary cirquents is to
characterize `BoundaryAdminEquiv`. -/
def preferredDecoder_complete_target
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) : Prop :=
  theorem_boundary_admin_equiv_complete_for_foundations_boundary_syntax
    Dc aux.toBridgeAuxiliaryData aux.preferredDecoder

/-- Strengthened preferred full boundary code on the `ULift` path. This records
the full typed ordered boundary entries, not only the boundary sort profiles. -/
def preferredFullBoundaryCode
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) :
    (PreferredFoundationsBridgeSetup Dc aux).BoundaryObject →
      SyntacticBoundaryObject (FoundationsBoundaryAtom Dc aux.toBridgeAuxiliaryData) :=
  encodeBoundaryCandidateOfBoundaryCirquentDecoder
    Dc aux.toBridgeAuxiliaryData aux.preferredDecoder

/-- Equality of the strengthened preferred full boundary code forces equality
of the underlying ordered boundary cirquents. -/
theorem preferredFullBoundaryCode_eq_implies_boundary_eq
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    {Y₁ Y₂ : (PreferredFoundationsBridgeSetup Dc aux).BoundaryObject} :
    preferredFullBoundaryCode aux Y₁ = preferredFullBoundaryCode aux Y₂ →
      Y₁ = Y₂ := by
  intro h
  apply ULift.down_injective
  exact encodeBoundaryCirquentCandidate_injective aux.toBridgeAuxiliaryData
    (by simpa [preferredFullBoundaryCode, preferredDecoder_apply] using h)

/-- Equality of the strengthened preferred full boundary code already yields
the preferred completeness conclusion: the decoded boundary objects are
administratively equivalent by reflexivity after full-entry extensionality
identifies them literally. -/
theorem preferredFullBoundaryCode_eq_implies_boundaryAdminEquiv
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    {Y₁ Y₂ : (PreferredFoundationsBridgeSetup Dc aux).BoundaryObject} :
    preferredFullBoundaryCode aux Y₁ = preferredFullBoundaryCode aux Y₂ →
      BoundaryAdminEquiv Y₁ Y₂ := by
  intro hcode
  have hY : Y₁ = Y₂ := preferredFullBoundaryCode_eq_implies_boundary_eq aux hcode
  subst hY
  exact BoundaryAdminEquiv.refl _

/-- Sharpened preferred completeness surface: on the preferred path the outer
syntactic boundary object is a singleton block, so completeness reduces to the
claim that equality of the strengthened preferred full boundary codes is
generated by local two-step swaps. -/
def preferred_boundary_code_eq_generated_by_local_two_step_swaps
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) : Prop :=
  ∀ {Y₁ Y₂ : (PreferredFoundationsBridgeSetup Dc aux).BoundaryObject},
    preferredFullBoundaryCode aux Y₁ = preferredFullBoundaryCode aux Y₂
    → BoundaryAdminEquiv Y₁ Y₂

/-- The strengthened preferred full boundary code is extensional enough to
discharge the preferred admin-generation target directly. -/
theorem preferred_boundary_code_eq_generated_by_local_two_step_swaps_of_fullCode
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) :
    preferred_boundary_code_eq_generated_by_local_two_step_swaps aux := by
  intro Y₁ Y₂ hcode
  exact preferredFullBoundaryCode_eq_implies_boundaryAdminEquiv aux hcode

/-- On the preferred path, equality of the encoded boundary codes already
implies the original completeness target, because `SyntacticBoundaryEquiv`
reduces to equality on singleton outer blocks. -/
theorem preferredDecoder_complete_of_boundary_code_eq_generated
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (hgen : preferred_boundary_code_eq_generated_by_local_two_step_swaps aux) :
    preferredDecoder_complete_target aux := by
  intro Y₁ Y₂ hEqv
  have hEq :
      encodeBoundaryCandidateOfBoundaryCirquentDecoder
          Dc aux.toBridgeAuxiliaryData aux.preferredDecoder Y₁
        =
        encodeBoundaryCandidateOfBoundaryCirquentDecoder
          Dc aux.toBridgeAuxiliaryData aux.preferredDecoder Y₂ := by
    have hPerm :
        List.Perm
          [encodeBoundaryCirquentBlock Dc aux.toBridgeAuxiliaryData Y₁.down]
          [encodeBoundaryCirquentBlock Dc aux.toBridgeAuxiliaryData Y₂.down] := by
      change List.Perm
        [encodeBoundaryCirquentBlock Dc aux.toBridgeAuxiliaryData Y₁.down]
        [encodeBoundaryCirquentBlock Dc aux.toBridgeAuxiliaryData Y₂.down] at hEqv
      exact hEqv
    have hEqList :
        [encodeBoundaryCirquentBlock Dc aux.toBridgeAuxiliaryData Y₁.down]
          =
        [encodeBoundaryCirquentBlock Dc aux.toBridgeAuxiliaryData Y₂.down] := by
      exact List.perm_singleton.mp hPerm
    simpa using hEqList
  exact hgen hEq

/-- The preferred decoder completeness target is already discharged on the
owner path by extensionality of the strengthened full boundary code. -/
theorem preferredDecoder_complete
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) :
    preferredDecoder_complete_target aux :=
  preferredDecoder_complete_of_boundary_code_eq_generated aux
    (preferred_boundary_code_eq_generated_by_local_two_step_swaps_of_fullCode aux)

/-- Exact missing theorem on the preferred path when completeness is not yet
available: every syntactic equivalence between decoded boundary cirquents must
be generated by local two-step swaps and the closure rules of
`BoundaryAdminEquiv`. -/
def theorem_preferred_boundary_syntactic_equiv_generated_by_local_two_step_swaps
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) : Prop :=
  preferredDecoder_complete_target aux

/-- Manuscript-facing sharpened preferred completeness target: equality of the
preferred singleton-block boundary codes is generated by local two-step swaps. -/
def preferred_boundary_code_eq_generated_by_local_two_step_swaps_target
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc) : Prop :=
  preferred_boundary_code_eq_generated_by_local_two_step_swaps aux

/-- Package the preferred `ULift.down` path as a `BoundaryObjectDecoder` once
the local-swap soundness theorem and the completeness theorem are supplied. -/
def preferredBoundaryObjectDecoder
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (hsound : preferredDecoder_twoStepSwap_sound_target aux)
    (hcomplete : preferredDecoder_complete_target aux) :
    BoundaryObjectDecoder Dc aux.toBridgeAuxiliaryData where
  decodeBoundary := aux.preferredDecoder
  decode_sound := preferredDecoder_sound_of_twoStepSwap_sound aux hsound
  decode_complete := hcomplete

/-- Package the preferred `ULift.down` path as a `BoundaryObjectDecoder`
directly from the local foundations-bridge commutation target and the existing
completeness target. -/
def preferredBoundaryObjectDecoder_of_boundaryExposure_commutes
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (hcomm : exposeBoundaryUnderSinkDeletion_commutes_for_independent_sinks aux)
    (hcomplete : preferredDecoder_complete_target aux) :
    BoundaryObjectDecoder Dc aux.toBridgeAuxiliaryData where
  decodeBoundary := aux.preferredDecoder
  decode_sound :=
    preferredDecoder_sound_of_twoStepSwap_sound aux
      (preferredDecoder_twoStepSwap_sound_of_boundaryExposure_commutes aux hcomm)
  decode_complete := hcomplete

/-- Package the preferred decoder directly from soundness, with completeness
discharged by the owner-path full-code argument. -/
def preferredBoundaryObjectDecoder_of_fullCode
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (hsound : preferredDecoder_twoStepSwap_sound_target aux) :
    BoundaryObjectDecoder Dc aux.toBridgeAuxiliaryData :=
  preferredBoundaryObjectDecoder aux hsound (preferredDecoder_complete aux)

/-- Package the preferred decoder directly from the preferred commutative
design witness, with no externally supplied completeness theorem. -/
def preferredBoundaryObjectDecoder_of_design_witness
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (witness : PreferredCommutativeBoundaryExposureDesignWitness aux) :
    BoundaryObjectDecoder Dc aux.toBridgeAuxiliaryData :=
  preferredBoundaryObjectDecoder_of_fullCode aux
    (preferredDecoder_twoStepSwap_sound_of_boundaryExposure_commutes aux
      (preferred_boundaryExposure_commutes_of_design_witness witness))

/-- Boundary presentation for the preferred specialized bridge setup, once the
decoder-level soundness/completeness obligations are supplied. -/
def preferredSyntacticBoundaryPresentation
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (hsound : preferredDecoder_twoStepSwap_sound_target aux)
    (hcomplete : preferredDecoder_complete_target aux) :
    SyntacticBoundaryPresentation (PreferredFoundationsBridgeSetup Dc aux) where
  Atom := FoundationsBoundaryAtom Dc aux.toBridgeAuxiliaryData
  encodeBoundary := encodeBoundaryCandidateOfBoundaryCirquentDecoder
    Dc aux.toBridgeAuxiliaryData aux.preferredDecoder
  encodeRefinedInterface := aux.preferredEncodeRefinedInterface
  boundary_sound := (preferredBoundaryObjectDecoder aux hsound hcomplete).decode_sound
  boundary_complete := (preferredBoundaryObjectDecoder aux hsound hcomplete).decode_complete
  externalOut_sound := by
    intro L₁ L₂ h
    simpa using h.map aux.preferredEncodeRefinedInterface
  externalOut_complete := by
    intro L₁ L₂ h
    exact externalOut_complete_of_injective
      (setup := PreferredFoundationsBridgeSetup Dc aux)
      aux.preferredEncodeRefinedInterface
      (preferredEncodeRefinedInterface_injective aux)
      h

/-- Boundary presentation for the preferred specialized bridge setup, once the
local foundations-bridge commutation theorem and the completeness theorem are
supplied. -/
def preferredSyntacticBoundaryPresentation_of_boundaryExposure_commutes
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (hcomm : exposeBoundaryUnderSinkDeletion_commutes_for_independent_sinks aux)
    (hcomplete : preferredDecoder_complete_target aux) :
    SyntacticBoundaryPresentation (PreferredFoundationsBridgeSetup Dc aux) :=
  preferredSyntacticBoundaryPresentation aux
    (preferredDecoder_twoStepSwap_sound_of_boundaryExposure_commutes aux hcomm)
    hcomplete

/-- Preferred boundary presentation from decoder soundness alone, with
completeness discharged by the owner-path full-code argument. -/
def preferredSyntacticBoundaryPresentation_of_fullCode
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (hsound : preferredDecoder_twoStepSwap_sound_target aux) :
    SyntacticBoundaryPresentation (PreferredFoundationsBridgeSetup Dc aux) :=
  preferredSyntacticBoundaryPresentation aux hsound (preferredDecoder_complete aux)

/-- Preferred boundary presentation packaged directly from the preferred
commutative design witness, with no externally supplied completeness theorem. -/
def preferredSyntacticBoundaryPresentation_of_design_witness
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (witness : PreferredCommutativeBoundaryExposureDesignWitness aux) :
    SyntacticBoundaryPresentation (PreferredFoundationsBridgeSetup Dc aux) :=
  preferredSyntacticBoundaryPresentation_of_fullCode aux
    (preferredDecoder_twoStepSwap_sound_of_boundaryExposure_commutes aux
      (preferred_boundaryExposure_commutes_of_design_witness witness))

/-- Preferred frontier quotient realization packaged directly from the
preferred commutative design witness, with no externally supplied completeness
theorem. -/
def preferred_frontier_quotient_realization_of_design_witness
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (witness : PreferredCommutativeBoundaryExposureDesignWitness aux) :
    FrontierQuotientRealization (PreferredFoundationsBridgeSetup Dc aux) :=
  syntactic_boundary_presentation_gives_frontier_quotient_realization
    (preferredSyntacticBoundaryPresentation_of_design_witness aux witness)

namespace PreferredCommutativeBoundaryExposureDesignWitness

/-- Generator-level preferred decoder soundness follows from a preferred
commutative boundary-exposure design witness. -/
theorem preferredDecoder_twoStepSwap_sound
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (witness : PreferredCommutativeBoundaryExposureDesignWitness aux) :
    preferredDecoder_twoStepSwap_sound_target aux :=
  preferredDecoder_twoStepSwap_sound_of_boundaryExposure_commutes aux
    (preferred_boundaryExposure_commutes_of_design_witness witness)

/-- Full preferred decoder soundness follows from a preferred commutative
boundary-exposure design witness. -/
theorem preferredDecoder_sound
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    {aux : FoundationsBoundaryBridgeAuxiliaryData Dc}
    (witness : PreferredCommutativeBoundaryExposureDesignWitness aux) :
    BoundarySoundTarget (setup := PreferredFoundationsBridgeSetup Dc aux)
      (encodeBoundaryCandidateOfBoundaryCirquentDecoder
        Dc aux.toBridgeAuxiliaryData aux.preferredDecoder) :=
  preferredDecoder_sound_of_twoStepSwap_sound aux
    (preferredDecoder_twoStepSwap_sound witness)

end PreferredCommutativeBoundaryExposureDesignWitness

open PreferredCommutativeBoundaryExposureDesignWitness

/-- Preferred boundary presentation packaged directly from the local
commutative design witness and the sharpened preferred completeness target. -/
def preferred_boundary_presentation_theorem
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (witness : PreferredCommutativeBoundaryExposureDesignWitness aux)
    (hcomplete : preferred_boundary_code_eq_generated_by_local_two_step_swaps aux) :
    SyntacticBoundaryPresentation (PreferredFoundationsBridgeSetup Dc aux) :=
  preferredSyntacticBoundaryPresentation aux
    (preferredDecoder_twoStepSwap_sound witness)
    (preferredDecoder_complete_of_boundary_code_eq_generated aux hcomplete)

/-- The preferred local sink-deletion commutation target holds on the named/free
syntax route via the concrete preferred design witness. -/
theorem theorem_named_free_syntax_gives_boundaryExposure_commutes
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    exposeBoundaryUnderSinkDeletion_commutes_for_independent_sinks
      (concretePreferredBoundaryBridgeAuxiliaryData aux) :=
  preferred_boundaryExposure_commutes_of_design_witness
    (namedFreeSyntax_toPreferredCommutativeBoundaryExposureDesignWitness
      presentation boundaryCodes.toConcretePreferredAuxiliaryData proofs)

/-- Preferred decoder completeness on the concrete preferred owner path. -/
theorem theorem_named_free_syntax_gives_preferredDecoder_complete
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    preferredDecoder_complete_target (concretePreferredBoundaryBridgeAuxiliaryData aux) :=
  preferredDecoder_complete (concretePreferredBoundaryBridgeAuxiliaryData aux)

/-- Preferred boundary decoder on the concrete preferred owner path. -/
def theorem_named_free_syntax_gives_preferredBoundaryObjectDecoder
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    BoundaryObjectDecoder presentation.toDoctrine
      (concretePreferredBoundaryBridgeAuxiliaryData aux).toBridgeAuxiliaryData :=
  preferredBoundaryObjectDecoder_of_design_witness
    (concretePreferredBoundaryBridgeAuxiliaryData aux)
    (namedFreeSyntax_toPreferredCommutativeBoundaryExposureDesignWitness
      presentation boundaryCodes.toConcretePreferredAuxiliaryData proofs)

/-- Preferred boundary presentation on the concrete preferred owner path,
packaged without an externally threaded completeness theorem. -/
def theorem_named_free_syntax_gives_preferredBoundaryPresentation
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    SyntacticBoundaryPresentation
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux)) :=
  preferredSyntacticBoundaryPresentation_of_design_witness
    (concretePreferredBoundaryBridgeAuxiliaryData aux)
    (namedFreeSyntax_toPreferredCommutativeBoundaryExposureDesignWitness
      presentation boundaryCodes.toConcretePreferredAuxiliaryData proofs)

/-- Preferred frontier quotient realization on the concrete preferred owner
path, packaged without an externally threaded completeness theorem. -/
def theorem_named_free_syntax_gives_preferredFrontierQuotientRealization
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    FrontierQuotientRealization
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux)) :=
  preferred_frontier_quotient_realization_of_design_witness
    (concretePreferredBoundaryBridgeAuxiliaryData aux)
    (namedFreeSyntax_toPreferredCommutativeBoundaryExposureDesignWitness
      presentation boundaryCodes.toConcretePreferredAuxiliaryData proofs)

/-- Preferred residue holography on the concrete preferred owner path,
packaged without an externally threaded completeness theorem. -/
theorem theorem_named_free_syntax_gives_preferredResidueHolographicReconstruction
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (H : HolographicReconstructionData
      (PreferredFoundationsBridgeSetup presentation.toDoctrine
        (concretePreferredBoundaryBridgeAuxiliaryData aux)))
    {R₁ R₂ :
      CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine
          (concretePreferredBoundaryBridgeAuxiliaryData aux))} :
    (theorem_named_free_syntax_gives_preferredFrontierQuotientRealization
        presentation boundaryCodes proofs).realize
        (H.toFrontierWord R₁)
      =
      (theorem_named_free_syntax_gives_preferredFrontierQuotientRealization
        presentation boundaryCodes proofs).realize
        (H.toFrontierWord R₂)
      ↔ FrontierWord.Equiv (H.toFrontierWord R₁) (H.toFrontierWord R₂) :=
    by
      simpa [theorem_named_free_syntax_gives_preferredFrontierQuotientRealization] using
        (syntactic_boundary_holographic_reconstruction
          (theorem_named_free_syntax_gives_preferredBoundaryPresentation
            presentation boundaryCodes proofs)
          H)

/-- Manuscript-facing alias: once the sharpened preferred completeness target
is supplied, the named/free syntax path gives the preferred boundary
presentation package. -/
def theorem_named_free_syntax_gives_boundary_presentation
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (hcomplete : preferred_boundary_code_eq_generated_by_local_two_step_swaps aux) :
    SyntacticBoundaryPresentation
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux) :=
  preferred_boundary_presentation_theorem aux
    (namedFreeSyntax_toPreferredCommutativeBoundaryExposureDesignWitness
      presentation boundaryCodes proofs)
    hcomplete

/-- Manuscript-facing alias: once the sharpened preferred completeness target
is supplied, the named/free syntax path yields frontier quotient realization on
the preferred bridge setup. -/
def theorem_named_free_syntax_gives_frontier_quotient_realization
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (hcomplete : preferred_boundary_code_eq_generated_by_local_two_step_swaps aux) :
    FrontierQuotientRealization
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux) :=
  syntactic_boundary_presentation_gives_frontier_quotient_realization
    (theorem_named_free_syntax_gives_boundary_presentation
      presentation boundaryCodes proofs hcomplete)

/-- Preferred frontier quotient realization, once the preferred commutative
design witness and the sharpened preferred completeness theorem are supplied. -/
def preferred_frontier_quotient_realization
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (witness : PreferredCommutativeBoundaryExposureDesignWitness aux)
    (hcomplete : preferred_boundary_code_eq_generated_by_local_two_step_swaps aux) :
    FrontierQuotientRealization (PreferredFoundationsBridgeSetup Dc aux) :=
  syntactic_boundary_presentation_gives_frontier_quotient_realization
    (preferred_boundary_presentation_theorem aux witness hcomplete)

/-- Preferred residue-level holographic reconstruction, once the preferred
commutative design witness and the sharpened preferred completeness theorem are
supplied. This packages the existing holography theorem on the preferred path
without weakening the theorem into an external hypothesis on the manuscript
side; the remaining inputs are still internal Lean targets. -/
theorem preferred_residue_holographic_reconstruction
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (witness : PreferredCommutativeBoundaryExposureDesignWitness aux)
    (hcomplete : preferred_boundary_code_eq_generated_by_local_two_step_swaps aux)
    (H : HolographicReconstructionData (PreferredFoundationsBridgeSetup Dc aux))
    {R₁ R₂ : CompletedReconstructionRecord (PreferredFoundationsBridgeSetup Dc aux)} :
    (syntactic_boundary_presentation_gives_holographic_quotient_realization
        (preferred_boundary_presentation_theorem aux witness hcomplete)).realize
        (H.toFrontierWord R₁)
      =
      (syntactic_boundary_presentation_gives_holographic_quotient_realization
        (preferred_boundary_presentation_theorem aux witness hcomplete)).realize
        (H.toFrontierWord R₂)
      ↔ FrontierWord.Equiv (H.toFrontierWord R₁) (H.toFrontierWord R₂) :=
  syntactic_boundary_holographic_reconstruction
    (preferred_boundary_presentation_theorem aux witness hcomplete) H

/-- Manuscript-facing alias: once the strengthened preferred completeness
target is supplied, the named/free syntax path yields the preferred
residue-level holographic reconstruction package. This is the Layer B-side
precursor to any later Layer D source-trace packaging. -/
theorem theorem_named_free_syntax_gives_residue_holographic_reconstruction
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (hcomplete : preferred_boundary_code_eq_generated_by_local_two_step_swaps aux)
    (H : HolographicReconstructionData
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux))
    {R₁ R₂ :
      CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)} :
    (syntactic_boundary_presentation_gives_holographic_quotient_realization
        (theorem_named_free_syntax_gives_boundary_presentation
          presentation boundaryCodes proofs hcomplete)).realize
        (H.toFrontierWord R₁)
      =
      (syntactic_boundary_presentation_gives_holographic_quotient_realization
        (theorem_named_free_syntax_gives_boundary_presentation
          presentation boundaryCodes proofs hcomplete)).realize
        (H.toFrontierWord R₂)
      ↔ FrontierWord.Equiv (H.toFrontierWord R₁) (H.toFrontierWord R₂) :=
  preferred_residue_holographic_reconstruction aux
    (namedFreeSyntax_toPreferredCommutativeBoundaryExposureDesignWitness
      presentation boundaryCodes proofs)
    hcomplete H

/-- Layer B export precursor for the named/free source-side theorem package.
This bundles the derived code/display objects, preferred witness, preferred
boundary presentation, frontier quotient realization, and residue holography
theorem without importing Layer D. -/
structure NamedFreeSourceHolographyPackage
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine) where
  boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux
  boundaryEntryCodeData : BoundaryEntryCodeData aux
  boundaryCanonicalDisplay : BoundaryCanonicalDisplay aux
  boundaryCanonicalLinearization : BoundaryCanonicalLinearization aux
  preferredBoundaryWitness : PreferredCommutativeBoundaryExposureDesignWitness aux
  holographyData :
    HolographicReconstructionData
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)
  boundaryPresentation :
    SyntacticBoundaryPresentation
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)
  frontierQuotientRealization :
    FrontierQuotientRealization
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)
  residueHolography :
    ∀ {R₁ R₂ :
      CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)},
      (syntactic_boundary_presentation_gives_holographic_quotient_realization
          boundaryPresentation).realize
          (holographyData.toFrontierWord R₁)
        =
        (syntactic_boundary_presentation_gives_holographic_quotient_realization
          boundaryPresentation).realize
          (holographyData.toFrontierWord R₂)
        ↔ FrontierWord.Equiv
            (holographyData.toFrontierWord R₁)
            (holographyData.toFrontierWord R₂)

/-- Build the bundled Layer B named/free source-side export precursor from the
current real inputs: named/free boundary codes and proofs, the strengthened
full-entry completeness theorem, and the holography data used on the preferred
path. -/
def namedFreeSyntax_toSourceHolographyPackage
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (hcomplete : preferred_boundary_code_eq_generated_by_local_two_step_swaps aux)
    (H : HolographicReconstructionData
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)) :
    NamedFreeSourceHolographyPackage presentation aux where
  boundaryCodes := boundaryCodes
  boundaryEntryCodeData :=
    namedFreeSyntax_toBoundaryEntryCodeData presentation boundaryCodes proofs
  boundaryCanonicalDisplay :=
    namedFreeSyntax_toBoundaryCanonicalDisplay presentation boundaryCodes proofs
  boundaryCanonicalLinearization :=
    namedFreeSyntax_toBoundaryCanonicalLinearization presentation boundaryCodes proofs
  preferredBoundaryWitness :=
    namedFreeSyntax_toPreferredCommutativeBoundaryExposureDesignWitness
      presentation boundaryCodes proofs
  holographyData := H
  boundaryPresentation :=
    theorem_named_free_syntax_gives_boundary_presentation
      presentation boundaryCodes proofs hcomplete
  frontierQuotientRealization :=
    theorem_named_free_syntax_gives_frontier_quotient_realization
      presentation boundaryCodes proofs hcomplete
  residueHolography := by
    intro R₁ R₂
    simpa using
      (theorem_named_free_syntax_gives_residue_holographic_reconstruction
        presentation boundaryCodes proofs hcomplete H (R₁ := R₁) (R₂ := R₂))

/-- Concrete-aux named/free source-side package. The boundary-facing package is
rebuilt directly for the concrete preferred auxiliary object by transporting the
boundary-code data fieldwise and using the identity holographic reconstruction
data on the concrete completed-record setup. -/
def namedFreeSyntax_toConcretePreferredSourceHolographyPackage
    {primitive : NamedPrimitiveInterfacePresentation}
    (presentation : NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (boundaryCodes : SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs : NamedFreeBoundaryAdapter.BoundaryProofs presentation) :
    NamedFreeSourceHolographyPackage presentation
      (concretePreferredBoundaryBridgeAuxiliaryData aux) :=
  namedFreeSyntax_toSourceHolographyPackage
    presentation
    (aux := concretePreferredBoundaryBridgeAuxiliaryData aux)
    (boundaryCodes := boundaryCodes.toConcretePreferredAuxiliaryData)
    proofs
    (preferred_boundary_code_eq_generated_by_local_two_step_swaps_of_fullCode
      (concretePreferredBoundaryBridgeAuxiliaryData aux))
    HolographicReconstructionData.identity

/-- Project the preferred boundary presentation from the bundled named/free
Layer B source-side export precursor. -/
def package_gives_boundary_presentation
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (pkg : NamedFreeSourceHolographyPackage presentation aux) :
    SyntacticBoundaryPresentation
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux) :=
  pkg.boundaryPresentation

/-- Project the preferred frontier quotient realization from the bundled
named/free Layer B source-side export precursor. -/
def package_gives_frontier_quotient_realization
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (pkg : NamedFreeSourceHolographyPackage presentation aux) :
    FrontierQuotientRealization
      (PreferredFoundationsBridgeSetup presentation.toDoctrine aux) :=
  pkg.frontierQuotientRealization

/-- Project the preferred residue-level holography theorem from the bundled
named/free Layer B source-side export precursor. -/
theorem package_gives_residue_holography
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (pkg : NamedFreeSourceHolographyPackage presentation aux)
    {R₁ R₂ :
      CompletedReconstructionRecord
        (PreferredFoundationsBridgeSetup presentation.toDoctrine aux)} :
    (syntactic_boundary_presentation_gives_holographic_quotient_realization
        pkg.boundaryPresentation).realize
        (pkg.holographyData.toFrontierWord R₁)
      =
      (syntactic_boundary_presentation_gives_holographic_quotient_realization
        pkg.boundaryPresentation).realize
        (pkg.holographyData.toFrontierWord R₂)
      ↔ FrontierWord.Equiv
          (pkg.holographyData.toFrontierWord R₁)
          (pkg.holographyData.toFrontierWord R₂) :=
  pkg.residueHolography

/-- Preferred bridge path packaged all the way to the existing Path B theorem
interface. -/
def theorem_preferred_bridge_boundary_presentation
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (hsound : preferredDecoder_twoStepSwap_sound_target aux)
    (hcomplete : preferredDecoder_complete_target aux) :
    SyntacticBoundaryPresentation (PreferredFoundationsBridgeSetup Dc aux) :=
  preferredSyntacticBoundaryPresentation aux hsound hcomplete

/-- Once the preferred-path decoder obligations are supplied, the existing Path
B scaffold yields faithful frontier quotient realization for the preferred
bridge setup. -/
def theorem_preferred_bridge_boundary_presentation_gives_frontier_quotient_realization
    {D : Foundations.PrimitiveInterfaceData.{u}}
    {Dc : Foundations.Doctrine D}
    (aux : FoundationsBoundaryBridgeAuxiliaryData Dc)
    (hsound : preferredDecoder_twoStepSwap_sound_target aux)
    (hcomplete : preferredDecoder_complete_target aux) :
    FrontierQuotientRealization (PreferredFoundationsBridgeSetup Dc aux) :=
  syntactic_boundary_presentation_gives_frontier_quotient_realization
    (preferredSyntacticBoundaryPresentation aux hsound hcomplete)

end FoundationsBoundaryBridgeAuxiliaryData

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc