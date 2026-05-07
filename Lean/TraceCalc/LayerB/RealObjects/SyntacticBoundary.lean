import TraceCalc.LayerB.RealObjects.BoundaryCode
import Mathlib.Data.Multiset.Basic

/-!
# Real-objects formalization: syntactic boundary presentation (Path B)

**Phase 9 Path B (2026-04-24).** The generic residue-level reduction is
already complete: faithful frontier quotient realization follows from the two
boundary obligations `BoundaryAdminCodeContract` and
`ExternalOutCodeContract`. This file develops the **constructive syntactic
route** requested by the user: rather than enriching the generic opaque setup,
introduce a separate syntactic boundary presentation and show that such a
presentation yields the required boundary code contracts, hence the full
frontier quotient realization.

## Scope discipline

* `RewriteCalculusSetup` is **not** mutated.
* The current opaque `setup.BoundaryObject` and `setup.RefinedInterface` are
  **not** assumed canonicalizable.
* A new **syntactic** boundary object is defined first, independently of the
  generic setup.
* The bridge back to the generic theorem is through a presentation theorem:

  syntactic boundary presentation
  ⇒ boundary code contracts
  ⇒ faithful frontier quotient realization.

## Items in this file

* **B1** — syntactic boundary atoms, blocks, and objects.
* **B2** — syntactic boundary and external-output equivalences.
* **B3** — a generic `PermCodeContract` and a concrete `Multiset`-based
  instance, using the exact quotient `List α / List.Perm`.
* **B4** — syntactic boundary and external-output code contracts.
* **B5** — `SyntacticBoundaryPresentation setup`, plus bridge theorems from a
  presentation to `BoundaryAdminCodeContract` and `ExternalOutCodeContract`.
* **B6** — full frontier quotient realization from a syntactic presentation.
* **B7** — manuscript-facing aliases.

## Manuscript point

This isolates the remaining mathematical burden in the constructive form the
user asked for:

  show the intended boundary objects admit a syntactic presentation.

Once that theorem is supplied, the boundary code contracts and faithful
frontier quotient realization are automatic.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

variable {setup : RewriteCalculusSetup.{u}}

/-! ## B1 — Syntactic boundary atoms and objects -/

/-- A syntactic boundary block is a finite list of atoms. Inner order is kept
strict in this first constructive model. -/
abbrev BoundaryBlock (Atom : Type u) := List Atom

/-- A syntactic boundary object is a finite list of boundary blocks. The outer
list is the administratively swappable layer. -/
abbrev SyntacticBoundaryObject (Atom : Type u) := List (BoundaryBlock Atom)

/-- In the syntactic presentation, refined interfaces are represented directly
by atoms. -/
abbrev SyntacticRefinedInterface (Atom : Type u) := Atom

/-! ## B2 — Syntactic boundary equivalence -/

/-- Boundary-block equivalence. In this initial constructive model, inner block
order is kept strict, so this is just equality. -/
def BoundaryBlockEquiv {Atom : Type u} (b₁ b₂ : BoundaryBlock Atom) : Prop :=
  b₁ = b₂

/-- Syntactic administrative equivalence on boundary objects: outer blocks may
permute, but each block's internal order stays strict. -/
def SyntacticBoundaryEquiv {Atom : Type u}
    (Y₁ Y₂ : SyntacticBoundaryObject Atom) : Prop :=
  List.Perm Y₁ Y₂

namespace SyntacticBoundaryEquiv

/-- Reflexivity of syntactic administrative equivalence. -/
theorem refl {Atom : Type u} (Y : SyntacticBoundaryObject Atom) :
    SyntacticBoundaryEquiv Y Y :=
  List.Perm.refl _

/-- Symmetry of syntactic administrative equivalence. -/
theorem symm {Atom : Type u} {Y₁ Y₂ : SyntacticBoundaryObject Atom} :
    SyntacticBoundaryEquiv Y₁ Y₂ → SyntacticBoundaryEquiv Y₂ Y₁ :=
  List.Perm.symm

/-- Transitivity of syntactic administrative equivalence. -/
theorem trans {Atom : Type u} {Y₁ Y₂ Y₃ : SyntacticBoundaryObject Atom} :
    SyntacticBoundaryEquiv Y₁ Y₂ →
      SyntacticBoundaryEquiv Y₂ Y₃ →
      SyntacticBoundaryEquiv Y₁ Y₃ :=
  List.Perm.trans

end SyntacticBoundaryEquiv

/-- Syntactic external-output equivalence: permutation of boundary atoms. -/
def SyntacticExternalOutEquiv {Atom : Type u}
    (L₁ L₂ : List (SyntacticRefinedInterface Atom)) : Prop :=
  List.Perm L₁ L₂

/-! ## B3 — Canonical list code modulo permutation -/

/-- A complete code for finite lists modulo permutation. -/
structure PermCodeContract (α : Type u) where
  /-- The code target type. -/
  Code : Type u
  /-- The canonical code. -/
  code : List α → Code
  /-- Soundness: permutation preserves the code. -/
  sound : ∀ {xs ys : List α}, List.Perm xs ys → code xs = code ys
  /-- Completeness: equal codes imply permutation. -/
  complete : ∀ {xs ys : List α}, code xs = code ys → List.Perm xs ys

/-- Canonical code for lists modulo permutation: pass to the quotient
`Multiset α`. -/
def multisetListCode {α : Type u} (xs : List α) : Multiset α :=
  (xs : Multiset α)

/-- Soundness of `multisetListCode`: permutation preserves the multiset code. -/
theorem multisetListCode_sound {α : Type u} {xs ys : List α}
    (h : List.Perm xs ys) : multisetListCode xs = multisetListCode ys := by
  exact Quot.sound h

/-- Completeness of `multisetListCode`: equal multiset codes imply
permutation. -/
theorem multisetListCode_complete {α : Type u} {xs ys : List α}
    (h : multisetListCode xs = multisetListCode ys) : List.Perm xs ys := by
  exact Multiset.coe_eq_coe.mp h

/-- A complete `PermCodeContract` via the exact quotient
`Multiset α = List α / List.Perm`. -/
def permCodeContractOfMultiset (α : Type u) : PermCodeContract α where
  Code := Multiset α
  code := multisetListCode
  sound := multisetListCode_sound
  complete := multisetListCode_complete

/-! ## B4 — Syntactic boundary code contracts -/

/-- Code contract for syntactic boundary objects modulo outer-block
permutation. -/
structure SyntacticBoundaryCodeContract (Atom : Type u) where
  /-- The syntactic boundary-code target. -/
  BoundaryCode : Type u
  /-- The syntactic boundary code. -/
  boundaryCode : SyntacticBoundaryObject Atom → BoundaryCode
  /-- Soundness for syntactic boundary equivalence. -/
  sound :
    ∀ {Y₁ Y₂ : SyntacticBoundaryObject Atom},
      SyntacticBoundaryEquiv Y₁ Y₂ → boundaryCode Y₁ = boundaryCode Y₂
  /-- Completeness for syntactic boundary equivalence. -/
  complete :
    ∀ {Y₁ Y₂ : SyntacticBoundaryObject Atom},
      boundaryCode Y₁ = boundaryCode Y₂ → SyntacticBoundaryEquiv Y₁ Y₂

/-- Code contract for syntactic external-output lists modulo permutation. -/
structure SyntacticExternalOutCodeContract (Atom : Type u) where
  /-- The external-output code target. -/
  ExternalOutCode : Type u
  /-- The external-output code. -/
  externalOutCode : List Atom → ExternalOutCode
  /-- Soundness for syntactic external-output equivalence. -/
  sound :
    ∀ {L₁ L₂ : List Atom},
      SyntacticExternalOutEquiv L₁ L₂ → externalOutCode L₁ = externalOutCode L₂
  /-- Completeness for syntactic external-output equivalence. -/
  complete :
    ∀ {L₁ L₂ : List Atom},
      externalOutCode L₁ = externalOutCode L₂ → SyntacticExternalOutEquiv L₁ L₂

/-- A permutation code on boundary blocks yields a syntactic boundary code
contract. -/
def syntacticBoundaryCodeContractOfPermCode {Atom : Type u}
    (C : PermCodeContract (BoundaryBlock Atom)) :
    SyntacticBoundaryCodeContract Atom where
  BoundaryCode := C.Code
  boundaryCode := C.code
  sound := C.sound
  complete := C.complete

/-- A permutation code on atoms yields a syntactic external-output code
contract. -/
def syntacticExternalOutCodeContractOfPermCode {Atom : Type u}
    (C : PermCodeContract Atom) :
    SyntacticExternalOutCodeContract Atom where
  ExternalOutCode := C.Code
  externalOutCode := C.code
  sound := C.sound
  complete := C.complete

/-- Syntactic boundary objects admit a concrete canonical code via the outer
multiset quotient of blocks. -/
def syntacticBoundaryCodeContract (Atom : Type u) :
    SyntacticBoundaryCodeContract Atom :=
  syntacticBoundaryCodeContractOfPermCode
    (permCodeContractOfMultiset (BoundaryBlock Atom))

/-- Syntactic external-output lists admit a concrete canonical code via the
multiset quotient. -/
def syntacticExternalOutCodeContract (Atom : Type u) :
    SyntacticExternalOutCodeContract Atom :=
  syntacticExternalOutCodeContractOfPermCode (permCodeContractOfMultiset Atom)

/-! ## B5 — Bridge from a syntactic presentation to the generic contracts -/

/-- A generic setup is *presented* by syntactic boundary objects when both the
boundary objects and refined interfaces admit encodings into a common atom
syntax, and those encodings are sound and complete for the relevant quotient
relations. -/
structure SyntacticBoundaryPresentation (setup : RewriteCalculusSetup.{u}) where
  /-- The atom type used by the syntactic presentation. -/
  Atom : Type u
  /-- Encode a generic boundary object as a syntactic one. -/
  encodeBoundary : setup.BoundaryObject → SyntacticBoundaryObject Atom
  /-- Encode a refined interface as an atom. -/
  encodeRefinedInterface : setup.RefinedInterface → Atom
  /-- Soundness of the boundary encoding for `BoundaryAdminEquiv`. -/
  boundary_sound :
    ∀ {Y₁ Y₂ : setup.BoundaryObject},
      BoundaryAdminEquiv Y₁ Y₂ →
        SyntacticBoundaryEquiv (encodeBoundary Y₁) (encodeBoundary Y₂)
  /-- Completeness of the boundary encoding for `BoundaryAdminEquiv`. -/
  boundary_complete :
    ∀ {Y₁ Y₂ : setup.BoundaryObject},
      SyntacticBoundaryEquiv (encodeBoundary Y₁) (encodeBoundary Y₂) →
        BoundaryAdminEquiv Y₁ Y₂
  /-- Soundness of interface encoding for permutation of external outputs. -/
  externalOut_sound :
    ∀ {L₁ L₂ : List setup.RefinedInterface},
      List.Perm L₁ L₂ →
        List.Perm (L₁.map encodeRefinedInterface) (L₂.map encodeRefinedInterface)
  /-- Completeness of interface encoding for permutation of external outputs. -/
  externalOut_complete :
    ∀ {L₁ L₂ : List setup.RefinedInterface},
      List.Perm (L₁.map encodeRefinedInterface) (L₂.map encodeRefinedInterface) →
        List.Perm L₁ L₂

namespace SyntacticBoundaryPresentation

/-- A syntactic presentation yields the generic admin-boundary code contract. -/
def toBoundaryAdminCodeContract
    (P : SyntacticBoundaryPresentation setup) :
    BoundaryAdminCodeContract.{u, u} setup := by
  let C := syntacticBoundaryCodeContract P.Atom
  exact
    { AdminBoundaryCode := C.BoundaryCode
      adminBoundaryCode := fun Y => C.boundaryCode (P.encodeBoundary Y)
      sound := fun h => C.sound (P.boundary_sound h)
      complete := fun h => P.boundary_complete (C.complete h) }

/-- A syntactic presentation yields the generic external-output code contract. -/
def toExternalOutCodeContract
    (P : SyntacticBoundaryPresentation setup) :
    ExternalOutCodeContract.{u, u} setup := by
  let C := syntacticExternalOutCodeContract P.Atom
  exact
    { ExternalOutCode := C.ExternalOutCode
      externalOutCode := fun L => C.externalOutCode (L.map P.encodeRefinedInterface)
      sound := fun h => C.sound (P.externalOut_sound h)
      complete := fun h => P.externalOut_complete (C.complete h) }

end SyntacticBoundaryPresentation

/-! ## B6 — Full quotient realization from a syntactic presentation -/

/-- A syntactic boundary presentation gives the faithful frontier quotient
realization by discharging the two named boundary obligations. -/
def syntactic_boundary_presentation_gives_frontier_quotient_realization
    (P : SyntacticBoundaryPresentation setup) :
    FrontierQuotientRealization.{u, u} setup :=
  theorem_full_quotient_realization_modulo_boundary_obligations
    (P.toBoundaryAdminCodeContract)
    (P.toExternalOutCodeContract)

/-! ## B7 — Manuscript-facing aliases -/

/-- Manuscript alias: syntactic boundary objects have a canonical quotient
code. -/
def theorem_syntactic_boundary_quotient_code
    (Atom : Type u) :
    SyntacticBoundaryCodeContract Atom :=
  syntacticBoundaryCodeContract Atom

/-- Manuscript alias: syntactic external-output lists have a canonical
permutation code. -/
def theorem_syntactic_external_out_perm_code
    (Atom : Type u) :
    SyntacticExternalOutCodeContract Atom :=
  syntacticExternalOutCodeContract Atom

/-- Manuscript alias: a syntactic presentation gives both boundary-side generic
code contracts. -/
def theorem_syntactic_boundary_presentation_gives_boundary_contracts
    (P : SyntacticBoundaryPresentation setup) :
    BoundaryAdminCodeContract.{u, u} setup × ExternalOutCodeContract.{u, u} setup :=
  (P.toBoundaryAdminCodeContract, P.toExternalOutCodeContract)

/-- Manuscript alias: a syntactic presentation gives the faithful frontier
quotient realization. -/
def theorem_syntactic_boundary_presentation_gives_frontier_quotient_realization
    (P : SyntacticBoundaryPresentation setup) :
    FrontierQuotientRealization.{u, u} setup :=
  syntactic_boundary_presentation_gives_frontier_quotient_realization P

/-! ## B8 — Local proof-harvest surface -/

/-! ### B2 equivalence simp bridges -/

/-- `BoundaryBlockEquiv` is definitionally equality. -/
@[simp]
theorem BoundaryBlockEquiv_iff {Atom : Type u} (b₁ b₂ : BoundaryBlock Atom) :
    BoundaryBlockEquiv b₁ b₂ ↔ b₁ = b₂ :=
  Iff.rfl

/-- `SyntacticBoundaryEquiv` is `List.Perm`. -/
@[simp]
theorem SyntacticBoundaryEquiv_iff {Atom : Type u}
    (Y₁ Y₂ : SyntacticBoundaryObject Atom) :
    SyntacticBoundaryEquiv Y₁ Y₂ ↔ List.Perm Y₁ Y₂ :=
  Iff.rfl

/-- `SyntacticExternalOutEquiv` is `List.Perm`. -/
@[simp]
theorem SyntacticExternalOutEquiv_iff {Atom : Type u}
    (L₁ L₂ : List (SyntacticRefinedInterface Atom)) :
    SyntacticExternalOutEquiv L₁ L₂ ↔ List.Perm L₁ L₂ :=
  Iff.rfl

/-! ### B3 `PermCodeContract` projection simp lemmas -/


/-- Soundness alias: `PermCodeContract` sound field is accessible via `perm_imp_code_eq`. -/
theorem PermCodeContract.perm_imp_code_eq {α : Type u} (C : PermCodeContract α)
    {xs ys : List α} (h : List.Perm xs ys) : C.code xs = C.code ys :=
  C.sound h

/-- Completeness alias: `PermCodeContract` complete field accessible via `code_eq_imp_perm`. -/
theorem PermCodeContract.code_eq_imp_perm {α : Type u} (C : PermCodeContract α)
    {xs ys : List α} (h : C.code xs = C.code ys) : List.Perm xs ys :=
  C.complete h

/-- Combined iff alias for `PermCodeContract`. -/
theorem PermCodeContract.code_eq_iff_perm {α : Type u} (C : PermCodeContract α)
    (xs ys : List α) :
    C.code xs = C.code ys ↔ List.Perm xs ys :=
  ⟨C.complete, C.sound⟩

/-! ### B3 `permCodeContractOfMultiset` simp lemmas -/

@[simp]
theorem permCodeContractOfMultiset_Code (α : Type u) :
    (permCodeContractOfMultiset α).Code = Multiset α :=
  rfl

@[simp]
theorem permCodeContractOfMultiset_code (α : Type u) (xs : List α) :
    (permCodeContractOfMultiset α).code xs = (xs : Multiset α) :=
  rfl

/-! ### B4 `SyntacticBoundaryCodeContract` projection simp lemmas -/


/-- Soundness iff alias for `SyntacticBoundaryCodeContract`. -/
theorem SyntacticBoundaryCodeContract.code_eq_iff_equiv {Atom : Type u}
    (C : SyntacticBoundaryCodeContract Atom)
    (Y₁ Y₂ : SyntacticBoundaryObject Atom) :
    C.boundaryCode Y₁ = C.boundaryCode Y₂ ↔ SyntacticBoundaryEquiv Y₁ Y₂ :=
  ⟨C.complete, C.sound⟩

/-! ### B4 `SyntacticExternalOutCodeContract` projection simp lemmas -/


/-- Soundness iff alias for `SyntacticExternalOutCodeContract`. -/
theorem SyntacticExternalOutCodeContract.code_eq_iff_equiv {Atom : Type u}
    (C : SyntacticExternalOutCodeContract Atom) (L₁ L₂ : List Atom) :
    C.externalOutCode L₁ = C.externalOutCode L₂ ↔ SyntacticExternalOutEquiv L₁ L₂ :=
  ⟨C.complete, C.sound⟩

/-! ### B4 concrete contract simp lemmas -/

@[simp]
theorem syntacticBoundaryCodeContract_BoundaryCode (Atom : Type u) :
    (syntacticBoundaryCodeContract Atom).BoundaryCode = Multiset (BoundaryBlock Atom) :=
  rfl

@[simp]
theorem syntacticBoundaryCodeContract_boundaryCode (Atom : Type u)
    (Y : SyntacticBoundaryObject Atom) :
    (syntacticBoundaryCodeContract Atom).boundaryCode Y = (Y : Multiset (BoundaryBlock Atom)) :=
  rfl

@[simp]
theorem syntacticExternalOutCodeContract_ExternalOutCode (Atom : Type u) :
    (syntacticExternalOutCodeContract Atom).ExternalOutCode = Multiset Atom :=
  rfl

@[simp]
theorem syntacticExternalOutCodeContract_externalOutCode (Atom : Type u)
    (L : List Atom) :
    (syntacticExternalOutCodeContract Atom).externalOutCode L = (L : Multiset Atom) :=
  rfl

/-! ### B5 `SyntacticBoundaryPresentation` field projection aliases -/

/-- Boundary encoding soundness for a presentation (direct field accessor). -/
theorem SyntacticBoundaryPresentation.boundary_sound_apply
    (P : SyntacticBoundaryPresentation setup)
    {Y₁ Y₂ : setup.BoundaryObject}
    (h : BoundaryAdminEquiv Y₁ Y₂) :
    SyntacticBoundaryEquiv (P.encodeBoundary Y₁) (P.encodeBoundary Y₂) :=
  P.boundary_sound h

/-- Boundary encoding completeness for a presentation (direct field accessor). -/
theorem SyntacticBoundaryPresentation.boundary_complete_apply
    (P : SyntacticBoundaryPresentation setup)
    {Y₁ Y₂ : setup.BoundaryObject}
    (h : SyntacticBoundaryEquiv (P.encodeBoundary Y₁) (P.encodeBoundary Y₂)) :
    BoundaryAdminEquiv Y₁ Y₂ :=
  P.boundary_complete h

/-- Boundary encoding iff: `BoundaryAdminEquiv Y₁ Y₂` iff encodings are syntactically equiv. -/
theorem SyntacticBoundaryPresentation.boundary_equiv_iff
    (P : SyntacticBoundaryPresentation setup)
    (Y₁ Y₂ : setup.BoundaryObject) :
    BoundaryAdminEquiv Y₁ Y₂ ↔
      SyntacticBoundaryEquiv (P.encodeBoundary Y₁) (P.encodeBoundary Y₂) :=
  ⟨P.boundary_sound, P.boundary_complete⟩

/-- External-output encoding soundness (direct field accessor). -/
theorem SyntacticBoundaryPresentation.externalOut_sound_apply
    (P : SyntacticBoundaryPresentation setup)
    {L₁ L₂ : List setup.RefinedInterface}
    (h : List.Perm L₁ L₂) :
    List.Perm (L₁.map P.encodeRefinedInterface) (L₂.map P.encodeRefinedInterface) :=
  P.externalOut_sound h

/-- External-output encoding completeness (direct field accessor). -/
theorem SyntacticBoundaryPresentation.externalOut_complete_apply
    (P : SyntacticBoundaryPresentation setup)
    {L₁ L₂ : List setup.RefinedInterface}
    (h : List.Perm (L₁.map P.encodeRefinedInterface) (L₂.map P.encodeRefinedInterface)) :
    List.Perm L₁ L₂ :=
  P.externalOut_complete h

/-- External-output encoding iff. -/
theorem SyntacticBoundaryPresentation.externalOut_perm_iff
    (P : SyntacticBoundaryPresentation setup)
    (L₁ L₂ : List setup.RefinedInterface) :
    List.Perm L₁ L₂ ↔
      List.Perm (L₁.map P.encodeRefinedInterface) (L₂.map P.encodeRefinedInterface) :=
  ⟨P.externalOut_sound, P.externalOut_complete⟩

/-! ### B5 `toBoundaryAdminCodeContract` / `toExternalOutCodeContract` field simp -/

@[simp]
theorem SyntacticBoundaryPresentation.toBoundaryAdminCodeContract_AdminBoundaryCode
    (P : SyntacticBoundaryPresentation setup) :
    P.toBoundaryAdminCodeContract.AdminBoundaryCode =
      Multiset (BoundaryBlock P.Atom) :=
  rfl

@[simp]
theorem SyntacticBoundaryPresentation.toBoundaryAdminCodeContract_adminBoundaryCode
    (P : SyntacticBoundaryPresentation setup)
    (Y : setup.BoundaryObject) :
    P.toBoundaryAdminCodeContract.adminBoundaryCode Y =
      (P.encodeBoundary Y : Multiset (BoundaryBlock P.Atom)) :=
  rfl

@[simp]
theorem SyntacticBoundaryPresentation.toExternalOutCodeContract_ExternalOutCode
    (P : SyntacticBoundaryPresentation setup) :
    P.toExternalOutCodeContract.ExternalOutCode = Multiset P.Atom :=
  rfl

@[simp]
theorem SyntacticBoundaryPresentation.toExternalOutCodeContract_externalOutCode
    (P : SyntacticBoundaryPresentation setup)
    (L : List setup.RefinedInterface) :
    P.toExternalOutCodeContract.externalOutCode L =
      (L.map P.encodeRefinedInterface : Multiset P.Atom) :=
  rfl

/-! ### B4 `SyntacticBoundaryCodeContract` / `SyntacticExternalOutCodeContract` directional aliases -/

/-- Soundness of `SyntacticBoundaryCodeContract` (direct application). -/
theorem SyntacticBoundaryCodeContract.sound_apply {Atom : Type u}
    (C : SyntacticBoundaryCodeContract Atom)
    {Y₁ Y₂ : SyntacticBoundaryObject Atom}
    (h : SyntacticBoundaryEquiv Y₁ Y₂) :
    C.boundaryCode Y₁ = C.boundaryCode Y₂ :=
  C.sound h

/-- Completeness of `SyntacticBoundaryCodeContract` (direct application). -/
theorem SyntacticBoundaryCodeContract.complete_apply {Atom : Type u}
    (C : SyntacticBoundaryCodeContract Atom)
    {Y₁ Y₂ : SyntacticBoundaryObject Atom}
    (h : C.boundaryCode Y₁ = C.boundaryCode Y₂) :
    SyntacticBoundaryEquiv Y₁ Y₂ :=
  C.complete h

/-- Soundness of `SyntacticExternalOutCodeContract` (direct application). -/
theorem SyntacticExternalOutCodeContract.sound_apply {Atom : Type u}
    (C : SyntacticExternalOutCodeContract Atom)
    {L₁ L₂ : List Atom}
    (h : SyntacticExternalOutEquiv L₁ L₂) :
    C.externalOutCode L₁ = C.externalOutCode L₂ :=
  C.sound h

/-- Completeness of `SyntacticExternalOutCodeContract` (direct application). -/
theorem SyntacticExternalOutCodeContract.complete_apply {Atom : Type u}
    (C : SyntacticExternalOutCodeContract Atom)
    {L₁ L₂ : List Atom}
    (h : C.externalOutCode L₁ = C.externalOutCode L₂) :
    SyntacticExternalOutEquiv L₁ L₂ :=
  C.complete h

/-! ### B5 `SyntacticBoundaryPresentation` bridge directional aliases -/

/-- Assembled admin-boundary code contract soundness (direct application). -/
theorem SyntacticBoundaryPresentation.toBoundaryAdminCodeContract_sound_apply
    (P : SyntacticBoundaryPresentation setup)
    {Y₁ Y₂ : setup.BoundaryObject}
    (h : BoundaryAdminEquiv Y₁ Y₂) :
    P.toBoundaryAdminCodeContract.adminBoundaryCode Y₁ =
      P.toBoundaryAdminCodeContract.adminBoundaryCode Y₂ :=
  P.toBoundaryAdminCodeContract.sound h

/-- Assembled admin-boundary code contract completeness (direct application). -/
theorem SyntacticBoundaryPresentation.toBoundaryAdminCodeContract_complete_apply
    (P : SyntacticBoundaryPresentation setup)
    {Y₁ Y₂ : setup.BoundaryObject}
    (h : P.toBoundaryAdminCodeContract.adminBoundaryCode Y₁ =
         P.toBoundaryAdminCodeContract.adminBoundaryCode Y₂) :
    BoundaryAdminEquiv Y₁ Y₂ :=
  P.toBoundaryAdminCodeContract.complete h

/-- Assembled external-output code contract soundness (direct application). -/
theorem SyntacticBoundaryPresentation.toExternalOutCodeContract_sound_apply
    (P : SyntacticBoundaryPresentation setup)
    {L₁ L₂ : List setup.RefinedInterface}
    (h : List.Perm L₁ L₂) :
    P.toExternalOutCodeContract.externalOutCode L₁ =
      P.toExternalOutCodeContract.externalOutCode L₂ :=
  P.toExternalOutCodeContract.sound h

/-- Assembled external-output code contract completeness (direct application). -/
theorem SyntacticBoundaryPresentation.toExternalOutCodeContract_complete_apply
    (P : SyntacticBoundaryPresentation setup)
    {L₁ L₂ : List setup.RefinedInterface}
    (h : P.toExternalOutCodeContract.externalOutCode L₁ =
         P.toExternalOutCodeContract.externalOutCode L₂) :
    List.Perm L₁ L₂ :=
  P.toExternalOutCodeContract.complete h

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc