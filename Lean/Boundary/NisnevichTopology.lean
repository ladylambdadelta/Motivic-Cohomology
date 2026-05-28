import Boundary.NisnevichDescent
import Mathlib.CategoryTheory.Sites.Coverage

/-!
# Nisnevich Presieve Definitions for Sm/k

This file defines the generating presieve for a Nisnevich distinguished square
and the collection of Nisnevich covering presieves on each object of
`Geometry.SmSchemeOver k`.

## What is here

- `nisnevichCoverPresieve sq` — the two-morphism presieve
  `{openToBase, patchToBase}` on `sq.base` for a distinguished square `sq`.

- `nisnevichCovering X` — the set of all Nisnevich covering presieves on `X`:
  those equal (up to transport) to `nisnevichCoverPresieve sq` for some
  square with base `X`.

## What is NOT here — `NisnevichDistinguishedSquareDataQ.pullback`

Assembling a `Coverage (SmSchemeOver k)` from `nisnevichCovering` requires
proving `Coverage.pullback`: given any `S ∈ nisnevichCovering X` and any
morphism `f : Y ⟶ X`, produce a covering presieve in `nisnevichCovering Y`
factoring through `S` along `f`.

The required statement is:

  NisnevichDistinguishedSquareDataQ.pullback
    {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : Y ⟶ sq.base) :
    NisnevichDistinguishedSquareDataQ category

where the returned square has `base = Y` and open/patch/overlap given by the
fibre products `sq.openPiece ×_{sq.base} Y`, `sq.patchPiece ×_{sq.base} Y`,
`sq.overlap ×_{sq.base} Y`.

### Blocking dependency 1 — `HasPullbacks (Geometry.SmSchemeOver k)`

`HasPullbacks Scheme` exists in Mathlib (`Mathlib.AlgebraicGeometry.Pullbacks`,
instance at line 448).  However `Geometry.SmSchemeOver k` uses a **custom**
`Category` instance (`SmOverHom`, not `Over Scheme (Spec k)`), so the Mathlib
`Over.hasPullbacks` instance does not apply directly.  A dedicated instance

  instance smSchemeOver_hasPullbacks :
      HasPullbacks (Geometry.SmSchemeOver k)

must be constructed by:
  (a) forming the scheme-level pullback via `Scheme.pullback`,
  (b) equipping it with a structure map to `Spec k`,
  (c) proving the pullback scheme is smooth (from
      `AlgebraicGeometry.isSmooth_isStableUnderBaseChange`), separated, and
      of finite type over `k`,
  (d) packing it as a `SmSchemeOver k` value and verifying the universal
      property in terms of `SmOverHom`.

### Blocking dependency 2 — typed geometry fields ✓ RESOLVED

`NisnevichDistinguishedSquareDataQ` previously carried several fields of bare
type `Prop`.  These have been replaced with typed fields:

  patchToBase_isEtale    : IsEtale patchToBase.hom
  overlap_isPullback     : IsPullback overlapToOpen.hom overlapToPatch.hom
                             openToBase.hom patchToBase.hom

The `residueFieldLift` and four `*_transferRepresentsMap` obligation fields
(which were unused in proofs) have been removed.

With the geometry fields now typed, `IsEtale` stability under base change
(`instance : IsStableUnderBaseChange @IsEtale`,
`Mathlib.AlgebraicGeometry.Morphisms.Etale` line 33) and `IsPullback`
stability machinery are now accessible once the remaining blockers below are
resolved.

### Blocking dependency 3 — `IsOpenImmersion` stable under base change

After `smSchemeOver_hasPullbacks` is available, `IsOpenImmersion` of the
pulled-back open piece follows from `MorphismProperty.pullback_snd`
(`Mathlib.CategoryTheory.MorphismProperty.Limits:97`) together with
`instance : IsStableUnderBaseChange @IsOpenImmersion`.
(This Mathlib instance needs to be located or proved.)

### Blocking dependency 4 — `IsEtale` stable under base change

Similarly, the étale condition on the pulled-back patch piece follows from
`MorphismProperty.pullback_snd` together with
`instance : IsStableUnderBaseChange @IsEtale`
(`Mathlib.AlgebraicGeometry.Morphisms.Etale`, line 33).

### Blocking dependency 5 — `RationalFiniteCorrespondence` under base change

`SmCorQ.Hom category X Y = RationalFiniteCorrespondence X Y` (a rational
finite correspondence in the sense of Voevodsky).  The transfer maps

  openToBaseTransfer   : SmCorQ.Hom category sq.openPiece sq.base
  patchToBaseTransfer  : SmCorQ.Hom category sq.patchPiece sq.base

must be transported to the pulled-back square.  Concretely, this requires a
natural map

  RationalFiniteCorrespondence.baseChange
    (f : SmOverHom Y X) (c : RationalFiniteCorrespondence A X) :
    RationalFiniteCorrespondence (A ×_X Y) Y

induced by the graph of the projection `pullback.fst`.  This theory of
correspondences under base change is **not** present in Mathlib or in this
project, and is the deepest blocker.

Until all five dependencies are resolved, `NisnevichCoverage` and
`NisnevichTopology` cannot be constructed without an unproved axiom.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory

namespace Boundary

noncomputable section

/-!
## Generating presieve for a Nisnevich distinguished square
-/

/-- The two-morphism generating presieve on `sq.base` determined by a Nisnevich
distinguished square: a morphism `f : Y ⟶ sq.base` belongs to this presieve
iff it equals the open-piece inclusion **or** the patch-piece étale map. -/
def nisnevichCoverPresieve
    {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category) :
    Presieve sq.base :=
  fun Y f =>
    (∃ h : Y = sq.openPiece, h ▸ f = sq.openToBase) ∨
    (∃ h : Y = sq.patchPiece, h ▸ f = sq.patchToBase)

/-- `openToBase` belongs to the generating presieve of its distinguished square. -/
theorem nisnevichCoverPresieve_openToBase
    {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category) :
    nisnevichCoverPresieve sq sq.openToBase :=
  Or.inl ⟨rfl, rfl⟩

/-- `patchToBase` belongs to the generating presieve of its distinguished square. -/
theorem nisnevichCoverPresieve_patchToBase
    {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category) :
    nisnevichCoverPresieve sq sq.patchToBase :=
  Or.inr ⟨rfl, rfl⟩

/-!
## Nisnevich covering families
-/

/-- The collection of Nisnevich covering presieves on `X`: those equal to the
generating presieve of some Nisnevich distinguished square with base `X`.

A presieve `S` on `X` is in `nisnevichCovering X` iff there exist a
rationalization category `cat` and a distinguished square `sq` with
`sq.base = X` such that `S = nisnevichCoverPresieve sq` (after transport
along `sq.base = X`). -/
def nisnevichCovering
    (X : Geometry.SmSchemeOver k) : Set (Presieve X) :=
  { S | ∃ (cat : SmCorQ (k := k))
           (sq : NisnevichDistinguishedSquareDataQ cat)
           (h : sq.base = X),
         S = h ▸ nisnevichCoverPresieve sq }

/-- The generating presieve of a square with base `X` lies in
`nisnevichCovering X`. -/
theorem nisnevichCoverPresieve_mem_nisnevichCovering
    {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category) :
    nisnevichCoverPresieve sq ∈ nisnevichCovering sq.base :=
  ⟨category, sq, rfl, rfl⟩

end

end Boundary
