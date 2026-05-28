import Boundary.NisnevichDescent
import Geometry.Correspondences.Graph

/-!
# Graph-Based Transfer Maps for Pulled-Back Nisnevich Squares

This file provides the graph-correspondence constructors for the four transfer
maps of a base-changed Nisnevich distinguished square.

## Strategy

Given a Nisnevich square `sq` and a base-change morphism `f : SmOverHom Y sq.base`,
the transfer maps for the pulled-back square are constructed as graph correspondences
of the scheme-level projection morphisms, using
`Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition`.

Each constructor takes as explicit parameters:
- a `Geometry.SmSchemeOver k` structure for the relevant pulled-back piece, and
- a `SmOverHom` for the relevant projection morphism, and
- a `FiniteIrreducibleComponentDecomposition` of the source piece.

These are not supplied automatically because:
1. The `SmSchemeOver k` structure for a pullback requires `IsOfFiniteType` for
   the structural map, which for an étale or open-immersion pullback needs
   `IsLocallyNoetherian` on the base (or an explicit hypothesis).
2. `FiniteIrreducibleComponentDecomposition` is a Noetherian datum that is not
   automatic from the `SmSchemeOver` axioms alone.

## Exact remaining blocker for `NisnevichDistinguishedSquareDataQ.pullback`

Once the four transfer maps defined here are in hand, the only remaining
obligation is the commutativity condition
`overlap_to_base_transfer_commutes` for the pulled-back square.  That condition
requires:

  **`Geometry.ordinaryMorphismGraph_comp`** (currently a stub in
  `Lean/Geometry/Correspondences/Composition.lean`):
  ```
  category.comp
      (ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category f D_X)
      (ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category g D_Y)
    = ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category (f ≫ g) D_X
  ```
  This is the classical fact that composition of graph correspondences equals
  the graph of the composite (for smooth separated morphisms of finite type).
  Proof sketch: the fiber product of the two graph supports is
  `X.scheme ×_{Y.scheme} Y.scheme ≅ X.scheme`, and its integral structure
  matches the graph of `f ≫ g`.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory

namespace Boundary

noncomputable section

namespace SmCorQ

/-- The graph-correspondence transfer map of an ordinary `Sm/k` morphism,
given a certified finite irreducible-component decomposition of the source.

This is a named alias for
`Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition`
placed in the `SmCorQ` namespace for use in Nisnevich-square constructions. -/
def graphTransfer
    (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (f : SmOverHom X Y)
    (decomp : FiniteIrreducibleComponentDecomposition X) :
    SmCorQ.Hom category X Y :=
  Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category f decomp

/-- `graphTransfer` does not depend on the choice of finite irreducible-component
decomposition of the source. -/
theorem graphTransfer_independent
    (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (f : SmOverHom X Y)
    (D₁ D₂ : FiniteIrreducibleComponentDecomposition X) :
    SmCorQ.graphTransfer category f D₁ = SmCorQ.graphTransfer category f D₂ :=
  Geometry.ordinaryMorphismGraph_rationalCorrespondence_independent category f D₁ D₂

end SmCorQ

namespace NisnevichDistinguishedSquareDataQ

/-- Graph-based open-to-base transfer for a base-changed Nisnevich square.

Given a Nisnevich square `sq` with base-change morphism `f : SmOverHom Y sq.base`,
a `SmSchemeOver k` structure `openPiece'` for the pulled-back open piece,
a projection morphism `snd_open : SmOverHom openPiece' Y` (corresponding to
`pullback.snd sq.openToBase.hom f.hom`), and a finite irreducible-component
decomposition `decomp` of `openPiece'`, this produces the graph correspondence
`openPiece' → Y` as the open-to-base transfer for the pulled-back square. -/
def baseChange_openToBaseTransfer
    {category : SmCorQ (k := k)}
    (_sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (_f : SmOverHom Y _sq.base)
    (openPiece' : Geometry.SmSchemeOver k)
    (snd_open : SmOverHom openPiece' Y)
    (decomp : FiniteIrreducibleComponentDecomposition openPiece') :
    SmCorQ.Hom category openPiece' Y :=
  SmCorQ.graphTransfer category snd_open decomp

/-- Graph-based patch-to-base transfer for a base-changed Nisnevich square.

Analogous to `baseChange_openToBaseTransfer` for the étale patch piece.
`snd_patch` should be the morphism corresponding to
`pullback.snd sq.patchToBase.hom f.hom`. -/
def baseChange_patchToBaseTransfer
    {category : SmCorQ (k := k)}
    (_sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (_f : SmOverHom Y _sq.base)
    (patchPiece' : Geometry.SmSchemeOver k)
    (snd_patch : SmOverHom patchPiece' Y)
    (decomp : FiniteIrreducibleComponentDecomposition patchPiece') :
    SmCorQ.Hom category patchPiece' Y :=
  SmCorQ.graphTransfer category snd_patch decomp

/-- Graph-based overlap-to-open transfer for a base-changed Nisnevich square.

`toOpen` should be the morphism corresponding to the first pullback projection
restricted to the overlap piece, i.e. the `SmOverHom` analogue of
`pullback.fst (pullback.snd sq.openToBase.hom f.hom)
              (pullback.snd sq.patchToBase.hom f.hom)`. -/
def baseChange_overlapToOpenTransfer
    {category : SmCorQ (k := k)}
    (_sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (_f : SmOverHom Y _sq.base)
    (overlap' openPiece' : Geometry.SmSchemeOver k)
    (toOpen : SmOverHom overlap' openPiece')
    (decomp : FiniteIrreducibleComponentDecomposition overlap') :
    SmCorQ.Hom category overlap' openPiece' :=
  SmCorQ.graphTransfer category toOpen decomp

/-- Graph-based overlap-to-patch transfer for a base-changed Nisnevich square.

`toPatch` should be the morphism corresponding to the second pullback projection
restricted to the overlap piece, i.e. the `SmOverHom` analogue of
`pullback.snd (pullback.snd sq.openToBase.hom f.hom)
              (pullback.snd sq.patchToBase.hom f.hom)`. -/
def baseChange_overlapToPatchTransfer
    {category : SmCorQ (k := k)}
    (_sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (_f : SmOverHom Y _sq.base)
    (overlap' patchPiece' : Geometry.SmSchemeOver k)
    (toPatch : SmOverHom overlap' patchPiece')
    (decomp : FiniteIrreducibleComponentDecomposition overlap') :
    SmCorQ.Hom category overlap' patchPiece' :=
  SmCorQ.graphTransfer category toPatch decomp

end NisnevichDistinguishedSquareDataQ

end -- noncomputable section

end Boundary
