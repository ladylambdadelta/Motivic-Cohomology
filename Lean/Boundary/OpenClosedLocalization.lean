import Boundary.MinimalPresentationPackage
import Boundary.ProjectiveLineGeometry
import Boundary.NisnevichPullbackTransfer

/-!
# Open/Closed Localization Construction Surface

This file records the actual smooth pair data used by the Boundary-side Tate
pipeline. The record is intentionally narrow: it packages real ambient/open/
closed geometric data and the corresponding correspondence-level transfer maps
without inventing a fake localization triangle or purity layer.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory

namespace Boundary

noncomputable section

/-- A smooth closed pair with the ambient/open/closed geometry and the actual
correspondence-level transfer maps used by the Boundary motivic pipeline. -/
structure SmoothClosedPairQ (category : SmCorQ (k := k)) where
  ambient : Geometry.SmSchemeOver k
  openPiece : Geometry.SmSchemeOver k
  closedPiece : Geometry.SmSchemeOver k
  codimension : Nat
  openToAmbient : openPiece ⟶ ambient
  closedToAmbient : closedPiece ⟶ ambient
  openToAmbientTransfer : SmCorQ.Hom category openPiece ambient
  closedToAmbientTransfer : SmCorQ.Hom category closedPiece ambient
  openImmersionTarget : IsOpenImmersion openToAmbient.hom
  closedSection : closedToAmbient.hom ≫ ambient.structMap = 𝟙 _

/-- Boundary-side localization package built from an indexed family of actual
smooth closed pairs. The package records the geometric input only; any
localization triangle or purity theorem must be proved in the owner files that
consume these pairs. -/
structure OpenClosedLocalizationPresentationQ (category : SmCorQ (k := k)) where
  PairIndex : Type (u + 1)
  pair : PairIndex → SmoothClosedPairQ category

namespace OpenClosedLocalizationPresentationQ

/-- The geometric ambient object for a chosen pair. -/
abbrev ambient {category : SmCorQ (k := k)}
    (presentation : OpenClosedLocalizationPresentationQ (k := k) category)
    (i : presentation.PairIndex) :
    Geometry.SmSchemeOver k :=
  (presentation.pair i).ambient

/-- The open piece for a chosen pair. -/
abbrev openPiece {category : SmCorQ (k := k)}
    (presentation : OpenClosedLocalizationPresentationQ (k := k) category)
    (i : presentation.PairIndex) :
    Geometry.SmSchemeOver k :=
  (presentation.pair i).openPiece

/-- The closed piece for a chosen pair. -/
abbrev closedPiece {category : SmCorQ (k := k)}
    (presentation : OpenClosedLocalizationPresentationQ (k := k) category)
    (i : presentation.PairIndex) :
    Geometry.SmSchemeOver k :=
  (presentation.pair i).closedPiece

/-- The closed-leg section equation for a chosen pair. -/
abbrev closedSection {category : SmCorQ (k := k)}
    (presentation : OpenClosedLocalizationPresentationQ (k := k) category)
    (i : presentation.PairIndex) :
    (presentation.pair i).closedToAmbient.hom ≫ (presentation.ambient i).structMap = 𝟙 _ :=
  (presentation.pair i).closedSection

end OpenClosedLocalizationPresentationQ

/-- The canonical `P¹` open/closed pair used by the Tate surface:
the open piece is the standard `x₁` chart, and the closed piece is the
canonical rational section `[0:1]` of the projective line. -/
def boundaryProjectiveLineOpenClosedPair
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    SmoothClosedPairQ (Boundary.canonicalCategory composition) where
  ambient := Boundary.boundaryProjectiveLineCanonicalObject (k := k)
  openPiece :=
    Geometry.SmSchemeOver.ofOpenImmersionMap
      (Y := Boundary.boundaryProjectiveLineCanonicalObject (k := k))
      (Boundary.boundaryProjectiveLineCoordinateAwayι (k := k) 1)
  closedPiece := Boundary.boundarySpecObject k
  codimension := 1
  openToAmbient :=
    Boundary.boundaryProjectiveLineCoordinateAwayι (k := k) 1
  closedToAmbient :=
    Boundary.boundaryProjectiveLineBasepoint (k := k)
  openToAmbientTransfer :=
    SmCorQ.graphTransfer (Boundary.canonicalCategory composition)
      (Boundary.boundaryProjectiveLineCoordinateAwayι (k := k) 1)
      (composition.diagonalDecomposition
        (Boundary.boundaryProjectiveLineCanonicalObject (k := k)))
  closedToAmbientTransfer :=
    SmCorQ.graphTransfer (Boundary.canonicalCategory composition)
      (Boundary.boundaryProjectiveLineBasepoint (k := k))
      (composition.diagonalDecomposition
        (Boundary.boundarySpecObject k))
  openImmersionTarget := by
    infer_instance
  closedSection := by
    simpa [Boundary.boundaryProjectiveLineBasepoint_hom] using
      (Boundary.boundaryProjectiveLineBasepoint_section (k := k))

/-- The canonical projective-line localization pair is already geometric data
and not a synthetic witness shell. This theorem packages that fact for the
stabilization layer. -/
theorem boundaryProjectiveLineOpenClosedPair_isCanonical
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    (boundaryProjectiveLineOpenClosedPair (k := k) composition).ambient =
      Boundary.boundaryProjectiveLineCanonicalObject (k := k) ∧
    (boundaryProjectiveLineOpenClosedPair (k := k) composition).closedPiece =
      Boundary.boundarySpecObject k := by
  constructor <;> rfl

/-- The canonical projective-line pair carries the basepoint section equation
as an owner-level theorem. -/
theorem boundaryProjectiveLineOpenClosedPair_closedSection
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    (boundaryProjectiveLineOpenClosedPair (k := k) composition).closedToAmbient.hom ≫
        (boundaryProjectiveLineOpenClosedPair (k := k) composition).ambient.structMap =
      𝟙 _ := by
  exact
    (Boundary.boundaryProjectiveLineBasepoint_section (k := k))

/-- The canonical `P¹` pair exposes its open piece as the standard chart. -/
theorem boundaryProjectiveLineOpenClosedPair_openPiece_eq
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    (boundaryProjectiveLineOpenClosedPair (k := k) composition).openPiece =
      Geometry.SmSchemeOver.ofOpenImmersionMap
        (Y := Boundary.boundaryProjectiveLineCanonicalObject (k := k))
        (Boundary.boundaryProjectiveLineCoordinateAwayι (k := k) 1) :=
  rfl

/-- The canonical `P¹` pair exposes its closed piece as the base `Spec k`. -/
theorem boundaryProjectiveLineOpenClosedPair_closedPiece_eq
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    (boundaryProjectiveLineOpenClosedPair (k := k) composition).closedPiece =
      Boundary.boundarySpecObject k :=
  rfl

/-- The canonical Boundary-side localization package for the projective line.
This is the stable owner-level input for the Tate/localization surface. -/
def boundaryProjectiveLineLocalizationPresentation
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    OpenClosedLocalizationPresentationQ (Boundary.canonicalCategory composition) where
  PairIndex := PUnit
  pair := fun _ => boundaryProjectiveLineOpenClosedPair (k := k) composition

end

end Boundary
