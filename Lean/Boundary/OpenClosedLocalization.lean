import Boundary.MinimalPresentationPackage

/-!
# Open/Closed Localization Target Surface

This file records typed smooth closed-pair data and the exact theorem surface
for the internal localization triangle derived from the minimal presentation
package.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory

namespace Boundary

noncomputable section

/-- Typed smooth closed pair together with the chosen transfer maps that will
eventually feed the Gysin map and localization triangle. -/
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
  closedImmersionTarget : Prop
  complementCompatibilityTarget : Prop
  open_transferRepresentsMapTarget : Prop
  closed_transferRepresentsMapTarget : Prop

/-- Exact theorem-target package for internal open/closed localization on the
boundary-side correspondence category. -/
structure OpenClosedLocalizationPresentationQ (category : SmCorQ (k := k)) where
  PairIndex : Type (u + 1)
  pair : PairIndex → SmoothClosedPairQ category
  purityTarget : PairIndex → Prop
  gysinMapTarget : PairIndex → Prop
  localizationTriangleTarget : Prop
  gluingCompatibilityTarget : Prop

namespace OpenClosedLocalizationPresentationQ

def theoremTarget {category : SmCorQ (k := k)}
    (presentation : OpenClosedLocalizationPresentationQ category) : Prop :=
  (∀ pairIndex, presentation.purityTarget pairIndex ∧ presentation.gysinMapTarget pairIndex) ∧
    presentation.localizationTriangleTarget ∧
    presentation.gluingCompatibilityTarget

end OpenClosedLocalizationPresentationQ

/-- Certified wrapper for the open/closed localization theorem surface. -/
structure CertifiedOpenClosedLocalizationPresentationQ (category : SmCorQ (k := k)) where
  target : OpenClosedLocalizationPresentationQ category
  theorem_holds : target.theoremTarget

end

end Boundary
