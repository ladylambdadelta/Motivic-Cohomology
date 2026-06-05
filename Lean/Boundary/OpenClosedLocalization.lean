import Boundary.MinimalPresentationPackage

/-!
# Open/Closed Localization Construction Surface

This file records typed smooth closed-pair data and the exact construction surface
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
  closedImmersionData : Type (u + 1)
  complementCompatibilityObligation : Type (u + 1)
  openTransferRepresentsMapData : Type (u + 1)
  closedTransferRepresentsMapData : Type (u + 1)

/-- Exact construction package for internal open/closed localization on the
boundary-side correspondence category. -/
structure OpenClosedLocalizationPresentationQ (category : SmCorQ (k := k)) where
  PairIndex : Type (u + 1)
  pair : PairIndex → SmoothClosedPairQ category
  purityData : PairIndex → Type (u + 1)
  gysinMapData : PairIndex → Type (u + 1)
  localizationTriangleData : Type (u + 1)
  gluingCompatibilityObligation : Type (u + 1)

end

end Boundary
