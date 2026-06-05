import Boundary.Hodge.FilteredVectorSpace
import Boundary.Hodge.GradedVectorSpace
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Pure Hodge structures

The first project-local Hodge structure API.  A pure Hodge structure is bundled
as a finite-dimensional complex vector space with genuine `(p,q)` subspaces and
a decreasing Hodge filtration related to those pieces.

This is intentionally the linear-algebra layer only: it does not assert that
the structure has arisen from de Rham, Betti, or analytic cohomology.
-/

universe u

namespace Boundary
namespace Hodge

/-- A pure Hodge structure at the linear-algebra level. -/
structure PureHodgeStructure where
  weight : ℤ
  carrier : Type u
  addCommGroup : AddCommGroup carrier
  complexModule : Module ℂ carrier
  finite : Module.Finite ℂ carrier
  hodgePiece : ℤ × ℤ → Submodule ℂ carrier
  hodgePiece_free : ∀ pq, Module.Free ℂ (hodgePiece pq)
  hodgePiece_finite : ∀ pq, Module.Finite ℂ (hodgePiece pq)
  hodgeFiltration : DecreasingFiltration ℂ carrier
  piece_le_filtration :
    ∀ ⦃p r s : ℤ⦄, p ≤ r → hodgePiece (r, s) ≤ hodgeFiltration.step p
  weight_zero :
    ∀ ⦃p q : ℤ⦄, p + q ≠ weight → hodgePiece (p, q) = ⊥

namespace PureHodgeStructure

attribute [instance] addCommGroup complexModule finite hodgePiece_free hodgePiece_finite

/-- The Hodge number `h^{p,q}` of a pure Hodge structure. -/
noncomputable def hodgeNumber (H : PureHodgeStructure) (p q : ℤ) : ℕ :=
  Module.finrank ℂ (H.hodgePiece (p, q))

/-- The bigraded rank profile of a pure Hodge structure. -/
noncomputable def rankProfile (H : PureHodgeStructure) : BigradedRankProfile :=
  fun pq => H.hodgeNumber pq.1 pq.2

theorem hodgePiece_le_filtration (H : PureHodgeStructure)
    ⦃p r s : ℤ⦄ (hpr : p ≤ r) :
    H.hodgePiece (r, s) ≤ H.hodgeFiltration.step p :=
  H.piece_le_filtration hpr

theorem hodgeFiltration_antitone (H : PureHodgeStructure)
    ⦃p q : ℤ⦄ (hpq : p ≤ q) :
    H.hodgeFiltration.step q ≤ H.hodgeFiltration.step p :=
  H.hodgeFiltration.antitone hpq

theorem hodgePiece_eq_bot_of_weight_ne (H : PureHodgeStructure)
    ⦃p q : ℤ⦄ (hpq : p + q ≠ H.weight) :
    H.hodgePiece (p, q) = ⊥ :=
  H.weight_zero hpq

@[simp]
theorem hodgeNumber_eq_zero_of_weight_ne (H : PureHodgeStructure)
    ⦃p q : ℤ⦄ (hpq : p + q ≠ H.weight) :
    H.hodgeNumber p q = 0 := by
  rw [hodgeNumber, H.hodgePiece_eq_bot_of_weight_ne hpq]
  exact finrank_bot ℂ H.carrier

/-- Product of pure Hodge structures of the same weight.  This is the
linear-algebra direct sum model on product carriers. -/
def prod (H G : PureHodgeStructure) (hwt : H.weight = G.weight) :
    PureHodgeStructure where
  weight := H.weight
  carrier := H.carrier × G.carrier
  addCommGroup := inferInstance
  complexModule := inferInstance
  finite := inferInstance
  hodgePiece := fun pq => submoduleProd ℂ H.carrier (H.hodgePiece pq) (G.hodgePiece pq)
  hodgePiece_free := fun pq => by
    letI := H.hodgePiece_free pq
    letI := G.hodgePiece_free pq
    exact free_submoduleProd ℂ H.carrier (H.hodgePiece pq) (G.hodgePiece pq)
  hodgePiece_finite := fun pq => by
    letI := H.hodgePiece_finite pq
    letI := G.hodgePiece_finite pq
    exact finite_submoduleProd ℂ H.carrier (H.hodgePiece pq) (G.hodgePiece pq)
  hodgeFiltration :=
    { step := fun p =>
        submoduleProd ℂ H.carrier (H.hodgeFiltration.step p) (G.hodgeFiltration.step p)
      antitone' := by
        intro p q hpq x hx
        exact ⟨H.hodgeFiltration.antitone hpq hx.1,
          G.hodgeFiltration.antitone hpq hx.2⟩ }
  piece_le_filtration := by
    intro p r s hpr x hx
    exact ⟨H.hodgePiece_le_filtration hpr hx.1,
      G.hodgePiece_le_filtration hpr hx.2⟩
  weight_zero := by
    intro p q hpq
    ext x
    constructor
    · intro hx
      have hH : H.hodgePiece (p, q) = ⊥ := H.hodgePiece_eq_bot_of_weight_ne hpq
      have hG : G.hodgePiece (p, q) = ⊥ := by
        exact G.hodgePiece_eq_bot_of_weight_ne (by simpa [← hwt] using hpq)
      have hx₁ : x.1 = 0 := by
        exact (Submodule.mem_bot ℂ).1 (by simpa [hH] using hx.1)
      have hx₂ : x.2 = 0 := by
        exact (Submodule.mem_bot ℂ).1 (by simpa [hG] using hx.2)
      exact (Submodule.mem_bot ℂ).2 (Prod.ext hx₁ hx₂)
    · intro hx
      rw [Submodule.mem_bot] at hx
      rw [hx]
      simp [submoduleProd]

@[simp]
theorem hodgeNumber_prod (H G : PureHodgeStructure) (hwt : H.weight = G.weight)
    (p q : ℤ) :
    (H.prod G hwt).hodgeNumber p q = H.hodgeNumber p q + G.hodgeNumber p q := by
  simpa [hodgeNumber, prod] using
    finrank_submoduleProd ℂ H.carrier (H.hodgePiece (p, q)) (G.hodgePiece (p, q))

@[simp]
theorem rankProfile_prod (H G : PureHodgeStructure) (hwt : H.weight = G.weight) :
    (H.prod G hwt).rankProfile =
      BigradedRankProfile.add H.rankProfile G.rankProfile := by
  funext pq
  rcases pq with ⟨p, q⟩
  simp [rankProfile]

end PureHodgeStructure

end Hodge
end Boundary
