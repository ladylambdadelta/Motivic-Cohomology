import Boundary.Hodge.PureHodgeStructure

/-!
# Mixed Hodge structures

This file records the linear-algebra shape of a mixed Hodge structure: a
rational vector space with an increasing weight filtration, a complex vector
space with a decreasing Hodge filtration, and pure Hodge structures on the
weight-graded pieces.
-/

universe u

namespace Boundary
namespace Hodge

/-- A mixed Hodge structure, at the level of filtrations and pure graded
pieces.  The comparison map between rational complexification and the complex
carrier is left for the realization layer, where the relevant tensor product
objects are owned. -/
structure MixedHodgeStructure where
  rationalCarrier : Type u
  rationalAddCommGroup : AddCommGroup rationalCarrier
  rationalModule : Module ℚ rationalCarrier
  rationalFinite : Module.Finite ℚ rationalCarrier
  complexCarrier : Type u
  complexAddCommGroup : AddCommGroup complexCarrier
  complexModule : Module ℂ complexCarrier
  complexFinite : Module.Finite ℂ complexCarrier
  weightFiltration : IncreasingFiltration ℚ rationalCarrier
  hodgeFiltration : DecreasingFiltration ℂ complexCarrier
  gradedPiece : ℤ → PureHodgeStructure
  gradedPiece_weight : ∀ n : ℤ, (gradedPiece n).weight = n

namespace MixedHodgeStructure

attribute [instance] rationalAddCommGroup rationalModule rationalFinite
attribute [instance] complexAddCommGroup complexModule complexFinite

theorem weightFiltration_monotone (M : MixedHodgeStructure)
    ⦃m n : ℤ⦄ (hmn : m ≤ n) :
    M.weightFiltration.step m ≤ M.weightFiltration.step n :=
  M.weightFiltration.monotone hmn

theorem hodgeFiltration_antitone (M : MixedHodgeStructure)
    ⦃p q : ℤ⦄ (hpq : p ≤ q) :
    M.hodgeFiltration.step q ≤ M.hodgeFiltration.step p :=
  M.hodgeFiltration.antitone hpq

theorem gradedPiece_is_pure_of_weight (M : MixedHodgeStructure) (n : ℤ) :
    (M.gradedPiece n).weight = n :=
  M.gradedPiece_weight n

@[simp]
theorem gradedPiece_hodgeNumber_eq_zero_of_ne (M : MixedHodgeStructure)
    {n p q : ℤ} (hpq : p + q ≠ n) :
    (M.gradedPiece n).hodgeNumber p q = 0 := by
  exact
    PureHodgeStructure.hodgeNumber_eq_zero_of_weight_ne
      (M.gradedPiece n) (by simpa [M.gradedPiece_is_pure_of_weight n] using hpq)

end MixedHodgeStructure

end Hodge
end Boundary
