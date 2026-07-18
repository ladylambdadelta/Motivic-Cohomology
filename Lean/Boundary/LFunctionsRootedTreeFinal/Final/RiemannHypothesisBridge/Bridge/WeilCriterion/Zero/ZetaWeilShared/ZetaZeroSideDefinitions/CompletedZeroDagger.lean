import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.Core

/-!
# Completed-zero dagger transport

This owner packages the negative-conjugate involution on completed zeta zeros.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ComplexConjugate

/-- The completed-zero locus is stable under the autocorrelation dagger
involution. -/
theorem zetaCompletedZero_neg_star
    {ρ : ℂ}
    (hρ : ZetaCompletedZero ρ) :
    ZetaCompletedZero (-star ρ) := by
  have hconj : ZetaCompletedZero (conj ρ) := zetaCompletedZero_conj hρ
  have hneg : ZetaCompletedZero (-(conj ρ)) := zetaCompletedZero_neg hconj
  exact hneg

/-- Dagger transport on the completed-zero subtype. -/
def zetaCompletedZeroDagger :
    {ρ : ℂ // ZetaCompletedZero ρ} → {ρ : ℂ // ZetaCompletedZero ρ} :=
  fun ρ => ⟨-star (ρ : ℂ), zetaCompletedZero_neg_star ρ.2⟩

/-- The underlying complex number of dagger transport is the expected
negative conjugate. -/
theorem zetaCompletedZeroDagger_coe
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    (zetaCompletedZeroDagger ρ : ℂ) = -star (ρ : ℂ) := by
  rfl

/-- Dagger transport is an involution on completed zeros. -/
theorem zetaCompletedZeroDagger_involutive :
    Function.Involutive zetaCompletedZeroDagger := by
  intro ρ
  apply Subtype.ext
  calc
    ((zetaCompletedZeroDagger (zetaCompletedZeroDagger ρ) :
      {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ) =
        -star (-star (ρ : ℂ)) := by
          rfl
    _ = -(-star (star (ρ : ℂ))) := by
          exact congrArg Neg.neg (star_neg (star (ρ : ℂ)))
    _ = -(-((ρ : ℂ))) := by
          exact
            congrArg Neg.neg
              (congrArg Neg.neg (star_star (ρ : ℂ)))
    _ = (ρ : ℂ) := neg_neg (ρ : ℂ)

/-- Dagger transport is injective on the completed-zero index type.  This is
the reindexing form of involutivity used by weighted tail estimates. -/
theorem zetaCompletedZeroDagger_injective :
    Function.Injective zetaCompletedZeroDagger := by
  intro left right hleftRight
  calc
    left = zetaCompletedZeroDagger (zetaCompletedZeroDagger left) :=
      (zetaCompletedZeroDagger_involutive left).symm
    _ = zetaCompletedZeroDagger (zetaCompletedZeroDagger right) := by
      exact congrArg zetaCompletedZeroDagger hleftRight
    _ = right := zetaCompletedZeroDagger_involutive right

end
end LFunctions
end Boundary
