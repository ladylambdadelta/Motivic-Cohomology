import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.FiniteWindow.Core
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissibleInterpolation.ZetaAdmissibleProbe.Owner

/-!
# Finite-support completed-zero tomography

This file owns the finite-dimensional analytic separation used by completed-zero
annihilators.  Multiplicity-weighted completed-zero coefficients define a finite
exponential distribution, and its Laplace pairing is exactly the finite-window
zero-side annihilator.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction
namespace FiniteWindow

open scoped ENNReal

noncomputable def completedZeroFiniteExponentialCoefficient
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta) : S → ℂ :=
  fun eta : S =>
    -((zetaZeroMultiplicity (eta : ℂ) : ℂ)) *
      b ⟨(eta : ℂ), hS eta eta.property⟩

theorem completedZeroFiniteExponentialCoefficient_ne_zero
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
    (rho : S)
    (hrho : b ⟨(rho : ℂ), hS rho rho.property⟩ ≠ 0) :
    completedZeroFiniteExponentialCoefficient b S hS rho ≠ 0 := by
  have hmultiplicityPositive : 0 < zetaZeroMultiplicity (rho : ℂ) :=
    zetaZeroMultiplicity_pos_of_completedZero
      ⟨(rho : ℂ), hS rho rho.property⟩
  have hmultiplicityNatNonzero : zetaZeroMultiplicity (rho : ℂ) ≠ 0 :=
    Nat.ne_of_gt hmultiplicityPositive
  have hmultiplicityComplexNonzero :
      (zetaZeroMultiplicity (rho : ℂ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hmultiplicityNatNonzero
  have hnegativeMultiplicityNonzero :
      -((zetaZeroMultiplicity (rho : ℂ) : ℂ)) ≠ 0 :=
    neg_ne_zero.mpr hmultiplicityComplexNonzero
  unfold completedZeroFiniteExponentialCoefficient
  exact mul_ne_zero hnegativeMultiplicityNonzero hrho

theorem zetaCompletedZeroSideAnnihilatorFiniteWindow_eq_finiteExponentialLaplacePairing
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f =
      finiteExponentialLaplacePairing S
        (completedZeroFiniteExponentialCoefficient b S hS) f := by
  unfold zetaCompletedZeroSideAnnihilatorFiniteWindow
  unfold finiteExponentialLaplacePairing
  apply Finset.sum_congr rfl
  intro eta heta
  have hspectralLaplace :
      zetaSpectralEval f (eta : ℂ) =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' (eta : ℂ) :=
    zetaSpectralEval_eq_laplace f (eta : ℂ)
  unfold completedZeroFiniteExponentialCoefficient
  unfold zetaZeroSideContribution
  have hassociate :
      b ⟨(eta : ℂ), hS eta eta.property⟩ *
          (-((zetaZeroMultiplicity (eta : ℂ) : ℂ)) *
            zetaSpectralEval f (eta : ℂ)) =
        (b ⟨(eta : ℂ), hS eta eta.property⟩ *
          -((zetaZeroMultiplicity (eta : ℂ) : ℂ))) *
            zetaSpectralEval f (eta : ℂ) :=
    (mul_assoc
      (b ⟨(eta : ℂ), hS eta eta.property⟩)
      (-((zetaZeroMultiplicity (eta : ℂ) : ℂ)))
      (zetaSpectralEval f (eta : ℂ))).symm
  have hcoefficientCommutes :
      (b ⟨(eta : ℂ), hS eta eta.property⟩ *
          -((zetaZeroMultiplicity (eta : ℂ) : ℂ))) *
            zetaSpectralEval f (eta : ℂ) =
        (-((zetaZeroMultiplicity (eta : ℂ) : ℂ)) *
          b ⟨(eta : ℂ), hS eta eta.property⟩) *
            zetaSpectralEval f (eta : ℂ) :=
    congrArg
      (fun value : ℂ => value * zetaSpectralEval f (eta : ℂ))
      (mul_comm
        (b ⟨(eta : ℂ), hS eta eta.property⟩)
        (-((zetaZeroMultiplicity (eta : ℂ) : ℂ))))
  have hspectralCommutes :
      (-((zetaZeroMultiplicity (eta : ℂ) : ℂ)) *
          b ⟨(eta : ℂ), hS eta eta.property⟩) *
            zetaSpectralEval f (eta : ℂ) =
        zetaSpectralEval f (eta : ℂ) *
          (-((zetaZeroMultiplicity (eta : ℂ) : ℂ)) *
            b ⟨(eta : ℂ), hS eta eta.property⟩) :=
    mul_comm
      (-((zetaZeroMultiplicity (eta : ℂ) : ℂ)) *
        b ⟨(eta : ℂ), hS eta eta.property⟩)
      (zetaSpectralEval f (eta : ℂ))
  have hlaplaceSubstitution :
      zetaSpectralEval f (eta : ℂ) *
          (-((zetaZeroMultiplicity (eta : ℂ) : ℂ)) *
            b ⟨(eta : ℂ), hS eta eta.property⟩) =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' (eta : ℂ) *
          (-((zetaZeroMultiplicity (eta : ℂ) : ℂ)) *
            b ⟨(eta : ℂ), hS eta eta.property⟩) :=
    congrArg
      (fun value : ℂ =>
        value *
          (-((zetaZeroMultiplicity (eta : ℂ) : ℂ)) *
            b ⟨(eta : ℂ), hS eta eta.property⟩))
      hspectralLaplace
  exact
    Eq.trans hassociate
      (Eq.trans hcoefficientCommutes
        (Eq.trans hspectralCommutes hlaplaceSubstitution))

theorem exists_probe_with_nonzero_finiteWindowAnnihilator
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
    (rho : S)
    (hrho : b ⟨(rho : ℂ), hS rho rho.property⟩ ≠ 0) :
    ∃ f : ZetaAdmissibleFunction,
      zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f ≠ 0 := by
  have hcoefficient :
      completedZeroFiniteExponentialCoefficient b S hS rho ≠ 0 :=
    completedZeroFiniteExponentialCoefficient_ne_zero b S hS rho hrho
  have hsomeCoefficient :
      ∃ eta : S,
        completedZeroFiniteExponentialCoefficient b S hS eta ≠ 0 :=
    ⟨rho, hcoefficient⟩
  match admissibleProbes_separate_finiteExponentialDistributions S
      (completedZeroFiniteExponentialCoefficient b S hS) hsomeCoefficient with
  | ⟨f, hpairing⟩ =>
      exact
        ⟨f, fun hfiniteWindow =>
          hpairing
            ((zetaCompletedZeroSideAnnihilatorFiniteWindow_eq_finiteExponentialLaplacePairing
              b S hS f).symm.trans hfiniteWindow)⟩

end FiniteWindow
end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
