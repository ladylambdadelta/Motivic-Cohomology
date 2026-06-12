import Boundary.LFunctions.ZetaZeroTail
import Boundary.LFunctions.ZetaWeilShared

/-!
# Boundary zero-side orbit remainder

This file packages the orbit remainder as the tail specialized to the orbit of
the chosen zero.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The orbit remainder is the tail after removing the orbit of the chosen zero. -/
theorem zetaZeroOrbitRemainder_eq
    (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroOrbitRemainder ρ φ =
      zetaZeroTail (zetaZeroOrbitFinset ρ) φ := by
  rfl

/-- The real-valued orbit remainder is the real part of the complex one. -/
theorem zetaZeroOrbitRemainderRe_eq
    (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroOrbitRemainderRe ρ φ =
      Complex.re (zetaZeroOrbitRemainder ρ φ) := by
  rfl

/-- Complex zero-side excision for the functional-equation orbit of one zero. -/
theorem zetaCompletedZeroSideSum_eq_orbitContribution_add_orbitRemainder
    (ρ : ℂ) (φ : ZetaAdmissibleFunction)
    (hρ : ZetaCompletedZero ρ)
    (horbit : ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ → ZetaCompletedZero η) :
    (∑' η : {η : ℂ // ZetaCompletedZero η},
        zetaZeroSideContribution (η : ℂ) φ) =
      zetaZeroOrbitContribution ρ φ + zetaZeroOrbitRemainder ρ φ := by
  have htail :
      (∑' η : {η : ℂ // ZetaCompletedZero η},
          zetaZeroSideContribution (η : ℂ) φ) =
        (∑ η in zetaZeroOrbitFinset ρ, zetaZeroSideContribution η φ) +
          zetaZeroTail (zetaZeroOrbitFinset ρ) φ :=
    zetaCompletedZeroSideSum_eq_finite_add_tail
      (zetaZeroOrbitFinset ρ) φ horbit
  have horbit_sum :
      zetaZeroOrbitContribution ρ φ =
        ∑ η in zetaZeroOrbitFinset ρ, zetaZeroSideContribution η φ :=
    zetaZeroOrbitContribution_eq_sum ρ φ
  have hremainder :
      zetaZeroOrbitRemainder ρ φ =
        zetaZeroTail (zetaZeroOrbitFinset ρ) φ :=
    zetaZeroOrbitRemainder_eq ρ φ
  calc
    (∑' η : {η : ℂ // ZetaCompletedZero η},
        zetaZeroSideContribution (η : ℂ) φ) =
        (∑ η in zetaZeroOrbitFinset ρ, zetaZeroSideContribution η φ) +
          zetaZeroTail (zetaZeroOrbitFinset ρ) φ := htail
    _ = zetaZeroOrbitContribution ρ φ +
          zetaZeroTail (zetaZeroOrbitFinset ρ) φ := by
      exact congrArg
        (fun x : ℂ => x + zetaZeroTail (zetaZeroOrbitFinset ρ) φ)
        horbit_sum.symm
    _ = zetaZeroOrbitContribution ρ φ + zetaZeroOrbitRemainder ρ φ := by
      exact congrArg
        (fun x : ℂ => zetaZeroOrbitContribution ρ φ + x)
        hremainder.symm

/-- The completed zero-side real scalar splits into the chosen finite zero orbit and the
complementary orbit remainder.

This is the zero-side owner decomposition: after a finite functional-equation orbit has been
isolated, the completed zero-side `tsum` is the finite orbit contribution plus the tail over
all remaining zeros. -/
theorem zetaCompletedZeroSideRe_eq_orbitContribution_add_orbitRemainderRe
    (ρ : ℂ) (φ : ZetaAdmissibleFunction)
    (hρ : ZetaCompletedZero ρ)
    (horbit : ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ → ZetaCompletedZero η) :
    zetaCompletedZeroSideRe φ =
      zetaZeroOrbitContributionRe ρ φ + zetaZeroOrbitRemainderRe ρ φ := by
  have hcomplex :
      (∑' η : {η : ℂ // ZetaCompletedZero η},
          zetaZeroSideContribution (η : ℂ) φ) =
        zetaZeroOrbitContribution ρ φ + zetaZeroOrbitRemainder ρ φ :=
    zetaCompletedZeroSideSum_eq_orbitContribution_add_orbitRemainder
      ρ φ hρ horbit
  unfold zetaCompletedZeroSideRe
  unfold zetaZeroOrbitContributionRe
  unfold zetaZeroOrbitRemainderRe
  calc
    Complex.re
        (∑' η : {η : ℂ // ZetaCompletedZero η},
          zetaZeroSideContribution (η : ℂ) φ) =
        Complex.re (zetaZeroOrbitContribution ρ φ + zetaZeroOrbitRemainder ρ φ) := by
      exact congrArg Complex.re hcomplex
    _ = Complex.re (zetaZeroOrbitContribution ρ φ) +
          Complex.re (zetaZeroOrbitRemainder ρ φ) := by
      exact Complex.add_re
        (zetaZeroOrbitContribution ρ φ)
        (zetaZeroOrbitRemainder ρ φ)

end
end LFunctions
end Boundary
