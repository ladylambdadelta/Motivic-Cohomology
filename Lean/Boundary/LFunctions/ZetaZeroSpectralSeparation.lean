import Boundary.LFunctions.ZetaZeroSideContribution
import Boundary.LFunctions.ZetaAdmissibleSpectralInterpolation

/-!
# Finite spectral separation on zero orbits

This file owns the finite spectral interpolation step used to separate an
off-critical completed-zero orbit by an admissible autocorrelation probe.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The finite spectral sample set attached to a centered zero orbit. -/
def zetaZeroOrbitSpectralSampleFinset (ρ : ℂ) : Finset ℂ :=
  (zetaZeroOrbitFinset ρ).image zetaCenteredZero

/-- Membership in the centered zero orbit gives membership of the centered coordinate in the
finite spectral sample set. -/
theorem zetaCenteredZero_mem_zeroOrbitSpectralSampleFinset
    (ρ η : ℂ) (hη : η ∈ zetaZeroOrbitFinset ρ) :
    zetaCenteredZero η ∈ zetaZeroOrbitSpectralSampleFinset ρ := by
  unfold zetaZeroOrbitSpectralSampleFinset
  exact Finset.mem_image.mpr ⟨η, hη, rfl⟩

/-- The finite spectral interpolation layer supplies an autocorrelation probe whose
spectral samples are one on the centered zero orbit. -/
theorem exists_zeroOrbit_autocorrelation_unitSpectralSamples
    (ρ : ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ →
        zetaSpectralEval (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (zetaCenteredZero η) = 1 := by
  rcases
    ZetaAdmissibleFunction.exists_autocorrelation_spectralEval_one_on_finset
      (zetaZeroOrbitSpectralSampleFinset ρ) with
    ⟨f, hf⟩
  exact ⟨f, fun η hη =>
    hf (zetaCenteredZero η)
      (zetaCenteredZero_mem_zeroOrbitSpectralSampleFinset ρ η hη)⟩

/-- A nonzero real part prevents a zero from colliding with its reflected orbit face. -/
theorem zetaZeroOrbit_self_ne_neg_of_re_ne_zero
    (ρ : ℂ) (hρre : ρ.re ≠ 0) :
    ρ ≠ -ρ := by
  intro hρneg
  have hre : ρ.re = (-ρ).re :=
    congrArg Complex.re hρneg
  have hneg_re : (-ρ).re = -ρ.re :=
    Complex.neg_re ρ
  have hself_neg : ρ.re = -ρ.re :=
    hre.trans hneg_re
  have htwo_zero : ρ.re + ρ.re = 0 := by
    calc
      ρ.re + ρ.re = -ρ.re + ρ.re := by
        exact congrArg (fun x : ℝ => x + ρ.re) hself_neg
      _ = 0 := by
        exact neg_add_cancel ρ.re
  have htwo : (2 : ℝ) * ρ.re = 0 := by
    exact (two_mul ρ.re).symm.trans htwo_zero
  have htwo_ne : (2 : ℝ) ≠ 0 := by
    exact two_ne_zero
  exact hρre (eq_zero_of_mul_eq_zero_left htwo htwo_ne)

/-- The reflected face is not already present in the singleton positive face. -/
theorem zetaZeroOrbit_neg_not_mem_singleton_self
    (ρ : ℂ) (hρre : ρ.re ≠ 0) :
    -ρ ∉ ({ρ} : Finset ℂ) := by
  intro hmem
  have hneg_eq : -ρ = ρ :=
    Finset.mem_singleton.mp hmem
  exact zetaZeroOrbit_self_ne_neg_of_re_ne_zero ρ hρre hneg_eq.symm

/-- The two-point zero orbit sum is the sum over the two distinct reflected faces. -/
theorem zetaZeroOrbitContribution_eq_self_add_neg
    (ρ : ℂ) (hρre : ρ.re ≠ 0) (φ : ZetaAdmissibleFunction) :
    zetaZeroOrbitContribution ρ φ =
      zetaZeroSideContribution ρ φ + zetaZeroSideContribution (-ρ) φ := by
  unfold zetaZeroOrbitContribution
  unfold zetaZeroOrbitFinset
  calc
    (insert ρ (insert (-ρ) ∅)).sum (fun η => zetaZeroSideContribution η φ) =
        zetaZeroSideContribution ρ φ +
          (insert (-ρ) ∅).sum (fun η => zetaZeroSideContribution η φ) := by
      exact Finset.sum_insert
        (by
          intro hmem
          have hneg_eq : ρ = -ρ :=
            Finset.mem_singleton.mp hmem
          exact zetaZeroOrbit_self_ne_neg_of_re_ne_zero ρ hρre hneg_eq)
    _ =
        zetaZeroSideContribution ρ φ + zetaZeroSideContribution (-ρ) φ := by
      exact congrArg
        (fun x : ℂ => zetaZeroSideContribution ρ φ + x)
        (Finset.sum_singleton (fun η => zetaZeroSideContribution η φ) (-ρ))

/-- A unit spectral sample makes the single zero-side contribution equal to minus the
analytic multiplicity. -/
theorem zetaZeroSideContribution_eq_neg_multiplicity_of_unitSample
    (η : ℂ) (φ : ZetaAdmissibleFunction)
    (hsample : zetaSpectralEval φ (zetaCenteredZero η) = 1) :
    zetaZeroSideContribution η φ = - (zetaZeroMultiplicity η : ℂ) := by
  calc
    zetaZeroSideContribution η φ =
        - (zetaZeroMultiplicity η : ℂ) *
          zetaSpectralEval φ (zetaCenteredZero η) := by
      exact zetaZeroSideContribution_def η φ
    _ = - (zetaZeroMultiplicity η : ℂ) * 1 := by
      exact congrArg
        (fun x : ℂ => - (zetaZeroMultiplicity η : ℂ) * x)
        hsample
    _ = - (zetaZeroMultiplicity η : ℂ) := by
      exact mul_one (- (zetaZeroMultiplicity η : ℂ))

/-- The real part of a negative natural multiplicity, embedded in `ℂ`, is the negative
real multiplicity. -/
theorem complex_re_neg_natMultiplicity
    (m : ℕ) :
    Complex.re (-(m : ℂ)) = - (m : ℝ) := by
  calc
    Complex.re (-(m : ℂ)) = - Complex.re (m : ℂ) := by
      exact Complex.neg_re (m : ℂ)
    _ = - (m : ℝ) := by
      exact congrArg Neg.neg (Complex.ofReal_re (m : ℝ))

/-- A unit spectral sample makes the real single-zero contribution equal to minus the
analytic multiplicity. -/
theorem zetaZeroSideContribution_re_eq_neg_multiplicity_of_unitSample
    (η : ℂ) (φ : ZetaAdmissibleFunction)
    (hsample : zetaSpectralEval φ (zetaCenteredZero η) = 1) :
    Complex.re (zetaZeroSideContribution η φ) =
      - (zetaZeroMultiplicity η : ℝ) := by
  calc
    Complex.re (zetaZeroSideContribution η φ) =
        Complex.re (-(zetaZeroMultiplicity η : ℂ)) := by
      exact congrArg Complex.re
        (zetaZeroSideContribution_eq_neg_multiplicity_of_unitSample η φ hsample)
    _ = - (zetaZeroMultiplicity η : ℝ) := by
      exact complex_re_neg_natMultiplicity (zetaZeroMultiplicity η)

/-- Unit spectral samples on the two reflected faces identify the real orbit contribution
with the sum of the two negative multiplicities. -/
theorem zetaZeroOrbitContributionRe_eq_neg_multiplicity_add_neg_multiplicity
    (ρ : ℂ)
    (hρre : ρ.re ≠ 0)
    (φ : ZetaAdmissibleFunction)
    (hsample :
      ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ →
        zetaSpectralEval φ (zetaCenteredZero η) = 1) :
    zetaZeroOrbitContributionRe ρ φ =
      - (zetaZeroMultiplicity ρ : ℝ) +
        - (zetaZeroMultiplicity (-ρ) : ℝ) := by
  calc
    zetaZeroOrbitContributionRe ρ φ =
        Complex.re (zetaZeroOrbitContribution ρ φ) := by
      rfl
    _ =
        Complex.re
          (zetaZeroSideContribution ρ φ +
            zetaZeroSideContribution (-ρ) φ) := by
      exact congrArg Complex.re
        (zetaZeroOrbitContribution_eq_self_add_neg ρ hρre φ)
    _ =
        Complex.re (zetaZeroSideContribution ρ φ) +
          Complex.re (zetaZeroSideContribution (-ρ) φ) := by
      exact Complex.add_re
        (zetaZeroSideContribution ρ φ)
        (zetaZeroSideContribution (-ρ) φ)
    _ =
        - (zetaZeroMultiplicity ρ : ℝ) +
          - (zetaZeroMultiplicity (-ρ) : ℝ) := by
      exact congrArg₂ HAdd.hAdd
        (zetaZeroSideContribution_re_eq_neg_multiplicity_of_unitSample
          ρ φ (hsample ρ (zetaZeroOrbitFinset_mem_self ρ)))
        (zetaZeroSideContribution_re_eq_neg_multiplicity_of_unitSample
          (-ρ) φ (hsample (-ρ) (zetaZeroOrbitFinset_mem_neg ρ)))

/-- The sum of the two negative multiplicities on a completed reflected orbit is strictly
negative. -/
theorem neg_multiplicity_add_neg_multiplicity_lt_zero_of_orbitCompletedZero
    (ρ : ℂ)
    (hρ : ZetaCompletedZero ρ)
    (horbit : ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ → ZetaCompletedZero η) :
    - (zetaZeroMultiplicity ρ : ℝ) +
        - (zetaZeroMultiplicity (-ρ) : ℝ) < 0 := by
  have hρmult_pos_nat : 0 < zetaZeroMultiplicity ρ :=
    zetaZeroMultiplicity_pos_of_completedZero ⟨ρ, hρ⟩
  have hneg_mult_pos_nat : 0 < zetaZeroMultiplicity (-ρ) :=
    zetaZeroMultiplicity_pos_of_completedZero
      ⟨-ρ, horbit (-ρ) (zetaZeroOrbitFinset_mem_neg ρ)⟩
  have hρmult_pos : 0 < (zetaZeroMultiplicity ρ : ℝ) :=
    Nat.cast_pos.mpr hρmult_pos_nat
  have hneg_mult_pos : 0 < (zetaZeroMultiplicity (-ρ) : ℝ) :=
    Nat.cast_pos.mpr hneg_mult_pos_nat
  have hleft : - (zetaZeroMultiplicity ρ : ℝ) < 0 :=
    neg_lt_zero.mpr hρmult_pos
  have hright : - (zetaZeroMultiplicity (-ρ) : ℝ) < 0 :=
    neg_lt_zero.mpr hneg_mult_pos
  have hsum :
      - (zetaZeroMultiplicity ρ : ℝ) +
          - (zetaZeroMultiplicity (-ρ) : ℝ) < 0 + 0 :=
    add_lt_add hleft hright
  exact hsum.trans_eq (add_zero 0)

/-- Unit spectral samples on an off-critical completed-zero orbit force the signed
multiplicity-weighted orbit contribution to be strictly negative. -/
theorem zetaZeroOrbitContributionRe_lt_zero_of_unitSpectralSamples
    (ρ : ℂ)
    (hρ : ZetaCompletedZero ρ)
    (hρre : ρ.re ≠ 0)
    (horbit : ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ → ZetaCompletedZero η)
    (φ : ZetaAdmissibleFunction)
    (hsample :
      ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ →
        zetaSpectralEval φ (zetaCenteredZero η) = 1) :
    zetaZeroOrbitContributionRe ρ φ < 0 := by
  exact Eq.subst
    (motive := fun x : ℝ => x < 0)
    (zetaZeroOrbitContributionRe_eq_neg_multiplicity_add_neg_multiplicity
      ρ hρre φ hsample).symm
    (neg_multiplicity_add_neg_multiplicity_lt_zero_of_orbitCompletedZero
      ρ hρ horbit)

/-- Finite spectral orbit separation at an off-critical centered completed zero.

The spectral interpolation layer supplies a seed whose completed autocorrelation
has a strictly negative signed multiplicity-weighted contribution on the
two-point centered zero orbit. -/
theorem exists_zeroOrbit_autocorrelation_finiteSpectralSeparator_owner
    (ρ : ℂ)
    (hρ : ZetaCompletedZero ρ)
    (hρre : ρ.re ≠ 0)
    (horbit : ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ → ZetaCompletedZero η) :
    ∃ f : ZetaAdmissibleFunction,
      zetaZeroOrbitContributionRe ρ
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) < 0 := by
  rcases exists_zeroOrbit_autocorrelation_unitSpectralSamples ρ with
    ⟨f, hsample⟩
  exact ⟨f,
    zetaZeroOrbitContributionRe_lt_zero_of_unitSpectralSamples
      ρ hρ hρre horbit
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)
      hsample⟩

end

end LFunctions
end Boundary
