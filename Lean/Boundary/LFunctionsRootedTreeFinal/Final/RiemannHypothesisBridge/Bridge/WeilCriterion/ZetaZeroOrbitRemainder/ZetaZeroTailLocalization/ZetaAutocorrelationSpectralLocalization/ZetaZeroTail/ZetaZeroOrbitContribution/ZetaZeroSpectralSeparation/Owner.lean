import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroSideContribution.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CenteredZeros.CriticalStrip.Owner

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

/-- The finite spectral sample set attached to the uncentered zero-side
contribution coordinates of a zero orbit. -/
def zetaZeroOrbitContributionSpectralSampleFinset (ρ : ℂ) : Finset ℂ :=
  zetaZeroOrbitFinset ρ

/-- The raw spectral sample set for an orbit, closed under the autocorrelation dagger
operation. -/
def zetaZeroOrbitDaggerClosedSpectralSampleFinset
    (ρ : ℂ) : Finset ℂ :=
  ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset
    (zetaZeroOrbitContributionSpectralSampleFinset ρ)

/-- The finite completed-zero window attached to the dagger closure of an orbit sample set. -/
def zetaZeroOrbitDaggerClosedCompletedZeroFinset
    (ρ : ℂ) : Finset ℂ :=
  ZetaAdmissibleFunction.completedZeroDaggerClosureFinset
    (zetaZeroOrbitDaggerClosedSpectralSampleFinset ρ)

/-- Every point of the finite orbit dagger window is a completed zero. -/
theorem zetaZeroOrbitDaggerClosedCompletedZeroFinset_mem_completedZero
    (ρ z : ℂ)
    (hz : z ∈ zetaZeroOrbitDaggerClosedCompletedZeroFinset ρ) :
    ZetaCompletedZero z := by
  exact
    ZetaAdmissibleFunction.completedZeroDaggerClosureFinset_mem_completedZero
      (zetaZeroOrbitDaggerClosedSpectralSampleFinset ρ)
      z
      hz

/-- A completed zero outside the finite orbit dagger window is disjoint from the full
dagger closure of the raw orbit samples. -/
theorem zetaCompletedZero_not_mem_daggerClosedOrbitSamples_of_not_mem_orbitDaggerWindow
    (ρ z : ℂ)
    (hz : ZetaCompletedZero z)
    (hnot : z ∉ zetaZeroOrbitDaggerClosedCompletedZeroFinset ρ) :
    z ∉ ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset
      (zetaZeroOrbitDaggerClosedSpectralSampleFinset ρ) := by
  exact
    ZetaAdmissibleFunction.completedZero_not_mem_daggerClosedSpectralSampleFinset_of_not_mem_completedZeroDaggerClosure
      (zetaZeroOrbitDaggerClosedSpectralSampleFinset ρ)
      z
      hz
      hnot

/-- The orbit dagger window satisfies the raw separation contract consumed by finite-tail
Runge localization. -/
theorem zetaZeroOrbitDaggerClosedCompletedZeroFinset_rawSeparated
    (ρ : ℂ) :
    ∀ z : ℂ,
      ZetaCompletedZero z →
        z ∉ zetaZeroOrbitDaggerClosedCompletedZeroFinset ρ →
          z ∉ ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset
            (zetaZeroOrbitDaggerClosedSpectralSampleFinset ρ) := by
  intro z hz hnot
  exact
    zetaCompletedZero_not_mem_daggerClosedOrbitSamples_of_not_mem_orbitDaggerWindow
      ρ
      z
      hz
      hnot

/-- The distinguished completed zero belongs to its finite orbit dagger window. -/
theorem zetaZero_mem_zetaZeroOrbitDaggerClosedCompletedZeroFinset
    (ρ : ℂ)
    (hρ : ZetaCompletedZero ρ) :
    ρ ∈ zetaZeroOrbitDaggerClosedCompletedZeroFinset ρ := by
  apply Finset.mem_filter.mpr
  apply And.intro
  · exact
      ZetaAdmissibleFunction.mem_daggerClosedSpectralSampleFinset_self
        (zetaZeroOrbitDaggerClosedSpectralSampleFinset ρ)
        ρ
        (ZetaAdmissibleFunction.mem_daggerClosedSpectralSampleFinset_self
          (zetaZeroOrbitContributionSpectralSampleFinset ρ)
          ρ
          (zetaZeroOrbitFinset_mem_self ρ))
  · exact hρ

/-- Membership in the centered zero orbit gives membership of the centered coordinate in the
finite spectral sample set. -/
theorem zetaCenteredZero_mem_zeroOrbitSpectralSampleFinset
    (ρ η : ℂ) (hη : η ∈ zetaZeroOrbitFinset ρ) :
    zetaCenteredZero η ∈ zetaZeroOrbitSpectralSampleFinset ρ := by
  exact Finset.mem_image.mpr ⟨η, hη, rfl⟩

/-- Membership in the zero orbit gives membership in the uncentered
zero-side contribution sample set. -/
theorem zetaZeroOrbit_mem_contributionSpectralSampleFinset
    (ρ η : ℂ) (hη : η ∈ zetaZeroOrbitFinset ρ) :
    η ∈ zetaZeroOrbitContributionSpectralSampleFinset ρ := by
  exact hη

/-- The finite spectral interpolation layer supplies an autocorrelation probe whose
spectral samples are one on the centered zero orbit. -/
theorem exists_zeroOrbit_autocorrelation_unitSpectralSamples
    (ρ : ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ →
        zetaSpectralEval (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (zetaCenteredZero η) = 1 := by
  match
    ZetaAdmissibleFunction.exists_autocorrelation_spectralEval_one_on_finset
      (zetaZeroOrbitSpectralSampleFinset ρ) with
  | ⟨f, hf⟩ =>
      exact ⟨f, fun η hη =>
        hf (zetaCenteredZero η)
          (zetaCenteredZero_mem_zeroOrbitSpectralSampleFinset ρ η hη)⟩

/-- The finite spectral interpolation layer supplies an autocorrelation probe
whose uncentered spectral samples are one on the zero-side contribution orbit. -/
theorem exists_zeroOrbit_autocorrelation_unitContributionSpectralSamples
    (ρ : ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ →
        zetaSpectralEval (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          η = 1 := by
  match
    ZetaAdmissibleFunction.exists_autocorrelation_spectralEval_one_on_finset
      (zetaZeroOrbitContributionSpectralSampleFinset ρ) with
  | ⟨f, hf⟩ =>
      exact ⟨f, fun η hη =>
        hf η
          (zetaZeroOrbit_mem_contributionSpectralSampleFinset ρ η hη)⟩

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
    exact (two_mul ρ.re).trans htwo_zero
  have htwo_ne : (2 : ℝ) ≠ 0 := by
    exact two_ne_zero
  exact hρre (eq_zero_of_ne_zero_of_mul_left_eq_zero htwo_ne htwo)

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
  show
    (insert ρ (insert (-ρ) (∅ : Finset ℂ))).sum
        (fun η => zetaZeroSideContribution η φ) =
      zetaZeroSideContribution ρ φ + zetaZeroSideContribution (-ρ) φ
  calc
    (insert ρ (insert (-ρ) (∅ : Finset ℂ))).sum
        (fun η => zetaZeroSideContribution η φ) =
        zetaZeroSideContribution ρ φ +
          (insert (-ρ) (∅ : Finset ℂ)).sum
            (fun η => zetaZeroSideContribution η φ) := by
      exact Finset.sum_insert
        (by
          intro hmem
          exact
            match Finset.mem_insert.mp hmem with
            | Or.inl hneg_eq =>
                zetaZeroOrbit_self_ne_neg_of_re_ne_zero ρ hρre hneg_eq
            | Or.inr hempty =>
                False.elim (Finset.not_mem_empty ρ hempty))
    _ =
        zetaZeroSideContribution ρ φ + zetaZeroSideContribution (-ρ) φ := by
      exact congrArg
        (fun x : ℂ => zetaZeroSideContribution ρ φ + x)
        (Finset.sum_singleton (fun η => zetaZeroSideContribution η φ) (-ρ))

/-- A unit spectral sample makes the single zero-side contribution equal to minus the
analytic multiplicity. -/
theorem zetaZeroSideContribution_eq_neg_multiplicity_of_unitSample
    (η : ℂ) (φ : ZetaAdmissibleFunction)
    (hsample : zetaSpectralEval φ η = 1) :
    zetaZeroSideContribution η φ = - (zetaZeroMultiplicity η : ℂ) := by
  calc
    zetaZeroSideContribution η φ =
        - (zetaZeroMultiplicity η : ℂ) *
          zetaSpectralEval φ η := by
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
    (hsample : zetaSpectralEval φ η = 1) :
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
        zetaSpectralEval φ η = 1) :
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
  exact lt_of_lt_of_eq hsum (add_zero 0)

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
        zetaSpectralEval φ η = 1) :
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
  match exists_zeroOrbit_autocorrelation_unitContributionSpectralSamples ρ with
  | ⟨f, hsample⟩ =>
      exact ⟨f,
        zetaZeroOrbitContributionRe_lt_zero_of_unitSpectralSamples
          ρ hρ hρre horbit
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          hsample⟩

/-- Unit samples on a finite completed-zero set make its finite zero-side real
contribution strictly negative as soon as the set contains one completed zero. -/
theorem finiteCompletedZeroContributionRe_lt_zero_of_unitSpectralSamples
    (S : Finset ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (ρ : ℂ)
    (hρ : ρ ∈ S)
    (φ : ZetaAdmissibleFunction)
    (hsample : ∀ η : ℂ, η ∈ S → zetaSpectralEval φ η = 1) :
    Complex.re (∑ η in S, zetaZeroSideContribution η φ) < 0 := by
  have hterm_nonpos :
      ∀ η : ℂ, η ∈ S →
        Complex.re (zetaZeroSideContribution η φ) ≤ 0 := by
    intro η hη
    have hvalue :
        Complex.re (zetaZeroSideContribution η φ) =
          - (zetaZeroMultiplicity η : ℝ) :=
      zetaZeroSideContribution_re_eq_neg_multiplicity_of_unitSample
        η φ (hsample η hη)
    have hnonneg : 0 ≤ (zetaZeroMultiplicity η : ℝ) :=
      Nat.cast_nonneg (zetaZeroMultiplicity η)
    exact Eq.subst (motive := fun x : ℝ => x ≤ 0) hvalue.symm (neg_nonpos.mpr hnonneg)
  have hterm_negative :
      Complex.re (zetaZeroSideContribution ρ φ) < 0 := by
    have hvalue :
        Complex.re (zetaZeroSideContribution ρ φ) =
          - (zetaZeroMultiplicity ρ : ℝ) :=
      zetaZeroSideContribution_re_eq_neg_multiplicity_of_unitSample
        ρ φ (hsample ρ hρ)
    have hpositive : 0 < (zetaZeroMultiplicity ρ : ℝ) :=
      Nat.cast_pos.mpr
        (zetaZeroMultiplicity_pos_of_completedZero ⟨ρ, hS ρ hρ⟩)
    exact Eq.subst (motive := fun x : ℝ => x < 0) hvalue.symm (neg_lt_zero.mpr hpositive)
  have hsum :
      (∑ η in S, Complex.re (zetaZeroSideContribution η φ)) <
        ∑ _η in S, (0 : ℝ) :=
    Finset.sum_lt_sum hterm_nonpos ⟨ρ, hρ, hterm_negative⟩
  have hzero : (∑ _η in S, (0 : ℝ)) = 0 :=
    Finset.sum_const_zero
  have hsum_negative :
      (∑ η in S, Complex.re (zetaZeroSideContribution η φ)) < 0 :=
    hsum.trans_eq hzero
  exact lt_of_eq_of_lt
    (Complex.re_sum (s := S) (fun η => zetaZeroSideContribution η φ))
    hsum_negative

/-- The dagger-closed orbit sample set has a unit autocorrelation probe. -/
theorem exists_daggerClosedOrbit_autocorrelation_unitSpectralSamples
    (ρ : ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      ∀ z : ℂ,
        z ∈ zetaZeroOrbitDaggerClosedSpectralSampleFinset ρ →
          zetaSpectralEval (ZetaAdmissibleFunction.convolutionAutocorrelation f) z = 1 := by
  exact
    ZetaAdmissibleFunction.exists_autocorrelation_spectralEval_one_on_finset
      (zetaZeroOrbitDaggerClosedSpectralSampleFinset ρ)

/-- The real coordinate of `1/2 : ℂ` is `1/2 : ℝ`. -/
private theorem complex_half_re : (1 / 2 : ℂ).re = (1 / 2 : ℝ) := by
  have hhalf_complex : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) :=
    Eq.symm (Complex.ofReal_div (1 : ℝ) (2 : ℝ))
  have hhalf_coe_re : (((1 / 2 : ℝ) : ℂ).re) = (1 / 2 : ℝ) :=
    Complex.ofReal_re (1 / 2 : ℝ)
  exact Eq.trans (congrArg Complex.re hhalf_complex) hhalf_coe_re

/-- The real coordinate of a centered zero coordinate. -/
private theorem zetaCenteredZero_re (η : ℂ) :
    (zetaCenteredZero η).re = η.re - (1 / 2 : ℝ) := by
  have h1 : (zetaCenteredZero η).re = η.re - (1 / 2 : ℂ).re :=
    Complex.sub_re η (1 / 2 : ℂ)
  exact Eq.subst
    (motive := fun x : ℝ => (zetaCenteredZero η).re = η.re - x)
    complex_half_re
    h1

/-- Strict centered critical-strip bound for a completed zero. -/
theorem zetaCompletedZero_re_mem_open_centeredCriticalStrip
    (ρ : ℂ) (hρ : ZetaCompletedZero ρ) :
    -(1 / 2 : ℝ) < ρ.re ∧ ρ.re < (1 / 2 : ℝ) := by
  have hzero : centeredCompletedRiemannZeta ρ = 0 :=
    (centeredCompletedRiemannZetaFunction_eq ρ).symm.trans
      (zetaCompletedZero_zero_of_prop hρ)
  exact centeredCompletedRiemannZeta_zero_re_mem_open_centeredCriticalStrip ρ hzero

/-- The dagger-reflection real-part identity collapses to `1/2 < b` once the
reflected coordinate is bounded above by `1/2`. -/
private theorem half_lt_of_dagger_eq
    (a b : ℝ)
    (heq : -(a - (1 / 2 : ℝ)) = b - (1 / 2 : ℝ))
    (ha : a < (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) < b := by
  have hneg : -(a - (1 / 2 : ℝ)) = (1 / 2 : ℝ) - a :=
    neg_sub a (1 / 2 : ℝ)
  have heq2 : (1 / 2 : ℝ) - a = b - (1 / 2 : ℝ) :=
    hneg.symm.trans heq
  have hb : b = ((1 / 2 : ℝ) - a) + (1 / 2 : ℝ) :=
    sub_eq_iff_eq_add.mp heq2.symm
  have hpos : 0 < (1 / 2 : ℝ) - a :=
    sub_pos.mpr ha
  have hstep : (0 : ℝ) + (1 / 2 : ℝ) < ((1 / 2 : ℝ) - a) + (1 / 2 : ℝ) :=
    add_lt_add_right hpos (1 / 2 : ℝ)
  have hstep' : (1 / 2 : ℝ) < ((1 / 2 : ℝ) - a) + (1 / 2 : ℝ) :=
    Eq.subst
      (motive := fun x : ℝ => x < ((1 / 2 : ℝ) - a) + (1 / 2 : ℝ))
      (zero_add (1 / 2 : ℝ))
      hstep
  exact Eq.subst (motive := fun x : ℝ => (1 / 2 : ℝ) < x) hb.symm hstep'

/-- Finite spectral orbit separation: any completed zero outside the centered
two-point orbit of `ρ` has a centered coordinate that avoids the dagger-closed
finite spectral sample set of the orbit.

This is the genuine separation step.  The two non-orbit dagger faces force the
candidate zero to sit at uncentered real part in `(1,2)`, outside the critical
strip, contradicting strict critical-strip confinement of completed zeros. -/
theorem zetaCenteredZero_not_mem_daggerClosed_orbitSpectralSample_of_completedZero
    (ρ : ℂ) (hρ : ZetaCompletedZero ρ)
    (η : ℂ) (hη : ZetaCompletedZero η)
    (hηorbit : η ∉ zetaZeroOrbitFinset ρ) :
    zetaCenteredZero η ∉
      ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset
        (zetaZeroOrbitSpectralSampleFinset ρ) := by
  intro hmem
  have hηstrip := zetaCompletedZero_re_mem_open_centeredCriticalStrip η hη
  have hρstrip := zetaCompletedZero_re_mem_open_centeredCriticalStrip ρ hρ
  unfold ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset at hmem
  rcases Finset.mem_union.mp hmem with hsamp | hrefl
  · -- Direct sample face: forces `η ∈ orbit`.
    unfold zetaZeroOrbitSpectralSampleFinset at hsamp
    rcases Finset.mem_image.mp hsamp with ⟨θ, hθorbit, hθeq⟩
    have hsub : θ - (1 / 2 : ℂ) = η - (1 / 2 : ℂ) := hθeq
    have hθη : θ = η := sub_left_inj.mp hsub
    exact hηorbit
      (Eq.subst (motive := fun x : ℂ => x ∈ zetaZeroOrbitFinset ρ) hθη hθorbit)
  · -- Dagger-reflected face: forces an out-of-strip real part.
    unfold ZetaAdmissibleFunction.daggerReflectedSpectralSampleFinset at hrefl
    rcases Finset.mem_image.mp hrefl with ⟨w, hwsamp, hweq⟩
    unfold zetaZeroOrbitSpectralSampleFinset at hwsamp
    rcases Finset.mem_image.mp hwsamp with ⟨θ, hθorbit, hθw⟩
    have hweq' : -star (zetaCenteredZero θ) = zetaCenteredZero η := by
      exact
        Eq.subst
          (motive := fun x : ℂ => -star x = zetaCenteredZero η)
          hθw.symm
          hweq
    have hre :
        (-star (zetaCenteredZero θ)).re = (zetaCenteredZero η).re :=
      congrArg Complex.re hweq'
    have hL :
        (-star (zetaCenteredZero θ)).re = -(θ.re - (1 / 2 : ℝ)) := by
      calc
        (-star (zetaCenteredZero θ)).re
            = -((star (zetaCenteredZero θ)).re) :=
          Complex.neg_re (star (zetaCenteredZero θ))
        _ = -((zetaCenteredZero θ).re) :=
          congrArg Neg.neg (Complex.conj_re (zetaCenteredZero θ))
        _ = -(θ.re - (1 / 2 : ℝ)) :=
          congrArg Neg.neg (zetaCenteredZero_re θ)
    have heqre : -(θ.re - (1 / 2 : ℝ)) = η.re - (1 / 2 : ℝ) := by
      calc
        -(θ.re - (1 / 2 : ℝ)) = (-star (zetaCenteredZero θ)).re := hL.symm
        _ = (zetaCenteredZero η).re := hre
        _ = η.re - (1 / 2 : ℝ) := zetaCenteredZero_re η
    have hθlt : θ.re < (1 / 2 : ℝ) := by
      rcases (zetaZeroOrbitFinset_mem_iff ρ θ).mp hθorbit with hθρ | hθnρ
      · exact Eq.subst
          (motive := fun x : ℂ => x.re < (1 / 2 : ℝ)) hθρ.symm hρstrip.2
      · have hθre : θ.re = -ρ.re := by
          calc
            θ.re = (-ρ).re := congrArg Complex.re hθnρ
            _ = -ρ.re := Complex.neg_re ρ
        have hneg : -ρ.re < (1 / 2 : ℝ) := by
          have hlt : -ρ.re < -(-(1 / 2 : ℝ)) := neg_lt_neg hρstrip.1
          exact Eq.subst
            (motive := fun x : ℝ => -ρ.re < x) (neg_neg (1 / 2 : ℝ)) hlt
        exact Eq.subst
          (motive := fun x : ℝ => x < (1 / 2 : ℝ)) hθre.symm hneg
    have hfinal : (1 / 2 : ℝ) < η.re :=
      half_lt_of_dagger_eq θ.re η.re heqre hθlt
    exact (lt_asymm hfinal) hηstrip.2

end

end LFunctions
end Boundary
