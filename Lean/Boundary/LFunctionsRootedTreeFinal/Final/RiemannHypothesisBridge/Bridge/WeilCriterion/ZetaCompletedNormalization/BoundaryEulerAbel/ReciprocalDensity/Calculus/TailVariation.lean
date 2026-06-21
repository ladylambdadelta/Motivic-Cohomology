import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.FirstDerivative.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.ReciprocalVariation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.ReciprocalDensity.Regularity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.ReciprocalDensity.Calculus.TailCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.PostCutoffTail

/-!
# Reciprocal-density tail variation estimates
-/

namespace Boundary
namespace LFunctions

/-- Standard Abel/Dirichlet variation estimate for the reciprocal-amplitude
integral after the canonical cutoff.

This is the genuine remaining analytic sink: it is not the coarse scalar
majorant estimate above.  The proof should use the bounded primitive of the
logarithmic phase together with the total variation of `x ↦ 1 / x`, keeping the
endpoint contribution and variation contribution separate. -/
theorem reciprocalAmplitude_boundedPrimitive_variation_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hreciprocal_density :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
          (1 : ℝ) / x ^ 2) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) := by
  exact
    concreteReciprocalVariation_logarithmicPhase_integral_bound_of_density
      t ht hpartial hNM hreciprocal_density

/-- Oscillatory reciprocal-density integral estimate after the canonical cutoff.

This is not a consequence of integrating the coarse scalar majorant: that scalar
integral grows with the right endpoint.  The uniform bound is the
Euler-Maclaurin/first-derivative cancellation estimate for the concrete
reciprocal-amplitude term. -/
theorem partialSummation_reciprocalAmplitude_oscillatoryIntegral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hreciprocal_density :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
          (1 : ℝ) / x ^ 2) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) := by
  exact
    reciprocalAmplitude_boundedPrimitive_variation_integral_bound
      t ht hpartial hNM hreciprocal_density

/-- Oscillatory reciprocal-density integral estimate after the canonical cutoff.

This is the concrete Abel/partial-summation estimate for the reciprocal
amplitude, consuming the already isolated partial-sum and reciprocal-density
inputs. -/
theorem oscillatoryReciprocalDensity_logarithmicPhase_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hreciprocal_density :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
          (1 : ℝ) / x ^ 2) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) := by
  exact
    concreteReciprocalVariation_logarithmicPhase_integral_bound_of_density
      t ht hpartial hNM hreciprocal_density


/-- Integral arithmetic for the reciprocal-derivative term in the finite Abel
decomposition.

This is the variation side of partial summation for the weight `x ↦ 1 / x`.
After the first-derivative Euler-Maclaurin estimate bounds the logarithmic-phase
primitive, this theorem owns the monotone reciprocal-variation integral and the
normalization to the cutoff logarithm.  Cf. Edwards, *Riemann's Zeta Function*,
Euler-Maclaurin derivations. -/
theorem eulerMaclaurin_logarithmicPhase_finiteAbel_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) := by
  exact oscillatoryEulerMaclaurin_logarithmicPhase_integral_bound
    t ht hpartial hNM

/-- Deep Euler-Maclaurin arithmetic owner for the finite Abel endpoint and
reciprocal-derivative integral terms.

This is the remaining bookkeeping attached to the first-derivative
Euler-Maclaurin estimate: the reciprocal endpoint weights and the integral of
the reciprocal derivative are both normalized to the same logarithmic cutoff
constant. -/
theorem logarithmicPhase_firstDerivative_finiteAbel_endpoint_integral_arithmetic
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ +
        ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖)) ∧
    (‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          ((1 : ℝ) / x ^ 2) *
            (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))) := by
  exact
    ⟨eulerMaclaurin_logarithmicPhase_finiteAbel_endpoint_bound t ht hNM,
      eulerMaclaurin_logarithmicPhase_finiteAbel_integral_bound
        t ht hpartial hNM⟩

/-- Exact endpoint arithmetic for the finite Abel package.  This is the
reciprocal-weight endpoint part after the first-derivative estimate has been
applied at `M` and at the canonical cutoff. -/
theorem logarithmicPhase_firstDerivative_finiteAbel_endpoint_arithmetic
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ +
    ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    eulerMaclaurin_logarithmicPhase_finiteAbel_endpoint_bound t ht hNM

/-- Exact reciprocal-derivative integral arithmetic for the finite Abel package.
The analytic input is the first-derivative partial-sum estimate; this lemma owns
the endpoint and logarithmic integral bookkeeping. -/
theorem logarithmicPhase_firstDerivative_finiteAbel_integral_arithmetic
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) := by
  exact
    (logarithmicPhase_firstDerivative_finiteAbel_endpoint_integral_arithmetic
      t ht hpartial hNM).2

/-- Algebraic endpoint extraction from the logarithmic-phase first-derivative
partial-sum estimate.

This is not a separate analytic input: the two reciprocal endpoint weights are
controlled after the canonical cutoff by applying
`logarithmicPhasePartialSum_firstDerivative_bound` at `M` and at the cutoff. -/
theorem logarithmicPhase_firstDerivative_eulerMaclaurin_finiteAbel_package
    (hfiniteDifference : logarithmicPhaseFiniteDifferenceHypothesis)
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊((M : ℕ) : ℝ)⌋₊‖ ≤
        40 *
          ((((⌊((M : ℕ) : ℝ)⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ +
              Real.sqrt (1 + ‖t‖)) *
            Real.log (2 + ⌊((M : ℕ) : ℝ)⌋₊))) ∧
    (‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ +
        ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖)) ∧
    (‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))) := by
  exact
    ⟨logarithmicPhase_firstDerivative_finiteAbel_rightPartial_bound
        hfiniteDifference t ht hNM,
      logarithmicPhase_firstDerivative_finiteAbel_endpoint_arithmetic t ht hNM,
      logarithmicPhase_firstDerivative_finiteAbel_integral_arithmetic
        t ht hpartial hNM⟩

/-- Explicit finite Abel-tail constant for the logarithmic-phase oscillator
after the canonical cutoff.

The constant is intentionally not normalized to `1`: the owner estimate must
record the actual Abel endpoint and reciprocal-derivative contribution rather
than hiding it behind a false unit-bound surface. -/
noncomputable def boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant
    (t : ℝ) : ℝ :=
  4 + 16 * Real.log (3 + ‖t‖)

/-- Exponent normal form for the boundary-line finite-tail summand. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_tail_exponent_eq
    (t : ℝ) :
    (-1 : ℂ) + (-(t : ℂ) * Complex.I) =
      -boundaryLineOnePointRealParam t := by
  have hneg_sum :
      (-1 : ℂ) + (-(t : ℂ) * Complex.I) =
        -((1 : ℂ) + (t : ℂ) * Complex.I) := by
    calc
      (-1 : ℂ) + (-(t : ℂ) * Complex.I) =
          -(1 : ℂ) + -((t : ℂ) * Complex.I) := by
        exact congrArg₂ (fun u v : ℂ => u + v)
          (show (-1 : ℂ) = -(1 : ℂ) by rfl)
          (neg_mul (t : ℂ) Complex.I)
      _ = -((1 : ℂ) + (t : ℂ) * Complex.I) := by
        exact (neg_add (1 : ℂ) ((t : ℂ) * Complex.I)).symm
  have hparam :
      ((1 : ℂ) + (t : ℂ) * Complex.I) =
        boundaryLineOnePointRealParam t := by
    have hre :
        ((1 : ℂ) + (t : ℂ) * Complex.I).re =
          (boundaryLineOnePointRealParam t).re := by
      calc
        ((1 : ℂ) + (t : ℂ) * Complex.I).re =
            (1 : ℂ).re + ((t : ℂ) * Complex.I).re := by
          exact Complex.add_re (1 : ℂ) ((t : ℂ) * Complex.I)
        _ = (1 : ℝ) + (-(t : ℂ).im) := by
          exact congrArg₂ (fun u v : ℝ => u + v)
            (Complex.ofReal_re 1)
            (Complex.mul_I_re (t : ℂ))
        _ = (1 : ℝ) + (-0) := by
          exact congrArg (fun u : ℝ => (1 : ℝ) + (-u))
            (Complex.ofReal_im t)
        _ = (1 : ℝ) + 0 := by
          exact congrArg (fun u : ℝ => (1 : ℝ) + u) neg_zero
        _ = (1 : ℝ) := by
          exact add_zero 1
        _ = (boundaryLineOnePointRealParam t).re := by
          exact (boundaryLineOnePointRealParam_re t).symm
    have him :
        ((1 : ℂ) + (t : ℂ) * Complex.I).im =
          (boundaryLineOnePointRealParam t).im := by
      calc
        ((1 : ℂ) + (t : ℂ) * Complex.I).im =
            (1 : ℂ).im + ((t : ℂ) * Complex.I).im := by
          exact Complex.add_im (1 : ℂ) ((t : ℂ) * Complex.I)
        _ = (0 : ℝ) + (t : ℂ).re := by
          exact congrArg₂ (fun u v : ℝ => u + v)
            (Complex.ofReal_im 1)
            (Complex.mul_I_im (t : ℂ))
        _ = (0 : ℝ) + t := by
          exact congrArg (fun u : ℝ => (0 : ℝ) + u)
            (Complex.ofReal_re t)
        _ = t := by
          exact zero_add t
        _ = (boundaryLineOnePointRealParam t).im := by
          exact (boundaryLineOnePointRealParam_im t).symm
    exact Complex.ext hre him
  exact Eq.trans hneg_sum (congrArg Neg.neg hparam)

/-- Positive-natural complex-power normalization for the undamped
boundary-line tail term. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_positiveNat_cpow_tail_factorization
    (t : ℝ)
    {k : ℕ}
    (hk : 0 < k) :
    (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) =
      ((((k : ℕ) : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t)) := by
  let x : ℂ := (k : ℂ)
  have hx_ne : x ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hinv :
      ((k : ℂ)⁻¹ : ℂ) = x ^ (-1 : ℂ) := by
    exact (Complex.cpow_neg_one x).symm
  have hbase :
      (((k : ℕ) : ℝ) : ℂ) = x := by
    exact Complex.ofReal_natCast k
  have hmul :
      x ^ (-1 : ℂ) * x ^ (-(t : ℂ) * Complex.I) =
        x ^ ((-1 : ℂ) + (-(t : ℂ) * Complex.I)) := by
    exact (Complex.cpow_add (-1 : ℂ) (-(t : ℂ) * Complex.I) hx_ne).symm
  have hexponent :
      x ^ ((-1 : ℂ) + (-(t : ℂ) * Complex.I)) =
        x ^ (-boundaryLineOnePointRealParam t) := by
    exact congrArg
      (fun z : ℂ => x ^ z)
      (boundaryLineOnePointRealParam_logarithmicPhase_tail_exponent_eq t)
  have hright :
      x ^ (-boundaryLineOnePointRealParam t) =
        ((((k : ℕ) : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t)) := by
    exact congrArg
      (fun y : ℂ => y ^ (-boundaryLineOnePointRealParam t))
      hbase.symm
  calc
    (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        x ^ (-1 : ℂ) * x ^ (-(t : ℂ) * Complex.I) := by
      exact congrArg (fun y : ℂ => y * x ^ (-(t : ℂ) * Complex.I)) hinv
    _ = x ^ ((-1 : ℂ) + (-(t : ℂ) * Complex.I)) :=
      hmul
    _ = x ^ (-boundaryLineOnePointRealParam t) :=
      hexponent
    _ = ((((k : ℕ) : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t)) :=
      hright

/-- Finite post-cutoff weighted logarithmic-phase sums are exactly the finite
Euler-Maclaurin sums for `x ↦ x^(-(1+it))`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_weightedTail_eq_cpow_neg_sum
    (t : ℝ)
    {N M : ℕ}
    (hN : 0 < N) :
    (∑ n ∈ Finset.Ioc N M,
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))) =
      ∑ n in Finset.Ioc N M,
        ((((n : ℕ) : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t)) := by
  exact Finset.sum_congr rfl
    (fun n hn_mem =>
      let hn_pos : 0 < n :=
        Nat.lt_trans hN (Finset.mem_Ioc.mp hn_mem).1
      boundaryLineOnePointRealParam_logarithmicPhase_positiveNat_cpow_tail_factorization
        t hn_pos)

/-- Finite first-order Euler-Maclaurin identity for the exact post-cutoff
boundary-line tail. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_weightedTail_eulerMaclaurin_identity
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))) =
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) +
        (-(1 / 2 : ℂ) *
          ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
            (-boundaryLineOnePointRealParam t))) +
        ((1 / 2 : ℂ) *
          ((((M : ℕ) : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) +
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-boundaryLineOnePointRealParam t *
              (((x : ℝ) : ℂ) ^ (-(boundaryLineOnePointRealParam t + 1))))) := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  have hC_pos : 0 < C :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hsum :
      (∑ n ∈ Finset.Ioc C M,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        ∑ n in Finset.Ioc C M,
          ((((n : ℕ) : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t)) :=
    boundaryLineOnePointRealParam_logarithmicPhase_weightedTail_eq_cpow_neg_sum
      t hC_pos
  have hem :
      (∑ n in Finset.Ioc C M,
          ((((n : ℕ) : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) =
        (∫ x in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) +
          (-(1 / 2 : ℂ) *
            ((((C : ℕ) : ℝ) : ℂ) ^
              (-boundaryLineOnePointRealParam t))) +
          ((1 / 2 : ℂ) *
            ((((M : ℕ) : ℝ) : ℂ) ^
              (-boundaryLineOnePointRealParam t))) +
          (∫ x in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (-boundaryLineOnePointRealParam t *
                (((x : ℝ) : ℂ) ^
                  (-(boundaryLineOnePointRealParam t + 1))))) :=
    eulerMaclaurin_firstOrder_cpow_neg_finite_postCutoffTail_identity_standard
      (boundaryLineOnePointRealParam t) C M hC_pos hM
  exact Eq.trans hsum hem

/-- The boundary-line exponent has real part `-1` after negation. -/
theorem boundaryLineOnePointRealParam_neg_re_eq_neg_one
    (t : ℝ) :
    (-boundaryLineOnePointRealParam t).re = (-1 : ℝ) := by
  calc
    (-boundaryLineOnePointRealParam t).re =
        -(boundaryLineOnePointRealParam t).re := by
      exact Complex.neg_re (boundaryLineOnePointRealParam t)
    _ = -(1 : ℝ) := by
      exact congrArg Neg.neg (boundaryLineOnePointRealParam_re t)

/-- Positive-natural boundary-line tail powers have reciprocal norm. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_tail_cpow_norm_eq_inv
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    ‖((((n : ℕ) : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))‖ =
      ((n : ℝ)⁻¹) := by
  have hn_real_pos : (0 : ℝ) < (n : ℝ) :=
    Nat.cast_pos.mpr hn
  have hnorm :
      ‖((((n : ℕ) : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))‖ =
        (n : ℝ) ^ (-1 : ℝ) := by
    calc
      ‖((((n : ℕ) : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))‖ =
          Complex.abs
            ((((n : ℕ) : ℝ) : ℂ) ^
              (-boundaryLineOnePointRealParam t)) := by
        exact Complex.norm_eq_abs
          ((((n : ℕ) : ℝ) : ℂ) ^
            (-boundaryLineOnePointRealParam t))
      _ = (n : ℝ) ^ (-boundaryLineOnePointRealParam t).re := by
        exact Complex.abs_cpow_eq_rpow_re_of_pos
          hn_real_pos
          (-boundaryLineOnePointRealParam t)
      _ = (n : ℝ) ^ (-1 : ℝ) := by
        exact congrArg (fun r : ℝ => (n : ℝ) ^ r)
          (boundaryLineOnePointRealParam_neg_re_eq_neg_one t)
  have hinv :
      (n : ℝ) ^ (-1 : ℝ) = ((n : ℝ)⁻¹) := by
    calc
      (n : ℝ) ^ (-1 : ℝ) = ((n : ℝ) ^ (1 : ℝ))⁻¹ := by
        exact Real.rpow_neg (le_of_lt hn_real_pos) 1
      _ = ((n : ℝ)⁻¹) := by
        exact congrArg Inv.inv (Real.rpow_one (n : ℝ))
  exact Eq.trans hnorm hinv

/-- A post-cutoff boundary-line tail power has norm at most one. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_tail_cpow_norm_le_one
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    ‖((((n : ℕ) : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))‖ ≤
      (1 : ℝ) := by
  have hnorm :
      ‖((((n : ℕ) : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))‖ =
        ((n : ℝ)⁻¹) :=
    boundaryLineOnePointRealParam_logarithmicPhase_tail_cpow_norm_eq_inv
      t hn
  have hn_one : (1 : ℝ) ≤ (n : ℝ) :=
    Nat.one_le_cast.mpr (Nat.succ_le_of_lt hn)
  have hinv_le_one : ((n : ℝ)⁻¹) ≤ (1 : ℝ) :=
    inv_le_one_of_one_le₀ hn_one
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ (1 : ℝ))
    hnorm.symm
    hinv_le_one

/-- Each half-endpoint correction in the finite Euler-Maclaurin tail is bounded
by one. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_tail_halfEndpoint_norm_le_one
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n)
    (ε : ℂ)
    (hε : ‖ε‖ ≤ (1 : ℝ)) :
    ‖ε * ((((n : ℕ) : ℝ) : ℂ) ^
        (-boundaryLineOnePointRealParam t))‖ ≤
      (1 : ℝ) := by
  have hpow :
      ‖((((n : ℕ) : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))‖ ≤
        (1 : ℝ) :=
    boundaryLineOnePointRealParam_logarithmicPhase_tail_cpow_norm_le_one
      t hn
  have hmul :
      ‖ε * ((((n : ℕ) : ℝ) : ℂ) ^
          (-boundaryLineOnePointRealParam t))‖ =
        ‖ε‖ *
          ‖((((n : ℕ) : ℝ) : ℂ) ^
            (-boundaryLineOnePointRealParam t))‖ := by
    exact norm_mul ε
      ((((n : ℕ) : ℝ) : ℂ) ^
        (-boundaryLineOnePointRealParam t))
  have hproduct :
      ‖ε‖ *
          ‖((((n : ℕ) : ℝ) : ℂ) ^
            (-boundaryLineOnePointRealParam t))‖ ≤
        (1 : ℝ) * (1 : ℝ) :=
    mul_le_mul hε hpow
      (norm_nonneg
        ((((n : ℕ) : ℝ) : ℂ) ^
          (-boundaryLineOnePointRealParam t)))
      zero_le_one
  have hnorm_product :
      ‖ε * ((((n : ℕ) : ℝ) : ℂ) ^
          (-boundaryLineOnePointRealParam t))‖ ≤
        (1 : ℝ) * (1 : ℝ) :=
    Eq.subst
      (motive := fun r : ℝ => r ≤ (1 : ℝ) * (1 : ℝ))
      hmul.symm
      hproduct
  exact Eq.subst
    (motive := fun r : ℝ =>
      ‖ε * ((((n : ℕ) : ℝ) : ℂ) ^
          (-boundaryLineOnePointRealParam t))‖ ≤ r)
    (show (1 : ℝ) * (1 : ℝ) = (1 : ℝ) by
      exact one_mul (1 : ℝ))
    hnorm_product

/-- Each reciprocal-weighted logarithmic-phase term is dominated by its
reciprocal density. -/
theorem boundaryLineOnePointRealParam_reciprocalLogPhaseTerm_norm_le_inv
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    ‖((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      (1 : ℝ) / (n : ℝ) := by
  have hphase : ‖(n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ≤ (1 : ℝ) :=
    logarithmicPhase_nat_sample_norm_le_one t n
  have hinv_norm : ‖((n : ℂ)⁻¹ : ℂ)‖ = (1 : ℝ) / (n : ℝ) := by
    have hn_complex_ne : (n : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have hn_real_pos : (0 : ℝ) < (n : ℝ) :=
      Nat.cast_pos.mpr hn
    calc
      ‖((n : ℂ)⁻¹ : ℂ)‖ = ‖(n : ℂ)‖⁻¹ := by
        exact norm_inv (n : ℂ)
      _ = ((n : ℝ))⁻¹ := by
        exact congrArg Inv.inv (Complex.norm_natCast n)
      _ = (1 : ℝ) / (n : ℝ) := by
        exact (one_div (n : ℝ)).symm
  have hmul :
      ‖((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ =
        ‖((n : ℂ)⁻¹ : ℂ)‖ * ‖(n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ :=
    norm_mul ((n : ℂ)⁻¹ : ℂ) ((n : ℂ) ^ (-(t : ℂ) * Complex.I))
  have hinv_nonneg : 0 ≤ ‖((n : ℂ)⁻¹ : ℂ)‖ :=
    norm_nonneg ((n : ℂ)⁻¹ : ℂ)
  calc
    ‖((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ =
        ‖((n : ℂ)⁻¹ : ℂ)‖ * ‖(n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ :=
      hmul
    _ ≤ ‖((n : ℂ)⁻¹ : ℂ)‖ * 1 :=
      mul_le_mul_of_nonneg_left hphase hinv_nonneg
    _ = ‖((n : ℂ)⁻¹ : ℂ)‖ := by
      exact mul_one ‖((n : ℂ)⁻¹ : ℂ)‖
    _ = (1 : ℝ) / (n : ℝ) :=
      hinv_norm

/-- Finite reciprocal-density mass before the canonical cutoff is controlled by
the boundary-line harmonic cutoff. -/
theorem boundaryLineOnePointRealParam_reciprocalDensity_preCutoff_mass_le
    (t : ℝ)
    {N M : ℕ}
    (hN : 1 ≤ N)
    (hM : M ≤ ⌊2 + ‖t‖⌋₊) :
    (∑ n ∈ Finset.Ioc N M, (1 : ℝ) / (n : ℝ)) ≤
      harmonic ⌊2 + ‖t‖⌋₊ := by
  have hsubset :
      Finset.Ioc N M ⊆ Finset.Icc 1 ⌊2 + ‖t‖⌋₊ := by
    intro n hn_mem
    have hn_bounds := Finset.mem_Ioc.mp hn_mem
    have hn_one : 1 ≤ n :=
      le_trans hN (Nat.le_of_lt hn_bounds.1)
    have hn_cutoff : n ≤ ⌊2 + ‖t‖⌋₊ :=
      le_trans hn_bounds.2 hM
    exact Finset.mem_Icc.mpr ⟨hn_one, hn_cutoff⟩
  have hnonneg :
      ∀ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        n ∉ Finset.Ioc N M →
          (0 : ℝ) ≤ (1 : ℝ) / (n : ℝ) := by
    intro n hn_mem _hn_not
    have hn_one : 1 ≤ n :=
      (Finset.mem_Icc.mp hn_mem).1
    have hn_pos_real : (0 : ℝ) < (n : ℝ) :=
      Nat.cast_pos.mpr (Nat.lt_of_succ_le hn_one)
    exact div_nonneg zero_le_one (le_of_lt hn_pos_real)
  have hsum_subset :
      (∑ n ∈ Finset.Ioc N M, (1 : ℝ) / (n : ℝ)) ≤
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊, (1 : ℝ) / (n : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  have hharmonic :
      (∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊, (1 : ℝ) / (n : ℝ)) =
        harmonic ⌊2 + ‖t‖⌋₊ := by
    let qsum : ℚ :=
      Finset.sum (Finset.Icc 1 ⌊2 + ‖t‖⌋₊)
        (fun n : ℕ => ((n : ℚ)⁻¹ : ℚ))
    have hqsum_def :
        qsum =
          Finset.sum (Finset.Icc 1 ⌊2 + ‖t‖⌋₊)
            (fun n : ℕ => ((n : ℚ)⁻¹ : ℚ)) :=
      rfl
    have hrat :
        qsum = harmonic ⌊2 + ‖t‖⌋₊ :=
      Eq.trans hqsum_def
        (harmonic_eq_sum_Icc (n := ⌊2 + ‖t‖⌋₊)).symm
    have hcast_sum :
        (qsum : ℝ) =
          Finset.sum (Finset.Icc 1 ⌊2 + ‖t‖⌋₊)
            (fun n : ℕ => (((n : ℚ)⁻¹ : ℚ) : ℝ)) :=
      Eq.trans
        (congrArg (fun q : ℚ => (q : ℝ)) hqsum_def)
        (map_sum (Rat.castHom ℝ)
          (fun n : ℕ => ((n : ℚ)⁻¹ : ℚ))
          (Finset.Icc 1 ⌊2 + ‖t‖⌋₊))
    have hcast_harmonic :
        (qsum : ℝ) = (harmonic ⌊2 + ‖t‖⌋₊ : ℝ) :=
      congrArg (fun q : ℚ => (q : ℝ)) hrat
    have hsum_cast :
        (Finset.sum (Finset.Icc 1 ⌊2 + ‖t‖⌋₊)
          (fun n : ℕ => (((n : ℚ)⁻¹ : ℚ) : ℝ))) =
          harmonic ⌊2 + ‖t‖⌋₊ :=
      Eq.trans hcast_sum.symm hcast_harmonic
    have hterm :
        (∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊, (1 : ℝ) / (n : ℝ)) =
          ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊, (((n : ℚ)⁻¹ : ℚ) : ℝ) := by
      exact Finset.sum_congr rfl
        (fun n hn_mem => by
          have hn_one_le : 1 ≤ n :=
            (Finset.mem_Icc.mp hn_mem).1
          have hn_pos : 0 < n :=
            Nat.lt_of_succ_le hn_one_le
          calc
            (1 : ℝ) / (n : ℝ) = ((n : ℝ)⁻¹) := by
              exact one_div (n : ℝ)
            _ = (((n : ℚ)⁻¹ : ℚ) : ℝ) := by
              exact (Rat.cast_inv (α := ℝ) (n : ℚ)).symm)
    exact Eq.trans hterm hsum_cast
  exact le_trans hsum_subset (le_of_eq hharmonic)

/-- Finite pre-cutoff block estimate for reciprocal-weighted logarithmic-phase
tails.  This is purely the cardinal/term-norm side; no oscillatory cancellation
is used before the cutoff. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_preCutoff_finiteTail_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {N M : ℕ}
    (hN : 1 ≤ N)
    (hM : M ≤ ⌊2 + ‖t‖⌋₊) :
    ‖∑ n ∈ Finset.Ioc N M,
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      2 * Real.log (2 + ‖t‖) := by
  have hnorm_sum :
      ‖∑ n ∈ Finset.Ioc N M,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        ∑ n ∈ Finset.Ioc N M,
          ‖((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ :=
    norm_sum_le _ _
  have hterm_sum :
      (∑ n ∈ Finset.Ioc N M,
          ‖((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖) ≤
        ∑ n ∈ Finset.Ioc N M, (1 : ℝ) / (n : ℝ) := by
    exact Finset.sum_le_sum
      (fun n hn_mem =>
        let hn_pos : 0 < n :=
          Nat.lt_trans (Nat.lt_of_succ_le hN) (Finset.mem_Ioc.mp hn_mem).1
        boundaryLineOnePointRealParam_reciprocalLogPhaseTerm_norm_le_inv t hn_pos)
  have hmass :
      (∑ n ∈ Finset.Ioc N M, (1 : ℝ) / (n : ℝ)) ≤
        harmonic ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_reciprocalDensity_preCutoff_mass_le
      t hN hM
  have hharmonic :
      harmonic ⌊2 + ‖t‖⌋₊ ≤ 1 + Real.log (2 + ‖t‖) :=
    harmonic_boundaryLine_truncation_le_one_add_log t
  have hlog_one : (1 : ℝ) ≤ Real.log (2 + ‖t‖) :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have hone_add :
      1 + Real.log (2 + ‖t‖) ≤
        2 * Real.log (2 + ‖t‖) := by
    let L : ℝ := Real.log (2 + ‖t‖)
    calc
      1 + L ≤ L + L := by
        exact add_le_add_right hlog_one L
      _ = 1 * L + 1 * L := by
        exact congrArg₂ (fun u v : ℝ => u + v)
          (one_mul L).symm
          (one_mul L).symm
      _ = (1 + 1) * L := by
        exact (add_mul 1 1 L).symm
      _ = 2 * L := by
        exact congrArg (fun u : ℝ => u * L) one_add_one_eq_two
  exact
    le_trans hnorm_sum
      (le_trans hterm_sum
        (le_trans hmass (le_trans hharmonic hone_add)))


end LFunctions
end Boundary
