import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.FiniteCarrierBoundData

/-!
# Combined completed-log-derivative factor bound data

This file owns the paired zeta-side/inverse-Gamma bound-data package for
scheduled finite carriers and downstream log-derivative constructors.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

structure CompletedZetaZeroExcisedStrip.FactorBoundData
    {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b) where
  zetaSide : CompletedZetaZeroExcisedStrip.ZetaSideBoundData E
  inverseGamma : CompletedZetaZeroExcisedStrip.InverseGammaBoundData E

def CompletedZetaZeroExcisedStrip.FactorBoundData.ofParts
    {a b : ℝ} {E : CompletedZetaZeroExcisedStrip a b}
    (zetaSide : CompletedZetaZeroExcisedStrip.ZetaSideBoundData E)
    (inverseGamma : CompletedZetaZeroExcisedStrip.InverseGammaBoundData E) :
    CompletedZetaZeroExcisedStrip.FactorBoundData E :=
  { zetaSide := zetaSide
    inverseGamma := inverseGamma }

/-- Assemble factor data from the two logarithmic-derivative owner packages.
This is the direct route for the inverse-Gamma factor: it keeps the analytic
input at the level of its logarithmic derivative rather than requiring a
polynomial bound for the exponentially growing reciprocal Gamma factor. -/
def CompletedZetaZeroExcisedStrip.FactorBoundData.ofLogDerivBounds
    {a b : ℝ} {E : CompletedZetaZeroExcisedStrip a b}
    (zetaSide : CompletedZetaZeroExcisedStrip.ZetaSideBoundData E)
    (inverseGamma : CompletedZetaZeroExcisedStrip.InverseGammaBoundData E) :
    CompletedZetaZeroExcisedStrip.FactorBoundData E :=
  CompletedZetaZeroExcisedStrip.FactorBoundData.ofParts zetaSide inverseGamma

def CompletedZetaZeroExcisedStrip.FactorBoundData.ofCauchyLogDerivative
    {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b)
    (separated : E.HasPositiveSingularSeparation)
    (zetaRadius zetaAmplitude zetaValueLower : ℕ → ℝ)
    (gammaRadius gammaAmplitude gammaValueLower : ℕ → ℝ)
    (zetaRadius_pos : ∀ N : ℕ, 0 < zetaRadius N)
    (zetaAmplitude_pos : ∀ N : ℕ, 0 < zetaAmplitude N)
    (zetaValueLower_pos : ∀ N : ℕ, 0 < zetaValueLower N)
    (gammaRadius_pos : ∀ N : ℕ, 0 < gammaRadius N)
    (gammaAmplitude_pos : ∀ N : ℕ, 0 < gammaAmplitude N)
    (gammaValueLower_pos : ∀ N : ℕ, 0 < gammaValueLower N)
    (zetaDiffCont :
      ∀ (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        DiffContOnCl ℂ zetaSideFactor (Metric.ball z (zetaRadius N)))
    (zetaSphereBound :
      ∀ (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (zetaRadius N) →
          ‖zetaSideFactor w‖ ≤
            zetaAmplitude N * (1 + ‖z.im‖) ^ N)
    (zetaValueLower_bound :
      ∀ (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        zetaValueLower N ≤ ‖zetaSideFactor z‖)
    (gammaDiffCont :
      ∀ (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        DiffContOnCl ℂ
          (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (Metric.ball z (gammaRadius N)))
    (gammaSphereBound :
      ∀ (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (gammaRadius N) →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤
            gammaAmplitude N * (1 + ‖z.im‖) ^ N)
    (gammaValueLower_bound :
      ∀ (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        gammaValueLower N ≤ ‖(Complex.Gammaℝ z)⁻¹‖) :
    CompletedZetaZeroExcisedStrip.FactorBoundData E :=
  CompletedZetaZeroExcisedStrip.FactorBoundData.ofParts
    (CompletedZetaZeroExcisedStrip.ZetaSideBoundData.ofCauchyLogDerivative
      E
      separated
      zetaRadius
      zetaAmplitude
      zetaValueLower
      zetaRadius_pos
      zetaAmplitude_pos
      zetaValueLower_pos
      zetaDiffCont
      zetaSphereBound
      zetaValueLower_bound)
    (CompletedZetaZeroExcisedStrip.InverseGammaBoundData.ofCauchyLogDerivative
      E
      separated
      gammaRadius
      gammaAmplitude
      gammaValueLower
      gammaRadius_pos
      gammaAmplitude_pos
      gammaValueLower_pos
      gammaDiffCont
      gammaSphereBound
      gammaValueLower_bound)

def CompletedZetaZeroExcisedStrip.FactorBoundData.empty
    (a b : ℝ) :
    CompletedZetaZeroExcisedStrip.FactorBoundData
      (CompletedZetaZeroExcisedStrip.empty a b) :=
  CompletedZetaZeroExcisedStrip.FactorBoundData.ofParts
    (CompletedZetaZeroExcisedStrip.ZetaSideBoundData.empty a b)
    (CompletedZetaZeroExcisedStrip.InverseGammaBoundData.empty a b)

def CompletedZetaZeroExcisedStrip.FactorBoundData.singleton
    {a b : ℝ}
    (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0)
    (separated :
      CompletedZetaZeroExcisedStrip.HasPositiveSingularSeparation
        (Boundary.LFunctions.ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.singleton
          z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma)) :
    CompletedZetaZeroExcisedStrip.FactorBoundData
      (Boundary.LFunctions.ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.singleton
        z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma) :=
  CompletedZetaZeroExcisedStrip.FactorBoundData.ofParts
    (CompletedZetaZeroExcisedStrip.ZetaSideBoundData.singleton
      z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma separated)
    (CompletedZetaZeroExcisedStrip.InverseGammaBoundData.singleton
      z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma separated)

def CompletedZetaZeroExcisedStrip.FactorBoundData.singleton_of_lower_bounds
    {a b : ℝ}
    (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0)
    (δ : ℝ)
    (δ_pos : 0 < δ)
    (δ_zero : δ ≤ ‖z₀‖)
    (δ_one : δ ≤ ‖z₀ - 1‖)
    (δ_completedZero :
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δ ≤ ‖z₀ - ((1 / 2 : ℂ) + (ρ : ℂ))‖)
    (δ_gammaPole :
      ∀ n : ℕ, δ ≤ ‖z₀ - (-(2 * (n : ℂ)))‖) :
    CompletedZetaZeroExcisedStrip.FactorBoundData
      (CompletedZetaZeroExcisedStrip.singleton
        z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma) :=
  CompletedZetaZeroExcisedStrip.FactorBoundData.singleton
    z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma
    (CompletedZetaZeroExcisedStrip.HasPositiveSingularSeparation.singleton_of_lower_bounds
      z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma
      δ δ_pos δ_zero δ_one δ_completedZero δ_gammaPole)

def CompletedZetaZeroExcisedStrip.FactorBoundData.union
    {a b : ℝ} {E₁ E₂ : CompletedZetaZeroExcisedStrip a b}
    (data₁ : CompletedZetaZeroExcisedStrip.FactorBoundData E₁)
    (data₂ : CompletedZetaZeroExcisedStrip.FactorBoundData E₂) :
    CompletedZetaZeroExcisedStrip.FactorBoundData
      (CompletedZetaZeroExcisedStrip.union E₁ E₂) :=
  CompletedZetaZeroExcisedStrip.FactorBoundData.ofParts
    (CompletedZetaZeroExcisedStrip.ZetaSideBoundData.union
      data₁.zetaSide data₂.zetaSide)
    (CompletedZetaZeroExcisedStrip.InverseGammaBoundData.union
      data₁.inverseGamma data₂.inverseGamma)

structure CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
    (a b : ℝ) where
  carrier : CompletedZetaZeroExcisedStrip a b
  factorBound : CompletedZetaZeroExcisedStrip.FactorBoundData carrier

def CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.ofCarrier
    {a b : ℝ} (carrier : CompletedZetaZeroExcisedStrip a b)
    (factorBound : CompletedZetaZeroExcisedStrip.FactorBoundData carrier) :
    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier a b :=
  { carrier := carrier
    factorBound := factorBound }

def CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.empty
    (a b : ℝ) :
    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier a b :=
  CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.ofCarrier
    (CompletedZetaZeroExcisedStrip.empty a b)
    (CompletedZetaZeroExcisedStrip.FactorBoundData.empty a b)

def CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton
    {a b : ℝ}
    (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0)
    (separated :
      CompletedZetaZeroExcisedStrip.HasPositiveSingularSeparation
        (Boundary.LFunctions.ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.singleton
          z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma)) :
    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier a b :=
  CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.ofCarrier
    (CompletedZetaZeroExcisedStrip.singleton
      z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma)
    (CompletedZetaZeroExcisedStrip.FactorBoundData.singleton
      z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma separated)

def CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_lower_bounds
    {a b : ℝ}
    (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0)
    (δ : ℝ)
    (δ_pos : 0 < δ)
    (δ_zero : δ ≤ ‖z₀‖)
    (δ_one : δ ≤ ‖z₀ - 1‖)
    (δ_completedZero :
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δ ≤ ‖z₀ - ((1 / 2 : ℂ) + (ρ : ℂ))‖)
    (δ_gammaPole :
      ∀ n : ℕ, δ ≤ ‖z₀ - (-(2 * (n : ℂ)))‖) :
    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier a b :=
  CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.ofCarrier
    (CompletedZetaZeroExcisedStrip.singleton
      z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma)
    (CompletedZetaZeroExcisedStrip.FactorBoundData.singleton_of_lower_bounds
      z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma
      δ δ_pos δ_zero δ_one δ_completedZero δ_gammaPole)

theorem CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_lower_bounds_mem
    {a b : ℝ}
    (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0)
    (δ : ℝ)
    (δ_pos : 0 < δ)
    (δ_zero : δ ≤ ‖z₀‖)
    (δ_one : δ ≤ ‖z₀ - 1‖)
    (δ_completedZero :
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δ ≤ ‖z₀ - ((1 / 2 : ℂ) + (ρ : ℂ))‖)
    (δ_gammaPole :
      ∀ n : ℕ, δ ≤ ‖z₀ - (-(2 * (n : ℂ)))‖) :
    z₀ ∈
      (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_lower_bounds
        z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma
        δ δ_pos δ_zero δ_one δ_completedZero δ_gammaPole).carrier.carrier :=
  CompletedZetaZeroExcisedStrip.mem_singleton
    z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma

def CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_component_lower_bounds
    {a b : ℝ}
    (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0)
    (δZero δOne δCompleted δGamma : ℝ)
    (δZeroPos : 0 < δZero)
    (δOnePos : 0 < δOne)
    (δCompletedPos : 0 < δCompleted)
    (δGammaPos : 0 < δGamma)
    (δZeroBound : δZero ≤ ‖z₀‖)
    (δOneBound : δOne ≤ ‖z₀ - 1‖)
    (δCompletedBound :
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δCompleted ≤ ‖z₀ - ((1 / 2 : ℂ) + (ρ : ℂ))‖)
    (δGammaBound :
      ∀ n : ℕ, δGamma ≤ ‖z₀ - (-(2 * (n : ℂ)))‖) :
    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier a b :=
  let δLeft : ℝ := min δZero δOne
  let δRight : ℝ := min δCompleted δGamma
  let δ : ℝ := min δLeft δRight
  let δLeftPos : 0 < δLeft :=
    lt_min δZeroPos δOnePos
  let δRightPos : 0 < δRight :=
    lt_min δCompletedPos δGammaPos
  let δPos : 0 < δ :=
    lt_min δLeftPos δRightPos
  let δZeroLe : δ ≤ ‖z₀‖ :=
    le_trans
      (le_trans (min_le_left δLeft δRight) (min_le_left δZero δOne))
      δZeroBound
  let δOneLe : δ ≤ ‖z₀ - 1‖ :=
    le_trans
      (le_trans (min_le_left δLeft δRight) (min_le_right δZero δOne))
      δOneBound
  let δCompletedLe :
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δ ≤ ‖z₀ - ((1 / 2 : ℂ) + (ρ : ℂ))‖ :=
    fun ρ =>
      le_trans
        (le_trans (min_le_right δLeft δRight) (min_le_left δCompleted δGamma))
        (δCompletedBound ρ)
  let δGammaLe :
      ∀ n : ℕ, δ ≤ ‖z₀ - (-(2 * (n : ℂ)))‖ :=
    fun n =>
      le_trans
        (le_trans (min_le_right δLeft δRight) (min_le_right δCompleted δGamma))
        (δGammaBound n)
  CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_lower_bounds
    z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma
    δ δPos δZeroLe δOneLe δCompletedLe δGammaLe

theorem CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_component_lower_bounds_mem
    {a b : ℝ}
    (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0)
    (δZero δOne δCompleted δGamma : ℝ)
    (δZeroPos : 0 < δZero)
    (δOnePos : 0 < δOne)
    (δCompletedPos : 0 < δCompleted)
    (δGammaPos : 0 < δGamma)
    (δZeroBound : δZero ≤ ‖z₀‖)
    (δOneBound : δOne ≤ ‖z₀ - 1‖)
    (δCompletedBound :
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δCompleted ≤ ‖z₀ - ((1 / 2 : ℂ) + (ρ : ℂ))‖)
    (δGammaBound :
      ∀ n : ℕ, δGamma ≤ ‖z₀ - (-(2 * (n : ℂ)))‖) :
    z₀ ∈
      (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_component_lower_bounds
        z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma
        δZero δOne δCompleted δGamma
        δZeroPos δOnePos δCompletedPos δGammaPos
        δZeroBound δOneBound δCompletedBound δGammaBound).carrier.carrier :=
  CompletedZetaZeroExcisedStrip.mem_singleton
    z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma

theorem CompletedZetaZeroExcisedStrip.singleton_zero_half_norm_component_radius
    (z₀ : ℂ) (hz₀_zero : z₀ ≠ 0) :
    0 < ‖z₀‖ / 2 ∧ ‖z₀‖ / 2 ≤ ‖z₀‖ :=
  And.intro
    (half_pos (norm_pos_iff.mpr hz₀_zero))
    (half_le_self (norm_nonneg z₀))

theorem CompletedZetaZeroExcisedStrip.singleton_one_half_norm_component_radius
    (z₀ : ℂ) (hz₀_one : z₀ ≠ 1) :
    0 < ‖z₀ - 1‖ / 2 ∧ ‖z₀ - 1‖ / 2 ≤ ‖z₀ - 1‖ :=
  And.intro
    (half_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hz₀_one)))
    (half_le_self (norm_nonneg (z₀ - 1)))

def CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_singular_component_lower_bounds
    {a b : ℝ}
    (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0)
    (δCompleted δGamma : ℝ)
    (δCompletedPos : 0 < δCompleted)
    (δGammaPos : 0 < δGamma)
    (δCompletedBound :
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δCompleted ≤ ‖z₀ - ((1 / 2 : ℂ) + (ρ : ℂ))‖)
    (δGammaBound :
      ∀ n : ℕ, δGamma ≤ ‖z₀ - (-(2 * (n : ℂ)))‖) :
    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier a b :=
  let zeroRadius :=
    CompletedZetaZeroExcisedStrip.singleton_zero_half_norm_component_radius
      z₀ hz₀_zero
  let oneRadius :=
    CompletedZetaZeroExcisedStrip.singleton_one_half_norm_component_radius
      z₀ hz₀_one
  CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_component_lower_bounds
    z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma
    (‖z₀‖ / 2) (‖z₀ - 1‖ / 2) δCompleted δGamma
    zeroRadius.1 oneRadius.1 δCompletedPos δGammaPos
    zeroRadius.2 oneRadius.2 δCompletedBound δGammaBound

theorem CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_singular_component_lower_bounds_mem
    {a b : ℝ}
    (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0)
    (δCompleted δGamma : ℝ)
    (δCompletedPos : 0 < δCompleted)
    (δGammaPos : 0 < δGamma)
    (δCompletedBound :
      ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
        δCompleted ≤ ‖z₀ - ((1 / 2 : ℂ) + (ρ : ℂ))‖)
    (δGammaBound :
      ∀ n : ℕ, δGamma ≤ ‖z₀ - (-(2 * (n : ℂ)))‖) :
    z₀ ∈
      (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.singleton_of_singular_component_lower_bounds
        z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma
        δCompleted δGamma δCompletedPos δGammaPos
        δCompletedBound δGammaBound).carrier.carrier :=
  CompletedZetaZeroExcisedStrip.mem_singleton
    z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma

def CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.union
    {a b : ℝ}
    (left right : CompletedZetaZeroExcisedStrip.FactorBoundedCarrier a b) :
    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier a b :=
  CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.ofCarrier
    (CompletedZetaZeroExcisedStrip.union left.carrier right.carrier)
    (CompletedZetaZeroExcisedStrip.FactorBoundData.union
      left.factorBound right.factorBound)

theorem CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_left
    {a b : ℝ}
    (left right : CompletedZetaZeroExcisedStrip.FactorBoundedCarrier a b)
    {z : ℂ} (hz : z ∈ left.carrier.carrier) :
    z ∈ (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.union
      left right).carrier.carrier :=
  CompletedZetaZeroExcisedStrip.mem_union_left
    left.carrier right.carrier hz

theorem CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_right
    {a b : ℝ}
    (left right : CompletedZetaZeroExcisedStrip.FactorBoundedCarrier a b)
    {z : ℂ} (hz : z ∈ right.carrier.carrier) :
    z ∈ (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.union
      left right).carrier.carrier :=
  CompletedZetaZeroExcisedStrip.mem_union_right
    left.carrier right.carrier hz

theorem CompletedZetaZeroExcisedStrip.FactorBoundData.completed_bound
    {a b : ℝ} {E : CompletedZetaZeroExcisedStrip a b}
    (data : CompletedZetaZeroExcisedStrip.FactorBoundData E)
    (N : ℕ) (z : ℂ) (hz : z ∈ E.carrier) :
    ‖completedZetaNegLogDeriv z‖ ≤
      (data.zetaSide.constant N + data.inverseGamma.constant N) *
        (1 + ‖z.im‖) ^ N :=
  completedZetaNegLogDeriv_bound_of_separated_factorBoundData
    E data.zetaSide data.inverseGamma N z hz

def CompletedZetaNegLogDerivZetaSideControl.ofFactorBoundData
    (data :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    CompletedZetaNegLogDerivZetaSideControl :=
  CompletedZetaNegLogDerivZetaSideControl.ofBoundData
    (fun a b E => (data a b E).zetaSide)

def CompletedZetaNegLogDerivInverseGammaControl.ofFactorBoundData
    (data :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    CompletedZetaNegLogDerivInverseGammaControl :=
  CompletedZetaNegLogDerivInverseGammaControl.ofBoundData
    (fun a b E => (data a b E).inverseGamma)

def CompletedZetaNegLogDerivControl.ofFactorBoundData
    (f : ZetaAdmissibleFunction)
    (data :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    CompletedZetaNegLogDerivControl f :=
  CompletedZetaNegLogDerivControl.ofSuppliedConstants
    f
    (fun a b E N =>
      (data a b E).zetaSide.constant N +
        (data a b E).inverseGamma.constant N)
    (fun a b E N =>
      add_pos
        ((data a b E).zetaSide.constant_pos N)
        ((data a b E).inverseGamma.constant_pos N))
    (fun a b E N z hz =>
      (data a b E).completed_bound N z hz)

def completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorBoundData
    (data :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    CompletedZetaNegLogDerivAutocorrelationConcreteControl :=
  completedZetaNegLogDerivAutocorrelationConcreteControl_of_boundData_owner
    (fun a b E => (data a b E).zetaSide)
    (fun a b E => (data a b E).inverseGamma)

def completedZetaNegLogDerivAutocorrelationConcreteControl_of_cauchyLogDerivative_owner
    (separated :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        E.HasPositiveSingularSeparation)
    (zetaRadius zetaAmplitude zetaValueLower :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b), ℕ → ℝ)
    (gammaRadius gammaAmplitude gammaValueLower :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b), ℕ → ℝ)
    (zetaRadius_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < zetaRadius a b E N)
    (zetaAmplitude_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < zetaAmplitude a b E N)
    (zetaValueLower_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < zetaValueLower a b E N)
    (gammaRadius_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < gammaRadius a b E N)
    (gammaAmplitude_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < gammaAmplitude a b E N)
    (gammaValueLower_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < gammaValueLower a b E N)
    (zetaDiffCont :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        DiffContOnCl ℂ zetaSideFactor
          (Metric.ball z (zetaRadius a b E N)))
    (zetaSphereBound :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (zetaRadius a b E N) →
          ‖zetaSideFactor w‖ ≤
            zetaAmplitude a b E N * (1 + ‖z.im‖) ^ N)
    (zetaValueLower_bound :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        zetaValueLower a b E N ≤ ‖zetaSideFactor z‖)
    (gammaDiffCont :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        DiffContOnCl ℂ
          (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (Metric.ball z (gammaRadius a b E N)))
    (gammaSphereBound :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (gammaRadius a b E N) →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤
            gammaAmplitude a b E N * (1 + ‖z.im‖) ^ N)
    (gammaValueLower_bound :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        gammaValueLower a b E N ≤ ‖(Complex.Gammaℝ z)⁻¹‖) :
    CompletedZetaNegLogDerivAutocorrelationConcreteControl :=
  completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorBoundData
    (fun a b E =>
      CompletedZetaZeroExcisedStrip.FactorBoundData.ofCauchyLogDerivative
        E
        (separated a b E)
        (zetaRadius a b E)
        (zetaAmplitude a b E)
        (zetaValueLower a b E)
        (gammaRadius a b E)
        (gammaAmplitude a b E)
        (gammaValueLower a b E)
        (zetaRadius_pos a b E)
        (zetaAmplitude_pos a b E)
        (zetaValueLower_pos a b E)
        (gammaRadius_pos a b E)
        (gammaAmplitude_pos a b E)
        (gammaValueLower_pos a b E)
        (zetaDiffCont a b E)
        (zetaSphereBound a b E)
        (zetaValueLower_bound a b E)
        (gammaDiffCont a b E)
        (gammaSphereBound a b E)
        (gammaValueLower_bound a b E))

def completedZetaNegLogDerivControl_autocorrelation_of_factorBoundData_owner
    (data :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    ∀ f : ZetaAdmissibleFunction,
      CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  completedZetaNegLogDerivControl_autocorrelation_of_concreteControl
    (completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorBoundData
      data)

def completedZetaNegLogDerivControl_autocorrelation_of_cauchyLogDerivative_owner
    (separated :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        E.HasPositiveSingularSeparation)
    (zetaRadius zetaAmplitude zetaValueLower :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b), ℕ → ℝ)
    (gammaRadius gammaAmplitude gammaValueLower :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b), ℕ → ℝ)
    (zetaRadius_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < zetaRadius a b E N)
    (zetaAmplitude_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < zetaAmplitude a b E N)
    (zetaValueLower_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < zetaValueLower a b E N)
    (gammaRadius_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < gammaRadius a b E N)
    (gammaAmplitude_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < gammaAmplitude a b E N)
    (gammaValueLower_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < gammaValueLower a b E N)
    (zetaDiffCont :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        DiffContOnCl ℂ zetaSideFactor
          (Metric.ball z (zetaRadius a b E N)))
    (zetaSphereBound :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (zetaRadius a b E N) →
          ‖zetaSideFactor w‖ ≤
            zetaAmplitude a b E N * (1 + ‖z.im‖) ^ N)
    (zetaValueLower_bound :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        zetaValueLower a b E N ≤ ‖zetaSideFactor z‖)
    (gammaDiffCont :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        DiffContOnCl ℂ
          (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (Metric.ball z (gammaRadius a b E N)))
    (gammaSphereBound :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (gammaRadius a b E N) →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤
            gammaAmplitude a b E N * (1 + ‖z.im‖) ^ N)
    (gammaValueLower_bound :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        gammaValueLower a b E N ≤ ‖(Complex.Gammaℝ z)⁻¹‖) :
    ∀ f : ZetaAdmissibleFunction,
      CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  completedZetaNegLogDerivControl_autocorrelation_of_concreteControl
    (completedZetaNegLogDerivAutocorrelationConcreteControl_of_cauchyLogDerivative_owner
      separated
      zetaRadius
      zetaAmplitude
      zetaValueLower
      gammaRadius
      gammaAmplitude
      gammaValueLower
      zetaRadius_pos
      zetaAmplitude_pos
      zetaValueLower_pos
      gammaRadius_pos
      gammaAmplitude_pos
      gammaValueLower_pos
      zetaDiffCont
      zetaSphereBound
      zetaValueLower_bound
      gammaDiffCont
      gammaSphereBound
      gammaValueLower_bound)

/-- Completed-log-derivative control on separated zero-excised carriers.

This is the valid global surface for completed-log-derivative estimates:
pointwise exclusion from the singular locus is not enough for a uniform bound,
so every carrier bound carries its positive singular-separation proof. -/
structure CompletedZetaNegLogDerivSeparatedControl
    (f : ZetaAdmissibleFunction) where
  constant :
    ∀ {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b),
      E.HasPositiveSingularSeparation → ℕ → ℝ
  constant_pos :
    ∀ {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b)
      (separated : E.HasPositiveSingularSeparation) (N : ℕ),
      0 < constant E separated N
  bound :
    ∀ {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b)
      (separated : E.HasPositiveSingularSeparation) (N : ℕ)
      (z : ℂ),
      z ∈ E.carrier →
      ‖completedZetaNegLogDeriv z‖ ≤
        constant E separated N * (1 + ‖z.im‖) ^ N

def CompletedZetaNegLogDerivSeparatedControl.ofFactorBoundData
    (f : ZetaAdmissibleFunction)
    (data :
      ∀ {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b),
        E.HasPositiveSingularSeparation →
          CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    CompletedZetaNegLogDerivSeparatedControl f :=
  { constant :=
      fun E separated N =>
        (data E separated).zetaSide.constant N +
          (data E separated).inverseGamma.constant N
    constant_pos :=
      fun E separated N =>
        add_pos
          ((data E separated).zetaSide.constant_pos N)
          ((data E separated).inverseGamma.constant_pos N)
    bound :=
      fun E separated N z hz =>
        (data E separated).completed_bound N z hz }

theorem CompletedZetaNegLogDerivSeparatedControl.bound_of_mem
    {f : ZetaAdmissibleFunction}
    (control : CompletedZetaNegLogDerivSeparatedControl f)
    {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b)
    (separated : E.HasPositiveSingularSeparation) (N : ℕ)
    (z : ℂ) (hz : z ∈ E.carrier) :
    ‖completedZetaNegLogDeriv z‖ ≤
      control.constant E separated N * (1 + ‖z.im‖) ^ N :=
  control.bound E separated N z hz

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
