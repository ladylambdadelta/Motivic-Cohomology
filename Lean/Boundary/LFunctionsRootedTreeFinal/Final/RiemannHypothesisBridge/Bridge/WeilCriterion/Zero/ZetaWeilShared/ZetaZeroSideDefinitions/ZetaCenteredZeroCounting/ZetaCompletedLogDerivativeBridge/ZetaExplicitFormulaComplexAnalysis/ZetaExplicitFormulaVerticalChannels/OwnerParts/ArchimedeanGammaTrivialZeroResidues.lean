import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanWeilFunctional
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part02

/-!
# Gamma trivial-zero residues

This file specializes the generic analytic logarithmic-derivative residue
theorem to the simple zeros of the reciprocal completed real Gamma factor.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The analytic order at a Gamma trivial zero has natural value one. -/
theorem inverseGammaReal_order_toNat_eq_one_at_trivialZero
    (n : ℕ) :
    (Complex.differentiable_Gammaℝ_inv.analyticAt
      (zetaCompletedGammaTrivialZero n)).order.toNat = 1 := by
  let analyticGerm :
      AnalyticAt ℂ (fun s : ℂ => (Complex.Gammaℝ s)⁻¹)
        (zetaCompletedGammaTrivialZero n) :=
    Complex.differentiable_Gammaℝ_inv.analyticAt
      (zetaCompletedGammaTrivialZero n)
  have orderValue : analyticGerm.order = (1 : ℕ∞) := by
    unfold analyticGerm
    exact inverseGammaReal_order_eq_one_at_trivialZero n
  have naturalOrderValue :
      analyticGerm.order.toNat = (1 : ℕ∞).toNat :=
    congrArg ENat.toNat orderValue
  have oneNormalization : (1 : ℕ∞).toNat = 1 := by
    rfl
  exact Eq.trans naturalOrderValue oneNormalization

/-- The reciprocal real-Gamma logarithmic derivative has local residue one at
every Gamma trivial zero. -/
theorem inverseGammaReal_logDeriv_residue_tendsto_one_at_trivialZero
    (n : ℕ) :
    Tendsto
      (fun z : ℂ =>
        (z - zetaCompletedGammaTrivialZero n) *
          logDeriv (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) z)
      (𝓝[≠] (zetaCompletedGammaTrivialZero n))
      (𝓝 (1 : ℂ)) := by
  let point : ℂ := zetaCompletedGammaTrivialZero n
  let analyticGerm :
      AnalyticAt ℂ (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) point :=
    Complex.differentiable_Gammaℝ_inv.analyticAt point
  have valueZero : (Complex.Gammaℝ point)⁻¹ = 0 := by
    unfold point
    exact zetaCompletedGammaTrivialZero_inverseGammaReal_eq_zero n
  have notEventuallyZero :
      ¬ ∀ᶠ z in 𝓝 point, (Complex.Gammaℝ z)⁻¹ = 0 := by
    unfold point
    exact inverseGammaReal_not_eventually_zero_at_trivialZero n
  have residueAtOrder :
      Tendsto
        (fun z : ℂ =>
          (z - point) *
            logDeriv (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) z)
        (𝓝[≠] point)
        (𝓝 (analyticGerm.order.toNat : ℂ)) :=
    analyticAt_logDeriv_residue_tendsto_order_owner
      (fun s : ℂ => (Complex.Gammaℝ s)⁻¹)
      point analyticGerm valueZero notEventuallyZero
  have naturalOrderValue : analyticGerm.order.toNat = 1 := by
    unfold analyticGerm
    unfold point
    exact inverseGammaReal_order_toNat_eq_one_at_trivialZero n
  have complexOrderValue :
      (analyticGerm.order.toNat : ℂ) = (1 : ℂ) :=
    Eq.trans
      (congrArg (fun value : ℕ => (value : ℂ)) naturalOrderValue)
      (Nat.cast_one : ((1 : ℕ) : ℂ) = 1)
  exact Eq.subst
    (motive := fun residueValue : ℂ =>
      Tendsto
        (fun z : ℂ =>
          (z - point) *
            logDeriv (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) z)
        (𝓝[≠] point) (𝓝 residueValue))
    complexOrderValue
    residueAtOrder

/-- Multiplying the reciprocal-Gamma logarithmic derivative by the shifted
spectral transform gives the named Gamma trivial-zero residue coordinate. -/
theorem inverseGammaReal_PhiKernel_residue_tendsto_coordinate_at_trivialZero
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl f)
    (n : ℕ) :
    Tendsto
      (fun z : ℂ =>
        (z - zetaCompletedGammaTrivialZero n) *
          (logDeriv (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) z *
            zetaCompletedExplicitFormulaPhi f
              (z - (1 / 2 : ℂ))))
      (𝓝[≠] (zetaCompletedGammaTrivialZero n))
      (𝓝 (zetaCompletedGammaTrivialZeroResidueCoordinate f n)) := by
  let point : ℂ := zetaCompletedGammaTrivialZero n
  let residueKernel : ℂ → ℂ := fun z : ℂ =>
    (z - point) *
      logDeriv (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) z
  let shiftedPhi : ℂ → ℂ := fun z : ℂ =>
    zetaCompletedExplicitFormulaPhi f (z - (1 / 2 : ℂ))
  have residueLimit :
      Tendsto residueKernel (𝓝[≠] point) (𝓝 (1 : ℂ)) := by
    unfold residueKernel
    unfold point
    exact inverseGammaReal_logDeriv_residue_tendsto_one_at_trivialZero n
  have shiftedPhiContinuous : ContinuousAt shiftedPhi point := by
    unfold shiftedPhi
    exact
      (zetaCompletedExplicitFormulaPhi_shift_differentiableAt
        hPhi point).continuousAt
  have shiftedPhiLimit :
      Tendsto shiftedPhi (𝓝[≠] point) (𝓝 (shiftedPhi point)) :=
    shiftedPhiContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have productLimit :
      Tendsto (fun z : ℂ => residueKernel z * shiftedPhi z)
        (𝓝[≠] point) (𝓝 ((1 : ℂ) * shiftedPhi point)) :=
    residueLimit.mul shiftedPhiLimit
  have productFunctionEquality :
      (fun z : ℂ =>
        (z - point) *
          (logDeriv (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) z *
            shiftedPhi z)) =
      fun z : ℂ => residueKernel z * shiftedPhi z := by
    funext z
    unfold residueKernel
    exact
      (mul_assoc
        (z - point)
        (logDeriv (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) z)
        (shiftedPhi z)).symm
  have normalizedProductLimit :
      Tendsto
        (fun z : ℂ =>
          (z - point) *
            (logDeriv (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) z *
              shiftedPhi z))
        (𝓝[≠] point) (𝓝 ((1 : ℂ) * shiftedPhi point)) :=
    Eq.subst
      (motive := fun kernel : ℂ → ℂ =>
        Tendsto kernel (𝓝[≠] point)
          (𝓝 ((1 : ℂ) * shiftedPhi point)))
      productFunctionEquality.symm
      productLimit
  have targetNormalization :
      (1 : ℂ) * shiftedPhi point =
        zetaCompletedGammaTrivialZeroResidueCoordinate f n := by
    calc
      (1 : ℂ) * shiftedPhi point = shiftedPhi point :=
        one_mul (shiftedPhi point)
      _ = zetaCompletedExplicitFormulaPhi f
            (point - (1 / 2 : ℂ)) := by
        rfl
      _ = zetaCompletedGammaTrivialZeroResidueCoordinate f n := by
        unfold point
        rfl
  have targetLimit :
      Tendsto
        (fun z : ℂ =>
          (z - point) *
            (logDeriv (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) z *
              shiftedPhi z))
        (𝓝[≠] point)
        (𝓝 (zetaCompletedGammaTrivialZeroResidueCoordinate f n)) :=
    Eq.subst
      (motive := fun residueValue : ℂ =>
        Tendsto
          (fun z : ℂ =>
            (z - point) *
              (logDeriv (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) z *
                shiftedPhi z))
          (𝓝[≠] point) (𝓝 residueValue))
      targetNormalization
      normalizedProductLimit
  unfold shiftedPhi at targetLimit
  unfold point at targetLimit
  exact targetLimit

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
