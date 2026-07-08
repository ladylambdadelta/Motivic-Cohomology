import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineLineMeasurability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffinePhiDecay
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineKernelMajorantPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PaleyWienerFourierInversion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeNaturalTimeArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeRightTermKernelAlgebra
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledKernelLimitTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.SymmetricIntegralExhaustion
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Right von Mangoldt affine-kernel inversion

This file owns the Dirichlet/Mellin inversion step identifying the right
von Mangoldt affine kernel with the right one-sided natural prime
contribution.  The public prime contribution is obtained only after adding the
complementary left/reflected natural contribution and then transporting through
exhaustion.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped ENNReal
open scoped LSeries.notation
open scoped NNReal
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The right affine von Mangoldt factor unfolds to the Mathlib Dirichlet
`LSeries.term` expansion. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_eq_tsum_terms
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    (L ↗Λ) (zetaCompletedExplicitFormulaRightAffineLine F t) =
      ∑' n : ℕ,
        LSeries.term (↗Λ)
          (zetaCompletedExplicitFormulaRightAffineLine F t) n := by
  rfl

/-- The right affine von Mangoldt kernel after unfolding the Dirichlet-series
factor.  This is the exact normal form used before sum-integral exchange. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_eq_tsum_terms_mul_phi
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t =
      (∑' n : ℕ,
        LSeries.term (↗Λ)
          (zetaCompletedExplicitFormulaRightAffineLine F t) n) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) := by
  exact
    Eq.trans
      (congrArg
        (fun z : ℂ =>
          z * zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t))
        (zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_eq_logDerivative
          F t).symm)
      (congrArg
        (fun z : ℂ =>
          z * zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t))
        (zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_eq_tsum_terms
          F t))

/-- Fixed-time summability of the right von Mangoldt term kernels. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_summable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) :
    Summable
      (fun n : ℕ =>
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
          f F n t) := by
  let phi : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)
  let term : ℕ → ℂ := fun n : ℕ =>
    LSeries.term (↗Λ)
      (zetaCompletedExplicitFormulaRightAffineLine F t) n
  have hterm_summable : Summable term :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_terms_complex_summable
      F t
  have hmul_summable : Summable (fun n : ℕ => term n * phi) :=
    Summable.mul_right phi hterm_summable
  have hkernel :
      (fun n : ℕ => term n * phi) =
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
            f F n t) := by
    funext n
    exact Eq.refl _
  exact
    Eq.subst
      (motive := fun φ : ℕ → ℂ => Summable φ)
      hkernel
      hmul_summable

/-- Fixed-time absolute summability of the right von Mangoldt term kernels. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_norm_summable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) :
    Summable
      (fun n : ℕ =>
        ‖zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
          f F n t‖) := by
  let phi : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)
  let termNorm : ℕ → ℝ := fun n : ℕ =>
    ‖LSeries.term (↗Λ)
      (zetaCompletedExplicitFormulaRightAffineLine F t) n‖
  have hterm_norm_summable : Summable termNorm :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_terms_summable
      F t
  have hmul_summable :
      Summable (fun n : ℕ => termNorm n * ‖phi‖) :=
    Summable.mul_right ‖phi‖ hterm_norm_summable
  have hkernel_norm :
      (fun n : ℕ => termNorm n * ‖phi‖) =
        (fun n : ℕ =>
          ‖zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
            f F n t‖) := by
    funext n
    exact
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_norm_eq
        f F n t).symm
  exact
    Eq.subst
      (motive := fun φ : ℕ → ℝ => Summable φ)
      hkernel_norm
      hmul_summable

/-- The right von Mangoldt term kernel is bounded by the absolute Dirichlet
term times the rapid-decay majorant for `Φ_f`. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_norm_le_term_mul_phiMajorant
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N n : ℕ) (t : ℝ) :
    ‖zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel f F n t‖
      ≤ ‖LSeries.term (↗Λ)
          (zetaCompletedExplicitFormulaRightAffineLine F t) n‖ *
        (h.phi_control.verticalStripRapidDecayConstant
          (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) N *
          (1 + ‖t‖) ^ (-(N : ℤ))) := by
  let term : ℂ :=
    LSeries.term (↗Λ)
      (zetaCompletedExplicitFormulaRightAffineLine F t) n
  let phi : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)
  let majorant : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) N *
      (1 + ‖t‖) ^ (-(N : ℤ))
  have hnorm :
      ‖zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel f F n t‖ =
        ‖term‖ * ‖phi‖ :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_norm_eq
      f F n t
  have hphi : ‖phi‖ ≤ majorant :=
    zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_decay_bound
      f F h N t
  have hterm_nonneg : 0 ≤ ‖term‖ :=
    norm_nonneg term
  have hmul : ‖term‖ * ‖phi‖ ≤ ‖term‖ * majorant :=
    mul_le_mul_of_nonneg_left hphi hterm_nonneg
  exact hnorm.trans_le hmul

/-- The pointwise norm series of right von Mangoldt term kernels is controlled
by the fixed absolute Dirichlet-series bound and the rapid-decay majorant for
`Φ_f`. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_tsum_norm_le_factorBound_mul_phiMajorant
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (t : ℝ) :
    (∑' n : ℕ,
      ‖zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
        f F n t‖)
      ≤ zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
        (h.phi_control.verticalStripRapidDecayConstant
          (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) N *
          (1 + ‖t‖) ^ (-(N : ℤ))) := by
  let phi : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)
  let termNorm : ℕ → ℝ := fun n : ℕ =>
    ‖LSeries.term (↗Λ)
      (zetaCompletedExplicitFormulaRightAffineLine F t) n‖
  let baseNorm : ℕ → ℝ := fun n : ℕ =>
    ‖LSeries.term (↗Λ) (F.c : ℂ) n‖
  let majorant : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) N *
      (1 + ‖t‖) ^ (-(N : ℤ))
  have hterm_summable : Summable termNorm :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_terms_summable
      F t
  have hkernel_norm :
      (fun n : ℕ =>
        ‖zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
          f F n t‖) =
        (fun n : ℕ => termNorm n * ‖phi‖) := by
    funext n
    exact
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_norm_eq
        f F n t
  have hsum_kernel :
      (∑' n : ℕ,
        ‖zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
          f F n t‖) =
        (∑' n : ℕ, termNorm n * ‖phi‖) :=
    congrArg
      (fun ψ : ℕ → ℝ => ∑' n : ℕ, ψ n)
      hkernel_norm
  have hsum_mul :
      (∑' n : ℕ, termNorm n * ‖phi‖) =
        (∑' n : ℕ, termNorm n) * ‖phi‖ :=
    Summable.tsum_mul_right ‖phi‖ hterm_summable
  have hterm_base :
      termNorm = baseNorm := by
    funext n
    exact
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_term_norm_eq
        F t n
  have hsum_base :
      (∑' n : ℕ, termNorm n) =
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F := by
    exact
      Eq.trans
        (congrArg
          (fun ψ : ℕ → ℝ => ∑' n : ℕ, ψ n)
          hterm_base)
        (Eq.refl _)
  have hphi : ‖phi‖ ≤ majorant :=
    zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_decay_bound
      f F h N t
  have hB_nonneg :
      0 ≤ zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound_nonneg F
  calc
    (∑' n : ℕ,
      ‖zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
        f F n t‖) =
        (∑' n : ℕ, termNorm n * ‖phi‖) := hsum_kernel
    _ = (∑' n : ℕ, termNorm n) * ‖phi‖ := hsum_mul
    _ = zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
          ‖phi‖ := by
      exact
        congrArg
          (fun x : ℝ => x * ‖phi‖)
          hsum_base
    _ ≤ zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
          majorant := by
      exact mul_le_mul_of_nonneg_left hphi hB_nonneg

/-- Continuity of a fixed Dirichlet-series term along the right affine line. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_term_rightAffineLine_continuous
    (F : ExplicitFormulaContourFamily) (n : ℕ) :
    Continuous
      (fun t : ℝ =>
        LSeries.term (↗Λ)
          (zetaCompletedExplicitFormulaRightAffineLine F t) n) := by
  by_cases hn : n = 0
  · have hfun :
        (fun t : ℝ =>
          LSeries.term (↗Λ)
            (zetaCompletedExplicitFormulaRightAffineLine F t) n) =
          (fun _t : ℝ => (0 : ℂ)) := by
      funext t
      exact
        Eq.subst
          (motive := fun m : ℕ =>
            LSeries.term (↗Λ)
              (zetaCompletedExplicitFormulaRightAffineLine F t) m = 0)
          hn.symm
          (LSeries.term_zero (↗Λ)
            (zetaCompletedExplicitFormulaRightAffineLine F t))
    exact
      Eq.subst
        (motive := fun φ : ℝ → ℂ => Continuous φ)
        hfun.symm
        continuous_const
  · let line : ℝ → ℂ := fun t : ℝ =>
      zetaCompletedExplicitFormulaRightAffineLine F t
    let denom : ℝ → ℂ := fun t : ℝ => (n : ℂ) ^ line t
    have hline : Continuous line :=
      zetaCompletedExplicitFormulaRightAffineLine_continuous F
    have hbase_ne : (n : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hn
    have hdenom_cont : Continuous denom :=
      hline.const_cpow (Or.inl hbase_ne)
    have hdenom_ne : ∀ t : ℝ, denom t ≠ 0 := by
      intro t hzero
      have hbase_zero :
          (n : ℂ) = 0 :=
        (Complex.cpow_eq_zero_iff (n : ℂ) (line t)).mp hzero |>.1
      exact hbase_ne hbase_zero
    have hquot :
        Continuous
          (fun t : ℝ => (↗Λ : ℕ → ℂ) n / denom t) :=
      continuous_const.div hdenom_cont hdenom_ne
    have hfun :
        (fun t : ℝ =>
          LSeries.term (↗Λ)
            (zetaCompletedExplicitFormulaRightAffineLine F t) n) =
          (fun t : ℝ => (↗Λ : ℕ → ℂ) n / denom t) := by
      funext t
      exact LSeries.term_of_ne_zero hn (↗Λ) (line t)
    exact
      Eq.subst
        (motive := fun φ : ℝ → ℂ => Continuous φ)
        hfun.symm
        hquot

/-- Strong measurability of each right von Mangoldt Dirichlet-term kernel. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_aestronglyMeasurable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (n : ℕ) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
          f F n t)
      (volume : Measure ℝ) := by
  have hterm :
      AEStronglyMeasurable
        (fun t : ℝ =>
          LSeries.term (↗Λ)
            (zetaCompletedExplicitFormulaRightAffineLine F t) n)
        (volume : Measure ℝ) :=
    (zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_term_rightAffineLine_continuous
      F n).aestronglyMeasurable
  have hphi :
      AEStronglyMeasurable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_aestronglyMeasurable
      f F h
  exact hterm.mul hphi

/-- The inverse-quadratic majorant used to dominate the right von Mangoldt
term-kernel norm series is integrable on the real line. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_majorant_two_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
          h.phi_control.verticalStripRapidDecayConstant
            (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 2 *
          (1 + ‖t‖) ^ (-(2 : ℤ)))
      (volume : Measure ℝ) := by
  let B : ℝ :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 2
  let majorantInt : ℝ → ℝ := fun t : ℝ =>
    B * C * (1 + ‖t‖) ^ (-(2 : ℤ))
  let majorantReal : ℝ → ℝ := fun t : ℝ =>
    B * C * (1 + ‖t‖) ^ (-(2 : ℝ))
  have hfinrank : Module.finrank ℝ ℝ = 1 :=
    Module.finrank_self ℝ
  have hfinrank_cast : ((Module.finrank ℝ ℝ : ℕ) : ℝ) = 1 :=
    Eq.trans
      (congrArg (fun n : ℕ => (n : ℝ)) hfinrank)
      Nat.cast_one
  have hdim : (Module.finrank ℝ ℝ : ℝ) < 2 :=
    Eq.subst
      (motive := fun x : ℝ => x < 2)
      hfinrank_cast.symm
      one_lt_two
  have hbase :
      Integrable
        (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ)))
        (volume : Measure ℝ) :=
    integrable_one_add_norm (E := ℝ) hdim
  have hscaled :
      Integrable
        (fun t : ℝ => B * (C * (1 + ‖t‖) ^ (-(2 : ℝ))))
        (volume : Measure ℝ) :=
    (hbase.const_mul C).const_mul B
  have hscaled_eq_real :
      (fun t : ℝ => B * (C * (1 + ‖t‖) ^ (-(2 : ℝ)))) =
        majorantReal := by
    funext t
    exact (mul_assoc B C ((1 + ‖t‖) ^ (-(2 : ℝ)))).symm
  have hreal : Integrable majorantReal (volume : Measure ℝ) :=
    Eq.subst
      (motive := fun φ : ℝ → ℝ => Integrable φ (volume : Measure ℝ))
      hscaled_eq_real
      hscaled
  have hint_eq_real : majorantInt = majorantReal := by
    funext t
    have hexp :
        ((-(2 : ℤ) : ℤ) : ℝ) = -(2 : ℝ) :=
      Int.cast_neg 2
    have hpow :
        (1 + ‖t‖) ^ (-(2 : ℤ)) =
          (1 + ‖t‖) ^ (-(2 : ℝ)) :=
      Eq.trans
        (Real.rpow_intCast (1 + ‖t‖) (-(2 : ℤ))).symm
        (congrArg (fun r : ℝ => (1 + ‖t‖) ^ r) hexp)
    exact congrArg (fun x : ℝ => B * C * x) hpow
  have hint : Integrable majorantInt (volume : Measure ℝ) :=
    Eq.subst
      (motive := fun φ : ℝ → ℝ => Integrable φ (volume : Measure ℝ))
      hint_eq_real.symm
      hreal
  exact hint

/-- The inverse-quadratic majorant is nonnegative pointwise.  This records the
sign information coming from the fact that it dominates a norm series. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_majorant_two_nonneg
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (t : ℝ) :
    0 ≤
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
        h.phi_control.verticalStripRapidDecayConstant
          (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 2 *
        (1 + ‖t‖) ^ (-(2 : ℤ)) := by
  have hbound :
      (∑' n : ℕ,
        ‖zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
          f F n t‖)
        ≤ zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
          (h.phi_control.verticalStripRapidDecayConstant
            (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 2 *
            (1 + ‖t‖) ^ (-(2 : ℤ))) :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_tsum_norm_le_factorBound_mul_phiMajorant
      f F h 2 t
  have hleft_nonneg :
      0 ≤
        (∑' n : ℕ,
          ‖zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
            f F n t‖) :=
    tsum_nonneg
      (fun n : ℕ =>
        norm_nonneg
          (zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
            f F n t))
  have hassoc :
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
          (h.phi_control.verticalStripRapidDecayConstant
            (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 2 *
            (1 + ‖t‖) ^ (-(2 : ℤ))) =
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
          h.phi_control.verticalStripRapidDecayConstant
            (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 2 *
          (1 + ‖t‖) ^ (-(2 : ℤ)) :=
    (mul_assoc
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F)
      (h.phi_control.verticalStripRapidDecayConstant
        (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 2)
      ((1 + ‖t‖) ^ (-(2 : ℤ)))).symm
  exact hleft_nonneg.trans (hbound.trans_eq hassoc)

/-- Tonelli converts the summed `lintegral` of term-kernel norms into the
`lintegral` of the pointwise norm series, which is bounded by the
inverse-quadratic majorant. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_lintegral_norm_tsum_le_majorant_two_lintegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∑' n : ℕ,
      ∫⁻ t : ℝ,
        (‖zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
          f F n t‖₊ : ℝ≥0∞) ∂(volume : Measure ℝ))
      ≤
    ∫⁻ t : ℝ,
      ENNReal.ofReal
        (zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
          h.phi_control.verticalStripRapidDecayConstant
            (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 2 *
          (1 + ‖t‖) ^ (-(2 : ℤ))) ∂(volume : Measure ℝ) := by
  let kernel : ℕ → ℝ → ℂ := fun n t =>
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel f F n t
  let majorant : ℝ → ℝ := fun t : ℝ =>
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
      h.phi_control.verticalStripRapidDecayConstant
        (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 2 *
      (1 + ‖t‖) ^ (-(2 : ℤ))
  have hmeas :
      ∀ n : ℕ,
        AEMeasurable (fun t : ℝ => (‖kernel n t‖₊ : ℝ≥0∞))
          (volume : Measure ℝ) :=
    fun n : ℕ =>
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_aestronglyMeasurable
        f F h n).ennnorm
  have htonelli :
      (∑' n : ℕ,
        ∫⁻ t : ℝ, (‖kernel n t‖₊ : ℝ≥0∞) ∂(volume : Measure ℝ)) =
        ∫⁻ t : ℝ,
          ∑' n : ℕ, (‖kernel n t‖₊ : ℝ≥0∞) ∂(volume : Measure ℝ) :=
    (MeasureTheory.lintegral_tsum hmeas).symm
  have hpointwise :
      ∀ t : ℝ,
        (∑' n : ℕ, (‖kernel n t‖₊ : ℝ≥0∞)) ≤
          ENNReal.ofReal (majorant t) := by
    intro t
    let normSeries : ℕ → ℝ := fun n : ℕ => ‖kernel n t‖
    have hnorm_nonneg : ∀ n : ℕ, 0 ≤ normSeries n :=
      fun n : ℕ => norm_nonneg (kernel n t)
    have hnorm_summable : Summable normSeries :=
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_norm_summable
        f F t
    have hcoe_terms :
        (fun n : ℕ => (‖kernel n t‖₊ : ℝ≥0∞)) =
          fun n : ℕ => ENNReal.ofReal (normSeries n) := by
      funext n
      exact (ofReal_norm_eq_coe_nnnorm (kernel n t)).symm
    have hcoe_tsum :
        (∑' n : ℕ, (‖kernel n t‖₊ : ℝ≥0∞)) =
          ENNReal.ofReal (∑' n : ℕ, normSeries n) := by
      exact
        Eq.trans
          (congrArg tsum hcoe_terms)
          (ENNReal.ofReal_tsum_of_nonneg hnorm_nonneg hnorm_summable).symm
    have hreal_bound :
        (∑' n : ℕ, normSeries n) ≤ majorant t := by
      have hbound :
          (∑' n : ℕ,
            ‖zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
              f F n t‖)
            ≤ zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
              (h.phi_control.verticalStripRapidDecayConstant
                (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 2 *
                (1 + ‖t‖) ^ (-(2 : ℤ))) :=
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_tsum_norm_le_factorBound_mul_phiMajorant
          f F h 2 t
      have hnorm_tsum :
          (∑' n : ℕ, normSeries n) =
            (∑' n : ℕ,
              ‖zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
                f F n t‖) :=
        Eq.refl _
      have hassoc :
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
              (h.phi_control.verticalStripRapidDecayConstant
                (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 2 *
                (1 + ‖t‖) ^ (-(2 : ℤ))) =
            majorant t :=
        (mul_assoc
          (zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F)
          (h.phi_control.verticalStripRapidDecayConstant
            (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 2)
          ((1 + ‖t‖) ^ (-(2 : ℤ)))).symm
      exact hnorm_tsum.trans_le (hbound.trans_eq hassoc)
    exact hcoe_tsum.trans_le (ENNReal.ofReal_le_ofReal hreal_bound)
  exact
    htonelli.trans_le
      (MeasureTheory.lintegral_mono hpointwise)

/-- The summed `lintegral` of the right von Mangoldt Dirichlet-term kernel
norms is finite.  This is the exact integrability input required by
`MeasureTheory.integral_tsum`. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_lintegral_norm_tsum_ne_top
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∑' n : ℕ,
      ∫⁻ t : ℝ,
        (‖zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
          f F n t‖₊ : ℝ≥0∞) ∂(volume : Measure ℝ)) ≠ ∞ := by
  let majorant : ℝ → ℝ := fun t : ℝ =>
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F *
      h.phi_control.verticalStripRapidDecayConstant
        (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 2 *
      (1 + ‖t‖) ^ (-(2 : ℤ))
  have hle :
      (∑' n : ℕ,
        ∫⁻ t : ℝ,
          (‖zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
            f F n t‖₊ : ℝ≥0∞) ∂(volume : Measure ℝ))
        ≤
      ∫⁻ t : ℝ, ENNReal.ofReal (majorant t) ∂(volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_lintegral_norm_tsum_le_majorant_two_lintegral
      f F h
  have hmajorant_integrable :
      Integrable majorant (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_majorant_two_integrable
      f F h
  have hmajorant_nonneg :
      0 ≤ᵐ[(volume : Measure ℝ)] majorant :=
    Eventually.of_forall
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_majorant_two_nonneg
          f F h t)
  have hmajorant_lintegral_eq :
      ENNReal.ofReal (∫ t : ℝ, majorant t ∂(volume : Measure ℝ)) =
        ∫⁻ t : ℝ, ENNReal.ofReal (majorant t) ∂(volume : Measure ℝ) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      hmajorant_integrable hmajorant_nonneg
  have hmajorant_lintegral_ne_top :
      (∫⁻ t : ℝ, ENNReal.ofReal (majorant t) ∂(volume : Measure ℝ)) ≠ ∞ := by
    exact
      Eq.subst
        (motive := fun x : ℝ≥0∞ => x ≠ ∞)
        hmajorant_lintegral_eq
        ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hmajorant_lintegral_ne_top hle

/-- The right affine von Mangoldt kernel is the `tsum` of its Dirichlet-term
kernels. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_eq_tsum_termKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t =
      ∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
          f F n t := by
  let phi : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)
  let term : ℕ → ℂ := fun n : ℕ =>
    LSeries.term (↗Λ)
      (zetaCompletedExplicitFormulaRightAffineLine F t) n
  have hkernel :
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t =
        (∑' n : ℕ, term n) * phi :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_eq_tsum_terms_mul_phi
      f F t
  have hterm_summable : Summable term :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_terms_complex_summable
      F t
  have hmul :
      (∑' n : ℕ, term n) * phi =
        ∑' n : ℕ, term n * phi :=
    (Summable.tsum_mul_right phi hterm_summable).symm
  have hterm_kernel :
      (fun n : ℕ => term n * phi) =
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
            f F n t) := by
    funext n
    exact Eq.refl _
  exact
    Eq.trans hkernel
      (Eq.trans hmul
        (congrArg
          (fun φ : ℕ → ℂ => ∑' n : ℕ, φ n)
          hterm_kernel))

/-- Sum-integral exchange for the right von Mangoldt Dirichlet-term kernels.

This is exactly the dominated-convergence/Fubini step.  Its proof uses the
affine majorants and the absolute Dirichlet-series bound on `Re s = F.c`; it
contains no prime-power arithmetic. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integral_eq_tsum_termKernel_integrals_ownerExchange
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t) =
      ∑' n : ℕ,
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
            f F n t := by
  have hpointwise :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t) =
        (fun t : ℝ =>
          ∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
              f F n t) := by
    funext t
    exact
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_eq_tsum_termKernel
        f F t
  have hmeas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
              f F n t)
          (volume : Measure ℝ) :=
    fun n : ℕ =>
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_aestronglyMeasurable
        f F h n
  have hfinite :
      (∑' n : ℕ,
        ∫⁻ t : ℝ,
          (‖zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
            f F n t‖₊ : ℝ≥0∞) ∂(volume : Measure ℝ)) ≠ ∞ :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_lintegral_norm_tsum_ne_top
      f F h
  have hexchange :
      (∫ t : ℝ,
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
            f F n t) =
        ∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
              f F n t :=
    MeasureTheory.integral_tsum hmeas hfinite
  exact
    Eq.trans
      (congrArg
        (fun φ : ℝ → ℂ => ∫ t : ℝ, φ t)
        hpointwise)
      hexchange

/-- The explicit time-side prime-power `tsum` is the analytic-core
prime-power contribution. -/
theorem zetaCompletedExplicitFormula_timePrimePowerTsum_eq_primePowerContribution
    (f : ZetaAdmissibleFunction) :
    ((∑' ι : ZetaPrimePowerIndex,
      -(ZetaPrimePowerIndex.weight ι *
        Complex.re
          (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι) +
        star (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι))))) : ℂ) =
      zetaCompletedExplicitFormulaPrimePowerContribution f := by
  rfl

/-- The zero natural-index one-sided Mellin identity is pure Dirichlet-term
algebra. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_integral_eq_primeNaturalOneSidedTimeSample_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
        f F 0 t) =
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f 0 := by
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_integral_zero
        f F)
      (zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_zero f).symm

/-- Compatibility wrapper: the positive natural-index Mellin inversion for a
right von Mangoldt Dirichlet monomial.

The analytic Paley-Wiener/Fourier sampling theorem is owned upstream in
`PaleyWienerFourierInversion` / `PaleyWienerProjectSampling`; this theorem
only transports that monomial value across the right von Mangoldt term-kernel
normal form. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_integral_eq_primeNaturalOneSidedTimeSample_pos_ownerMellin
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
        f F n t) =
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n := by
  have hkernel :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
          f F n t) =
        fun t : ℝ =>
          ((↗Λ) n /
              (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) := by
    funext t
    exact
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_eq_of_ne_zero
        f F hn t
  exact
    Eq.trans
      (congrArg
        (fun φ : ℝ → ℂ => ∫ t : ℝ, φ t)
        hkernel)
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtPositiveMonomial_integral_eq_primeNaturalOneSidedTimeSample_ownerFourierInversion
        f F h hn)

/-- Single natural-index Mellin inversion, with the degenerate zero term
discharged separately from the positive analytic leaf. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_integral_eq_primeNaturalOneSidedTimeSample_ownerMellin
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (n : ℕ) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
        f F n t) =
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n := by
  by_cases hn : n = 0
  · exact
      Eq.subst
        (motive := fun m : ℕ =>
          (∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
              f F m t) =
            zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f m)
        hn.symm
        (zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_integral_eq_primeNaturalOneSidedTimeSample_zero
          f F)
  · exact
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_integral_eq_primeNaturalOneSidedTimeSample_pos_ownerMellin
        f F h hn

/-- Termwise Mellin inversion summed over natural indices.

The analytic content is the preceding pointwise theorem; this wrapper only
changes equal summands under `tsum`.  Sum-integral exchange and prime-power
arithmetic remain separate lemmas below. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_integrals_tsum_eq_primeNaturalOneSidedTimeTsum_ownerMellin
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∑' n : ℕ,
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
          f F n t) =
      ∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n := by
  exact
    tsum_congr
      (fun n : ℕ =>
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_integral_eq_primeNaturalOneSidedTimeSample_ownerMellin
          f F h n)

/-- Whole-line right von Mangoldt inversion from the local Mellin inversion and
sum-integral exchange, landing at the one-sided natural contribution. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integral_eq_primeNaturalOneSidedContribution_direct_ownerInversion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t) =
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f := by
  have hexchange :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t) =
        ∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
              f F n t :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integral_eq_tsum_termKernel_integrals_ownerExchange
      f F h
  have hmellin :
      (∑' n : ℕ,
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
            f F n t) =
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_integrals_tsum_eq_primeNaturalOneSidedTimeTsum_ownerMellin
      f F h
  have hdef :
      (∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n) =
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f :=
    (zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution_eq_tsum f).symm
  exact
    Eq.trans hexchange
      (Eq.trans hmellin hdef)

/-- Honest two-face arithmetic target for the right von Mangoldt whole-line
inversion: the proved right one-sided integral plus the complementary natural
prime contribution is the public prime contribution. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integral_add_complementContribution_eq_primeContribution_ownerInversion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t) +
        zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f =
      zetaCompletedExplicitFormulaPrimeContribution f := by
  have hright :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t) =
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integral_eq_primeNaturalOneSidedContribution_direct_ownerInversion
      f F h
  have hrecombine :
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f +
          zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f =
        zetaCompletedExplicitFormulaPrimeContribution f :=
    zetaCompletedExplicitFormulaPrimeNaturalOneSided_add_complementContribution_eq_primeContribution
      f
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        z + zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f =
          zetaCompletedExplicitFormulaPrimeContribution f)
      hright.symm
      hrecombine

/-- Strong measurability of the right von Mangoldt affine kernel, proved at
the inversion owner level so exhaustion transport does not depend on downstream
prime-channel estimates. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_aestronglyMeasurable_ownerInversion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    AEStronglyMeasurable
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaPrimeLogDerivative_rightAffineLine_continuous
    F).aestronglyMeasurable.mul
      (zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_aestronglyMeasurable
        f F h)

/-- Bundled owner-level majorant package for the right von Mangoldt affine
kernel. -/
def zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_majorantPackage_ownerInversion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F) := by
  let B : ℝ :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 2
  let majorant : ℝ → ℝ := fun t : ℝ =>
    B * (C * (1 + ‖t‖) ^ (-(2 : ℤ)))
  have hintegrable :
      Integrable majorant (volume : Measure ℝ) := by
    have hfinrank : Module.finrank ℝ ℝ = 1 :=
      Module.finrank_self ℝ
    have hfinrank_cast : ((Module.finrank ℝ ℝ : ℕ) : ℝ) = 1 :=
      Eq.trans
        (congrArg (fun n : ℕ => (n : ℝ)) hfinrank)
        Nat.cast_one
    have hdim : (Module.finrank ℝ ℝ : ℝ) < 2 :=
      Eq.subst
        (motive := fun x : ℝ => x < 2)
        hfinrank_cast.symm
        one_lt_two
    have hbase :
        Integrable
          (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ)))
          (volume : Measure ℝ) :=
      integrable_one_add_norm (E := ℝ) hdim
    have hscaled :
        Integrable
          (fun t : ℝ => B * (C * (1 + ‖t‖) ^ (-(2 : ℝ))))
          (volume : Measure ℝ) :=
      (hbase.const_mul C).const_mul B
    have hfun :
        majorant =
          (fun t : ℝ => B * (C * (1 + ‖t‖) ^ (-(2 : ℝ)))) := by
      funext t
      have hexp :
          ((-(2 : ℤ) : ℤ) : ℝ) = -(2 : ℝ) :=
        Int.cast_neg 2
      have hpow :
          (1 + ‖t‖) ^ (-(2 : ℤ)) =
            (1 + ‖t‖) ^ (-(2 : ℝ)) :=
        Eq.trans
          (Real.rpow_intCast (1 + ‖t‖) (-(2 : ℤ))).symm
          (congrArg (fun r : ℝ => (1 + ‖t‖) ^ r) hexp)
      exact congrArg (fun x : ℝ => B * (C * x)) hpow
    exact Eq.subst
      (motive := fun φ : ℝ → ℝ => Integrable φ (volume : Measure ℝ))
      hfun.symm
      hscaled
  have hfactor_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F t))
        (volume : Measure ℝ) :=
    (zetaCompletedExplicitFormulaPrimeLogDerivative_rightAffineLine_continuous
      F).aestronglyMeasurable
  have hphi_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_aestronglyMeasurable
      f F h
  have hbound :
      ∀ᵐ t ∂(volume : Measure ℝ),
        ‖explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F t)‖ *
            ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)‖
          ≤ majorant t :=
    Filter.Eventually.of_forall
      (fun t : ℝ =>
        let factor : ℂ :=
          explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F t)
        let phi : ℂ :=
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)
        let weight : ℝ := (1 + ‖t‖) ^ (-(2 : ℤ))
        have hfactor_eq :
            factor =
              (L ↗Λ) (zetaCompletedExplicitFormulaRightAffineLine F t) :=
          (zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_eq_logDerivative
            F t).symm
        have hfactor_norm_eq :
            ‖factor‖ =
              ‖(L ↗Λ) (zetaCompletedExplicitFormulaRightAffineLine F t)‖ :=
          congrArg (fun z : ℂ => ‖z‖) hfactor_eq
        have hfactor_L :
            ‖(L ↗Λ) (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤ B :=
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_norm_le_bound
            F t
        have hfactor : ‖factor‖ ≤ B :=
          Eq.subst
            (motive := fun x : ℝ => x ≤ B)
            hfactor_norm_eq.symm
            hfactor_L
        have hphi : ‖phi‖ ≤ C * weight :=
          zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_decay_bound
            f F h 2 t
        have hphi_nonneg : 0 ≤ ‖phi‖ :=
          norm_nonneg phi
        have hB_nonneg : 0 ≤ B :=
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound_nonneg F
        have hprod : ‖factor‖ * ‖phi‖ ≤ B * (C * weight) :=
          mul_le_mul hfactor hphi hphi_nonneg hB_nonneg
        have hassoc : B * (C * weight) = B * (C * weight) :=
          Eq.refl _
        hprod.trans_eq hassoc)
  exact
    ExplicitFormulaAffineKernelMajorantPackage.of_mul_le
      majorant hintegrable hfactor_meas hphi_meas hbound

/-- Owner-level integrability of the right von Mangoldt affine kernel. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integrable_ownerInversion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_majorantPackage_ownerInversion
    f F h).integrable

/-- Scheduled-window convergence of the right von Mangoldt affine kernel to its
whole-line integral, kept at owner level for acyclic prime inversion. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_integral_ownerInversion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)) := by
  have hsymmetric :
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)) :=
    explicitFormulaSymmetricIntervalIntegral_tendsto_integral
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F)
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integrable_ownerInversion
        f F h)
  let K : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle T).T)
        (F.rectangle T).T,
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t
  have hrectangle :
      Tendsto K atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)) :=
    explicitFormulaRectangleWindowIntegral_tendsto_of_symmetric
      F
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
      hsymmetric
  exact
    explicitFormulaScheduledScalar_tendsto_of_unscheduled
      K
      h.height_schedule.height
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
      hrectangle
      h.height_schedule.cofinal

/-- Owner scheduled right von Mangoldt one-sided inversion, transported from
the whole-line Mellin inversion value and scheduled-window exhaustion. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_primeNaturalOneSidedContribution_direct_ownerInversion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f)) := by
  have hintegral :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)) :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_integral_ownerInversion
      f F h
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            ∫ t in Set.Icc
                (-(F.rectangle (h.height_schedule.height u)).T)
                (F.rectangle (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
          atTop
          (𝓝 z))
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integral_eq_primeNaturalOneSidedContribution_direct_ownerInversion
        f F h)
      hintegral

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
