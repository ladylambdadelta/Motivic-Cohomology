import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineCauchyKernelBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineLineMeasurability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffinePhiDecay
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Pointwise bounds for the zero-pole affine kernel

This file combines the right-line Cauchy bound with the vertical-strip rapid
decay of `Φ_f`.  Integrability and whole-line inversion are deliberately kept in
their owner files.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The standard decaying majorant used for the isolated right `s = 0`
zero-pole affine kernel. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelMajorant
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (t : ℝ) : ℝ :=
  ((1 : ℝ) / F.c) *
    h.phi_control.verticalStripRapidDecayConstant
      (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) N *
      (1 + ‖t‖) ^ (-(N : ℤ))

/-- The standard decaying majorant used for the isolated left `s = 0`
zero-pole affine kernel. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernelMajorant
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (t : ℝ) : ℝ :=
  ((1 : ℝ) / (-(1 - F.c))) *
    h.phi_control.verticalStripRapidDecayConstant
      ((1 : ℝ) - F.c - (1 / 2 : ℝ))
      ((1 : ℝ) - F.c - (1 / 2 : ℝ)) N *
      (1 + ‖t‖) ^ (-(N : ℤ))

/-- The zero-pole affine-kernel majorant is nonnegative. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelMajorant_nonneg
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (t : ℝ) :
    0 ≤
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelMajorant
        f F h N t := by
  have hc_pos : 0 < (1 : ℝ) / F.c :=
    div_pos zero_lt_one F.c_pos
  have hC_pos :
      0 <
        h.phi_control.verticalStripRapidDecayConstant
          (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) N :=
    h.phi_control.verticalStripRapidDecayConstant_pos
      (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) N
  have hbase_nonneg : 0 ≤ 1 + ‖t‖ :=
    add_nonneg zero_le_one (norm_nonneg t)
  have hweight_nonneg :
      0 ≤ (1 + ‖t‖) ^ (-(N : ℤ)) :=
    zpow_nonneg hbase_nonneg (-(N : ℤ))
  exact
    mul_nonneg
      (mul_nonneg (le_of_lt hc_pos) (le_of_lt hC_pos))
      hweight_nonneg

/-- The left zero-pole affine-kernel majorant is nonnegative. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernelMajorant_nonneg
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (t : ℝ) :
    0 ≤
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernelMajorant
        f F h N t := by
  have hden_pos : 0 < -(1 - F.c) :=
    neg_pos.mpr F.one_sub_c_neg
  have hc_pos : 0 < (1 : ℝ) / (-(1 - F.c)) :=
    div_pos zero_lt_one hden_pos
  have hC_pos :
      0 <
        h.phi_control.verticalStripRapidDecayConstant
          ((1 : ℝ) - F.c - (1 / 2 : ℝ))
          ((1 : ℝ) - F.c - (1 / 2 : ℝ)) N :=
    h.phi_control.verticalStripRapidDecayConstant_pos
      ((1 : ℝ) - F.c - (1 / 2 : ℝ))
      ((1 : ℝ) - F.c - (1 / 2 : ℝ)) N
  have hbase_nonneg : 0 ≤ 1 + ‖t‖ :=
    add_nonneg zero_le_one (norm_nonneg t)
  have hweight_nonneg :
      0 ≤ (1 + ‖t‖) ^ (-(N : ℤ)) :=
    zpow_nonneg hbase_nonneg (-(N : ℤ))
  exact
    mul_nonneg
      (mul_nonneg (le_of_lt hc_pos) (le_of_lt hC_pos))
      hweight_nonneg

/-- Pointwise majorization of the isolated right `s = 0` zero-pole affine
kernel by the standard Cauchy-times-rapid-decay majorant. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_norm_le_majorant
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (t : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t‖
      ≤ zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelMajorant
          f F h N t := by
  let cauchy : ℂ :=
    -1 / zetaCompletedExplicitFormulaRightAffineLine F t
  let phi : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) N
  let weight : ℝ := (1 + ‖t‖) ^ (-(N : ℤ))
  have hkernel_norm :
      ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t‖ =
        ‖cauchy‖ * ‖phi‖ :=
    norm_mul cauchy phi
  have hcauchy : ‖cauchy‖ ≤ (1 : ℝ) / F.c :=
    zetaCompletedExplicitFormulaRightAffineLine_zeroPoleCoefficient_norm_le F t
  have hphi : ‖phi‖ ≤ C * weight :=
    zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_decay_bound f F h N t
  have hphi_bound_nonneg : 0 ≤ C * weight :=
    (norm_nonneg phi).trans hphi
  have hcauchy_bound_nonneg : 0 ≤ (1 : ℝ) / F.c :=
    (norm_nonneg cauchy).trans hcauchy
  have hprod :
      ‖cauchy‖ * ‖phi‖ ≤ ((1 : ℝ) / F.c) * (C * weight) :=
    mul_le_mul hcauchy hphi (norm_nonneg phi) hcauchy_bound_nonneg
  have hmajorant_assoc :
      ((1 : ℝ) / F.c) * (C * weight) =
        ((1 : ℝ) / F.c) * C * weight :=
    (mul_assoc ((1 : ℝ) / F.c) C weight).symm
  exact
    (le_of_eq hkernel_norm).trans
      (hprod.trans_eq hmajorant_assoc)

/-- Pointwise majorization of the isolated left `s = 0` zero-pole affine
kernel by the standard Cauchy-times-rapid-decay majorant. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_norm_le_majorant
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (t : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t‖
      ≤ zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernelMajorant
          f F h N t := by
  let cauchy : ℂ :=
    -1 / zetaCompletedExplicitFormulaLeftAffineLine F t
  let phi : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      ((1 : ℝ) - F.c - (1 / 2 : ℝ))
      ((1 : ℝ) - F.c - (1 / 2 : ℝ)) N
  let weight : ℝ := (1 + ‖t‖) ^ (-(N : ℤ))
  have hkernel_norm :
      ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t‖ =
        ‖cauchy‖ * ‖phi‖ :=
    norm_mul cauchy phi
  have hcauchy : ‖cauchy‖ ≤ (1 : ℝ) / (-(1 - F.c)) :=
    zetaCompletedExplicitFormulaLeftAffineLine_zeroPoleCoefficient_norm_le F t
  have hphi : ‖phi‖ ≤ C * weight :=
    zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_decay_bound f F h N t
  have hphi_bound_nonneg : 0 ≤ C * weight :=
    (norm_nonneg phi).trans hphi
  have hcauchy_bound_nonneg : 0 ≤ (1 : ℝ) / (-(1 - F.c)) :=
    (norm_nonneg cauchy).trans hcauchy
  have hprod :
      ‖cauchy‖ * ‖phi‖ ≤ ((1 : ℝ) / (-(1 - F.c))) * (C * weight) :=
    mul_le_mul hcauchy hphi (norm_nonneg phi) hcauchy_bound_nonneg
  have hmajorant_assoc :
      ((1 : ℝ) / (-(1 - F.c))) * (C * weight) =
        ((1 : ℝ) / (-(1 - F.c))) * C * weight :=
    (mul_assoc ((1 : ℝ) / (-(1 - F.c))) C weight).symm
  exact
    (le_of_eq hkernel_norm).trans
      (hprod.trans_eq hmajorant_assoc)

/-- The second-order zero-pole affine majorant is the corresponding real-power
Japanese-bracket majorant. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelMajorant_two_eq_rpow
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (t : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelMajorant
        f F h 2 t =
      ((1 : ℝ) / F.c) *
        h.phi_control.verticalStripRapidDecayConstant
          (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 2 *
          (1 + ‖t‖) ^ (-(2 : ℝ)) := by
  have hpow :
      (1 + ‖t‖) ^ (-(2 : ℤ)) =
        (1 + ‖t‖) ^ (-(2 : ℝ)) :=
    have hexp : ((-2 : ℤ) : ℝ) = -(2 : ℝ) :=
      Int.cast_negOfNat 2
    Eq.trans
      (Real.rpow_intCast (1 + ‖t‖) (-(2 : ℤ))).symm
      (congrArg (fun r : ℝ => (1 + ‖t‖) ^ r) hexp)
  exact congrArg
    (fun x : ℝ =>
      ((1 : ℝ) / F.c) *
        h.phi_control.verticalStripRapidDecayConstant
          (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 2 *
          x)
    hpow

/-- The second-order left zero-pole affine majorant is the corresponding
real-power Japanese-bracket majorant. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernelMajorant_two_eq_rpow
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (t : ℝ) :
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernelMajorant
        f F h 2 t =
      ((1 : ℝ) / (-(1 - F.c))) *
        h.phi_control.verticalStripRapidDecayConstant
          ((1 : ℝ) - F.c - (1 / 2 : ℝ))
          ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 2 *
          (1 + ‖t‖) ^ (-(2 : ℝ)) := by
  have hpow :
      (1 + ‖t‖) ^ (-(2 : ℤ)) =
        (1 + ‖t‖) ^ (-(2 : ℝ)) :=
    have hexp : ((-2 : ℤ) : ℝ) = -(2 : ℝ) :=
      Int.cast_negOfNat 2
    Eq.trans
      (Real.rpow_intCast (1 + ‖t‖) (-(2 : ℤ))).symm
      (congrArg (fun r : ℝ => (1 + ‖t‖) ^ r) hexp)
  exact congrArg
    (fun x : ℝ =>
      ((1 : ℝ) / (-(1 - F.c))) *
        h.phi_control.verticalStripRapidDecayConstant
          ((1 : ℝ) - F.c - (1 / 2 : ℝ))
          ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 2 *
          x)
    hpow

/-- Integrability of the second-order zero-pole affine majorant. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelMajorant_two_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelMajorant
          f F h 2 t)
      (volume : Measure ℝ) := by
  let A : ℝ := (1 : ℝ) / F.c
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 2
  have hfinrank : Module.finrank ℝ ℝ = 1 :=
    Module.finrank_self ℝ
  have hfinrank_cast : ((Module.finrank ℝ ℝ : ℕ) : ℝ) = 1 :=
    Eq.trans (congrArg (fun n : ℕ => (n : ℝ)) hfinrank) Nat.cast_one
  have hdim : (Module.finrank ℝ ℝ : ℝ) < 2 :=
    Eq.subst
      (motive := fun x : ℝ => x < 2)
      hfinrank_cast.symm
      one_lt_two
  have hbase :
      Integrable
        (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ)))
        (volume : Measure ℝ) :=
    integrable_one_add_norm hdim
  have hscaled :
      Integrable
        (fun t : ℝ => A * (C * (1 + ‖t‖) ^ (-(2 : ℝ))))
        (volume : Measure ℝ) :=
    (hbase.const_mul C).const_mul A
  have hfun :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelMajorant
          f F h 2 t) =
      (fun t : ℝ => A * (C * (1 + ‖t‖) ^ (-(2 : ℝ)))) := by
    funext t
    exact Eq.trans
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelMajorant_two_eq_rpow
        f F h t)
      (mul_assoc A C ((1 + ‖t‖) ^ (-(2 : ℝ))))
  exact Eq.subst
    (motive := fun φ : ℝ → ℝ => Integrable φ (volume : Measure ℝ))
    hfun.symm
    hscaled

/-- Integrability of the second-order left zero-pole affine majorant. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernelMajorant_two_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernelMajorant
          f F h 2 t)
      (volume : Measure ℝ) := by
  let A : ℝ := (1 : ℝ) / (-(1 - F.c))
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      ((1 : ℝ) - F.c - (1 / 2 : ℝ))
      ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 2
  have hfinrank : Module.finrank ℝ ℝ = 1 :=
    Module.finrank_self ℝ
  have hfinrank_cast : ((Module.finrank ℝ ℝ : ℕ) : ℝ) = 1 :=
    Eq.trans (congrArg (fun n : ℕ => (n : ℝ)) hfinrank) Nat.cast_one
  have hdim : (Module.finrank ℝ ℝ : ℝ) < 2 :=
    Eq.subst
      (motive := fun x : ℝ => x < 2)
      hfinrank_cast.symm
      one_lt_two
  have hbase :
      Integrable
        (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ)))
        (volume : Measure ℝ) :=
    integrable_one_add_norm hdim
  have hscaled :
      Integrable
        (fun t : ℝ => A * (C * (1 + ‖t‖) ^ (-(2 : ℝ))))
        (volume : Measure ℝ) :=
    (hbase.const_mul C).const_mul A
  have hfun :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernelMajorant
          f F h 2 t) =
      (fun t : ℝ => A * (C * (1 + ‖t‖) ^ (-(2 : ℝ)))) := by
    funext t
    exact Eq.trans
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernelMajorant_two_eq_rpow
        f F h t)
      (mul_assoc A C ((1 + ‖t‖) ^ (-(2 : ℝ))))
  exact Eq.subst
    (motive := fun φ : ℝ → ℝ => Integrable φ (volume : Measure ℝ))
    hfun.symm
    hscaled

/-- Continuity of the isolated right `s = 0` zero-pole affine kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_continuous
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Continuous
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t) := by
  have hline :
      Continuous (fun t : ℝ => zetaCompletedExplicitFormulaRightAffineLine F t) :=
    zetaCompletedExplicitFormulaRightAffineLine_continuous F
  have hline_ne :
      ∀ t : ℝ, zetaCompletedExplicitFormulaRightAffineLine F t ≠ 0 :=
    fun t => zetaCompletedExplicitFormulaRightAffineLine_ne_zero F t
  have hcauchy :
      Continuous
        (fun t : ℝ => (-1 : ℂ) / zetaCompletedExplicitFormulaRightAffineLine F t) :=
    continuous_const.div hline hline_ne
  have hphi :
      Continuous
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) :=
    zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_continuous f F h
  exact hcauchy.mul hphi

/-- Continuity of the isolated left `s = 0` zero-pole affine kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_continuous
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Continuous
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t) := by
  have hline :
      Continuous (fun t : ℝ => zetaCompletedExplicitFormulaLeftAffineLine F t) :=
    zetaCompletedExplicitFormulaLeftAffineLine_continuous F
  have hline_ne :
      ∀ t : ℝ, zetaCompletedExplicitFormulaLeftAffineLine F t ≠ 0 :=
    fun t => zetaCompletedExplicitFormulaLeftAffineLine_ne_zero F t
  have hcauchy :
      Continuous
        (fun t : ℝ => (-1 : ℂ) / zetaCompletedExplicitFormulaLeftAffineLine F t) :=
    continuous_const.div hline hline_ne
  have hphi :
      Continuous
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) :=
    zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_continuous f F h
  exact hcauchy.mul hphi

/-- Strong measurability of the isolated right `s = 0` zero-pole affine kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_aestronglyMeasurable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    AEStronglyMeasurable
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_continuous
    f F h).aestronglyMeasurable

/-- Strong measurability of the isolated left `s = 0` zero-pole affine kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_aestronglyMeasurable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    AEStronglyMeasurable
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_continuous
    f F h).aestronglyMeasurable

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
