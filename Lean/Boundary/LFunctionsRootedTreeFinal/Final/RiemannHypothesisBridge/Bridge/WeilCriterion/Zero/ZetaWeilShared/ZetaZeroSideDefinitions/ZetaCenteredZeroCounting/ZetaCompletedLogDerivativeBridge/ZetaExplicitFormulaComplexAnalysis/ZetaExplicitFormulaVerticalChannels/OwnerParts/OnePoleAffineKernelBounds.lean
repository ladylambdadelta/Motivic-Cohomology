import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineCauchyKernelBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineLineMeasurability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffinePhiDecay
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Pointwise bounds for the one-pole affine kernel

This file combines the affine `s = 1` Cauchy bounds with rapid decay of `Φ_f`.
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

noncomputable def zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernelMajorant
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (t : ℝ) : ℝ :=
  ((1 : ℝ) / (F.c - 1)) *
    h.phi_control.verticalStripRapidDecayConstant
      (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) N *
      (1 + ‖t‖) ^ (-(N : ℤ))

noncomputable def zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernelMajorant
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (t : ℝ) : ℝ :=
  ((1 : ℝ) / (-((1 - F.c) - 1))) *
    h.phi_control.verticalStripRapidDecayConstant
      ((1 : ℝ) - F.c - (1 / 2 : ℝ))
      ((1 : ℝ) - F.c - (1 / 2 : ℝ)) N *
      (1 + ‖t‖) ^ (-(N : ℤ))

theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_norm_le_majorant
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (t : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t‖
      ≤ zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernelMajorant
          f F h N t := by
  let cauchy : ℂ :=
    -(1 / (zetaCompletedExplicitFormulaRightAffineLine F t - 1))
  let phi : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) N
  let weight : ℝ := (1 + ‖t‖) ^ (-(N : ℤ))
  have hkernel_norm :
      ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t‖ =
        ‖cauchy‖ * ‖phi‖ :=
    norm_mul cauchy phi
  have hcauchy : ‖cauchy‖ ≤ (1 : ℝ) / (F.c - 1) :=
    zetaCompletedExplicitFormulaRightAffineLine_onePoleCoefficient_norm_le F t
  have hphi : ‖phi‖ ≤ C * weight :=
    zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_decay_bound f F h N t
  have hphi_bound_nonneg : 0 ≤ C * weight :=
    (norm_nonneg phi).trans hphi
  have hcauchy_bound_nonneg : 0 ≤ (1 : ℝ) / (F.c - 1) :=
    (norm_nonneg cauchy).trans hcauchy
  have hprod :
      ‖cauchy‖ * ‖phi‖ ≤ ((1 : ℝ) / (F.c - 1)) * (C * weight) :=
    mul_le_mul hcauchy hphi (norm_nonneg phi) hcauchy_bound_nonneg
  have hmajorant_assoc :
      ((1 : ℝ) / (F.c - 1)) * (C * weight) =
        ((1 : ℝ) / (F.c - 1)) * C * weight :=
    (mul_assoc ((1 : ℝ) / (F.c - 1)) C weight).symm
  exact
    (le_of_eq hkernel_norm).trans
      (hprod.trans_eq hmajorant_assoc)

theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_norm_le_majorant
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (t : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t‖
      ≤ zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernelMajorant
          f F h N t := by
  let cauchy : ℂ :=
    -(1 / (zetaCompletedExplicitFormulaLeftAffineLine F t - 1))
  let phi : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      ((1 : ℝ) - F.c - (1 / 2 : ℝ))
      ((1 : ℝ) - F.c - (1 / 2 : ℝ)) N
  let weight : ℝ := (1 + ‖t‖) ^ (-(N : ℤ))
  have hkernel_norm :
      ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t‖ =
        ‖cauchy‖ * ‖phi‖ :=
    norm_mul cauchy phi
  have hcauchy : ‖cauchy‖ ≤ (1 : ℝ) / (-((1 - F.c) - 1)) :=
    zetaCompletedExplicitFormulaLeftAffineLine_onePoleCoefficient_norm_le F t
  have hphi : ‖phi‖ ≤ C * weight :=
    zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_decay_bound f F h N t
  have hphi_bound_nonneg : 0 ≤ C * weight :=
    (norm_nonneg phi).trans hphi
  have hcauchy_bound_nonneg : 0 ≤ (1 : ℝ) / (-((1 - F.c) - 1)) :=
    (norm_nonneg cauchy).trans hcauchy
  have hprod :
      ‖cauchy‖ * ‖phi‖ ≤
        ((1 : ℝ) / (-((1 - F.c) - 1))) * (C * weight) :=
    mul_le_mul hcauchy hphi (norm_nonneg phi) hcauchy_bound_nonneg
  have hmajorant_assoc :
      ((1 : ℝ) / (-((1 - F.c) - 1))) * (C * weight) =
        ((1 : ℝ) / (-((1 - F.c) - 1))) * C * weight :=
    (mul_assoc ((1 : ℝ) / (-((1 - F.c) - 1))) C weight).symm
  exact
    (le_of_eq hkernel_norm).trans
      (hprod.trans_eq hmajorant_assoc)

theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernelMajorant_two_eq_rpow
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (t : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernelMajorant
        f F h 2 t =
      ((1 : ℝ) / (F.c - 1)) *
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
      ((1 : ℝ) / (F.c - 1)) *
        h.phi_control.verticalStripRapidDecayConstant
          (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 2 *
          x)
    hpow

theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernelMajorant_two_eq_rpow
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (t : ℝ) :
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernelMajorant
        f F h 2 t =
      ((1 : ℝ) / (-((1 - F.c) - 1))) *
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
      ((1 : ℝ) / (-((1 - F.c) - 1))) *
        h.phi_control.verticalStripRapidDecayConstant
          ((1 : ℝ) - F.c - (1 / 2 : ℝ))
          ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 2 *
          x)
    hpow

theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernelMajorant_two_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernelMajorant
          f F h 2 t)
      (volume : Measure ℝ) := by
  let A : ℝ := (1 : ℝ) / (F.c - 1)
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
        zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernelMajorant
          f F h 2 t) =
      (fun t : ℝ => A * (C * (1 + ‖t‖) ^ (-(2 : ℝ)))) := by
    funext t
    exact Eq.trans
      (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernelMajorant_two_eq_rpow
        f F h t)
      (mul_assoc A C ((1 + ‖t‖) ^ (-(2 : ℝ))))
  exact Eq.subst
    (motive := fun φ : ℝ → ℝ => Integrable φ (volume : Measure ℝ))
    hfun.symm
    hscaled

theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernelMajorant_two_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernelMajorant
          f F h 2 t)
      (volume : Measure ℝ) := by
  let A : ℝ := (1 : ℝ) / (-((1 - F.c) - 1))
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
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernelMajorant
          f F h 2 t) =
      (fun t : ℝ => A * (C * (1 + ‖t‖) ^ (-(2 : ℝ)))) := by
    funext t
    exact Eq.trans
      (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernelMajorant_two_eq_rpow
        f F h t)
      (mul_assoc A C ((1 + ‖t‖) ^ (-(2 : ℝ))))
  exact Eq.subst
    (motive := fun φ : ℝ → ℝ => Integrable φ (volume : Measure ℝ))
    hfun.symm
    hscaled

theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_continuous
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Continuous
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t) := by
  have hline :
      Continuous (fun t : ℝ => zetaCompletedExplicitFormulaRightAffineLine F t) :=
    zetaCompletedExplicitFormulaRightAffineLine_continuous F
  have hone : Continuous (fun _t : ℝ => (1 : ℂ)) :=
    continuous_const
  have hden :
      Continuous (fun t : ℝ => zetaCompletedExplicitFormulaRightAffineLine F t - 1) :=
    hline.sub hone
  have hden_ne :
      ∀ t : ℝ, zetaCompletedExplicitFormulaRightAffineLine F t - 1 ≠ 0 :=
    fun t hzero =>
      zetaCompletedExplicitFormulaRightAffineLine_ne_one F t
        (sub_eq_zero.mp hzero)
  have hcauchy :
      Continuous
        (fun t : ℝ => -(1 / (zetaCompletedExplicitFormulaRightAffineLine F t - 1))) :=
    (continuous_const.div hden hden_ne).neg
  have hphi :
      Continuous
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) :=
    zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_continuous f F h
  exact hcauchy.mul hphi

theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_continuous
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Continuous
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t) := by
  have hline :
      Continuous (fun t : ℝ => zetaCompletedExplicitFormulaLeftAffineLine F t) :=
    zetaCompletedExplicitFormulaLeftAffineLine_continuous F
  have hone : Continuous (fun _t : ℝ => (1 : ℂ)) :=
    continuous_const
  have hden :
      Continuous (fun t : ℝ => zetaCompletedExplicitFormulaLeftAffineLine F t - 1) :=
    hline.sub hone
  have hden_ne :
      ∀ t : ℝ, zetaCompletedExplicitFormulaLeftAffineLine F t - 1 ≠ 0 :=
    fun t hzero =>
      zetaCompletedExplicitFormulaLeftAffineLine_ne_one F t
        (sub_eq_zero.mp hzero)
  have hcauchy :
      Continuous
        (fun t : ℝ => -(1 / (zetaCompletedExplicitFormulaLeftAffineLine F t - 1))) :=
    (continuous_const.div hden hden_ne).neg
  have hphi :
      Continuous
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) :=
    zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_continuous f F h
  exact hcauchy.mul hphi

theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_aestronglyMeasurable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    AEStronglyMeasurable
      (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_continuous
    f F h).aestronglyMeasurable

theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_aestronglyMeasurable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    AEStronglyMeasurable
      (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_continuous
    f F h).aestronglyMeasurable

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
