import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineKernelMajorantPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineLineMeasurability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffinePhiDecay

/-!
# Affine centered product majorants

This file owns the common Paley-Wiener multiplication estimate for affine
vertical kernels: a linearly bounded factor times the centered transform
`Phi_f` is integrable.  Prime and archimedean channel files supply their own
factor measurability and linear bounds.
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

/-- A linearly bounded factor times the right centered test transform has an
integrable majorant. -/
def zetaCompletedExplicitFormulaRightCenteredAffineProduct_majorantPackage_of_linear_factor_bound_common
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A : ℝ → ℂ) (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hA_meas : AEStronglyMeasurable A (volume : Measure ℝ))
    (hA_bound : ∀ t : ℝ, ‖A t‖ ≤ B * (1 + ‖t‖)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (fun t : ℝ =>
        A t *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 4
  let majorant : ℝ → ℝ := fun t : ℝ => B * (C * (1 + ‖t‖) ^ (-(3 : ℤ)))
  have hintegrable :
      Integrable majorant (volume : Measure ℝ) := by
    have hfinrank : Module.finrank ℝ ℝ = 1 :=
      Module.finrank_self ℝ
    have hfinrank_cast : ((Module.finrank ℝ ℝ : ℕ) : ℝ) = 1 :=
      Eq.trans
        (congrArg (fun n : ℕ => (n : ℝ)) hfinrank)
        Nat.cast_one
    have htwo_add_one_eq_three : (2 : ℝ) + 1 = 3 :=
      two_add_one_eq_three
    have htwo_lt_three : (2 : ℝ) < 3 :=
      Eq.subst
        (motive := fun x : ℝ => (2 : ℝ) < x)
        htwo_add_one_eq_three
        (lt_add_of_pos_right (2 : ℝ) zero_lt_one)
    have hdim : (Module.finrank ℝ ℝ : ℝ) < 3 :=
      Eq.subst
        (motive := fun x : ℝ => x < 3)
        hfinrank_cast.symm
        (lt_trans one_lt_two htwo_lt_three)
    have hbase :
        Integrable
          (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℝ)))
          (volume : Measure ℝ) :=
      integrable_one_add_norm (E := ℝ) hdim
    have hscaled :
        Integrable
          (fun t : ℝ => B * (C * (1 + ‖t‖) ^ (-(3 : ℝ))))
          (volume : Measure ℝ) :=
      (hbase.const_mul C).const_mul B
    have hfun :
        majorant =
          (fun t : ℝ => B * (C * (1 + ‖t‖) ^ (-(3 : ℝ)))) := by
      funext t
      have hexp :
          ((-(3 : ℤ) : ℤ) : ℝ) = -(3 : ℝ) :=
        Int.cast_neg 3
      have hpow :
          (1 + ‖t‖) ^ (-(3 : ℤ)) =
            (1 + ‖t‖) ^ (-(3 : ℝ)) :=
        Eq.trans
          (Real.rpow_intCast (1 + ‖t‖) (-(3 : ℤ))).symm
          (congrArg (fun r : ℝ => (1 + ‖t‖) ^ r) hexp)
      exact congrArg (fun x : ℝ => B * (C * x)) hpow
    exact
      Eq.subst
        (motive := fun φ : ℝ → ℝ => Integrable φ (volume : Measure ℝ))
        hfun.symm
        hscaled
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
        ‖A t‖ *
            ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)‖ ≤
          majorant t :=
    Filter.Eventually.of_forall
      (fun t : ℝ =>
        have hfactor : ‖A t‖ ≤ B * (1 + ‖t‖) :=
          hA_bound t
        have hphi :
            ‖zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)‖ ≤
              C * (1 + ‖t‖) ^ (-(4 : ℤ)) :=
          zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_decay_bound
            f F h 4 t
        have hphi_nonneg :
            0 ≤ ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)‖ :=
          norm_nonneg
            (zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t))
        have hfactor_rhs_nonneg : 0 ≤ B * (1 + ‖t‖) :=
          mul_nonneg hB_nonneg
            (le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg t)))
        have hprod :
            ‖A t‖ *
                ‖zetaCompletedExplicitFormulaPhi f
                  (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)‖ ≤
              (B * (1 + ‖t‖)) *
                (C * (1 + ‖t‖) ^ (-(4 : ℤ))) :=
          mul_le_mul hfactor hphi hphi_nonneg hfactor_rhs_nonneg
        have hbase_nonzero : (1 + ‖t‖ : ℝ) ≠ 0 :=
          ne_of_gt
            (lt_of_lt_of_le zero_lt_one
              (le_add_of_nonneg_right (norm_nonneg t)))
        have hweight :
            (1 + ‖t‖) * (1 + ‖t‖) ^ (-(4 : ℤ)) =
              (1 + ‖t‖) ^ (-(3 : ℤ)) := by
          calc
            (1 + ‖t‖) * (1 + ‖t‖) ^ (-(4 : ℤ)) =
                (1 + ‖t‖) ^ (1 : ℤ) * (1 + ‖t‖) ^ (-(4 : ℤ)) := by
              exact
                congrArg
                  (fun x : ℝ => x * (1 + ‖t‖) ^ (-(4 : ℤ)))
                  (zpow_one (1 + ‖t‖)).symm
            _ = (1 + ‖t‖) ^ ((1 : ℤ) + (-(4 : ℤ))) := by
              exact (zpow_add₀ hbase_nonzero (1 : ℤ) (-(4 : ℤ))).symm
            _ = (1 + ‖t‖) ^ (-(3 : ℤ)) := by
              rfl
        have hassoc :
            (B * (1 + ‖t‖)) *
                (C * (1 + ‖t‖) ^ (-(4 : ℤ))) =
              B * (C * (1 + ‖t‖) ^ (-(3 : ℤ))) := by
          let a : ℝ := 1 + ‖t‖
          let b : ℝ := (1 + ‖t‖) ^ (-(4 : ℤ))
          have hscalar :
              (B * a) * (C * b) = B * (C * (a * b)) := by
            calc
              (B * a) * (C * b) = B * (a * (C * b)) :=
                mul_assoc B a (C * b)
              _ = B * ((a * C) * b) := by
                exact congrArg (fun x : ℝ => B * x) (mul_assoc a C b).symm
              _ = B * ((C * a) * b) := by
                exact congrArg (fun x : ℝ => B * (x * b)) (mul_comm a C)
              _ = B * (C * (a * b)) := by
                exact congrArg (fun x : ℝ => B * x) (mul_assoc C a b)
              _ = B * (C * (a * b)) := by
                exact Eq.refl _
          have hrewrite : a * b = (1 + ‖t‖) ^ (-(3 : ℤ)) :=
            hweight
          exact
            Eq.trans hscalar
              (congrArg (fun x : ℝ => B * (C * x)) hrewrite)
        hprod.trans_eq hassoc)
  exact
    ExplicitFormulaAffineKernelMajorantPackage.of_mul_le
      majorant hintegrable hA_meas hphi_meas hbound

/-- A linearly bounded factor times the left centered test transform has an
integrable majorant. -/
def zetaCompletedExplicitFormulaLeftCenteredAffineProduct_majorantPackage_of_linear_factor_bound_common
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A : ℝ → ℂ) (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hA_meas : AEStronglyMeasurable A (volume : Measure ℝ))
    (hA_bound : ∀ t : ℝ, ‖A t‖ ≤ B * (1 + ‖t‖)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (fun t : ℝ =>
        A t *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) := by
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      ((1 : ℝ) - F.c - (1 / 2 : ℝ))
      ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 4
  let majorant : ℝ → ℝ := fun t : ℝ => B * (C * (1 + ‖t‖) ^ (-(3 : ℤ)))
  have hintegrable :
      Integrable majorant (volume : Measure ℝ) := by
    have hfinrank : Module.finrank ℝ ℝ = 1 :=
      Module.finrank_self ℝ
    have hfinrank_cast : ((Module.finrank ℝ ℝ : ℕ) : ℝ) = 1 :=
      Eq.trans
        (congrArg (fun n : ℕ => (n : ℝ)) hfinrank)
        Nat.cast_one
    have htwo_add_one_eq_three : (2 : ℝ) + 1 = 3 :=
      two_add_one_eq_three
    have htwo_lt_three : (2 : ℝ) < 3 :=
      Eq.subst
        (motive := fun x : ℝ => (2 : ℝ) < x)
        htwo_add_one_eq_three
        (lt_add_of_pos_right (2 : ℝ) zero_lt_one)
    have hdim : (Module.finrank ℝ ℝ : ℝ) < 3 :=
      Eq.subst
        (motive := fun x : ℝ => x < 3)
        hfinrank_cast.symm
        (lt_trans one_lt_two htwo_lt_three)
    have hbase :
        Integrable
          (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℝ)))
          (volume : Measure ℝ) :=
      integrable_one_add_norm (E := ℝ) hdim
    have hscaled :
        Integrable
          (fun t : ℝ => B * (C * (1 + ‖t‖) ^ (-(3 : ℝ))))
          (volume : Measure ℝ) :=
      (hbase.const_mul C).const_mul B
    have hfun :
        majorant =
          (fun t : ℝ => B * (C * (1 + ‖t‖) ^ (-(3 : ℝ)))) := by
      funext t
      have hexp :
          ((-(3 : ℤ) : ℤ) : ℝ) = -(3 : ℝ) :=
        Int.cast_neg 3
      have hpow :
          (1 + ‖t‖) ^ (-(3 : ℤ)) =
            (1 + ‖t‖) ^ (-(3 : ℝ)) :=
        Eq.trans
          (Real.rpow_intCast (1 + ‖t‖) (-(3 : ℤ))).symm
          (congrArg (fun r : ℝ => (1 + ‖t‖) ^ r) hexp)
      exact congrArg (fun x : ℝ => B * (C * x)) hpow
    exact
      Eq.subst
        (motive := fun φ : ℝ → ℝ => Integrable φ (volume : Measure ℝ))
        hfun.symm
        hscaled
  have hphi_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_aestronglyMeasurable
      f F h
  have hbound :
      ∀ᵐ t ∂(volume : Measure ℝ),
        ‖A t‖ *
            ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ ≤
          majorant t :=
    Filter.Eventually.of_forall
      (fun t : ℝ =>
        have hfactor : ‖A t‖ ≤ B * (1 + ‖t‖) :=
          hA_bound t
        have hphi :
            ‖zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ ≤
              C * (1 + ‖t‖) ^ (-(4 : ℤ)) :=
          zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_decay_bound
            f F h 4 t
        have hphi_nonneg :
            0 ≤ ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ :=
          norm_nonneg
            (zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t))
        have hfactor_rhs_nonneg : 0 ≤ B * (1 + ‖t‖) :=
          mul_nonneg hB_nonneg
            (le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg t)))
        have hprod :
            ‖A t‖ *
                ‖zetaCompletedExplicitFormulaPhi f
                  (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ ≤
              (B * (1 + ‖t‖)) *
                (C * (1 + ‖t‖) ^ (-(4 : ℤ))) :=
          mul_le_mul hfactor hphi hphi_nonneg hfactor_rhs_nonneg
        have hbase_nonzero : (1 + ‖t‖ : ℝ) ≠ 0 :=
          ne_of_gt
            (lt_of_lt_of_le zero_lt_one
              (le_add_of_nonneg_right (norm_nonneg t)))
        have hweight :
            (1 + ‖t‖) * (1 + ‖t‖) ^ (-(4 : ℤ)) =
              (1 + ‖t‖) ^ (-(3 : ℤ)) := by
          calc
            (1 + ‖t‖) * (1 + ‖t‖) ^ (-(4 : ℤ)) =
                (1 + ‖t‖) ^ (1 : ℤ) * (1 + ‖t‖) ^ (-(4 : ℤ)) := by
              exact
                congrArg
                  (fun x : ℝ => x * (1 + ‖t‖) ^ (-(4 : ℤ)))
                  (zpow_one (1 + ‖t‖)).symm
            _ = (1 + ‖t‖) ^ ((1 : ℤ) + (-(4 : ℤ))) := by
              exact (zpow_add₀ hbase_nonzero (1 : ℤ) (-(4 : ℤ))).symm
            _ = (1 + ‖t‖) ^ (-(3 : ℤ)) := by
              rfl
        have hassoc :
            (B * (1 + ‖t‖)) *
                (C * (1 + ‖t‖) ^ (-(4 : ℤ))) =
              B * (C * (1 + ‖t‖) ^ (-(3 : ℤ))) := by
          let a : ℝ := 1 + ‖t‖
          let b : ℝ := (1 + ‖t‖) ^ (-(4 : ℤ))
          have hscalar :
              (B * a) * (C * b) = B * (C * (a * b)) := by
            calc
              (B * a) * (C * b) = B * (a * (C * b)) :=
                mul_assoc B a (C * b)
              _ = B * ((a * C) * b) := by
                exact congrArg (fun x : ℝ => B * x) (mul_assoc a C b).symm
              _ = B * ((C * a) * b) := by
                exact congrArg (fun x : ℝ => B * (x * b)) (mul_comm a C)
              _ = B * (C * (a * b)) := by
                exact congrArg (fun x : ℝ => B * x) (mul_assoc C a b)
              _ = B * (C * (a * b)) := by
                exact Eq.refl _
          have hrewrite : a * b = (1 + ‖t‖) ^ (-(3 : ℤ)) :=
            hweight
          exact
            Eq.trans hscalar
              (congrArg (fun x : ℝ => B * (C * x)) hrewrite)
        hprod.trans_eq hassoc)
  exact
    ExplicitFormulaAffineKernelMajorantPackage.of_mul_le
      majorant hintegrable hA_meas hphi_meas hbound

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
