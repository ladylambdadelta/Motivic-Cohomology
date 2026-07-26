import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.FiniteWindow.KernelDensityDetection

/-!
# Quantitative finite-window carrier separation

This file owns the constant-bearing form of completed-zero finite-window
detection.  A nonzero bounded completed-zero coefficient determines a finite
completed-zero carrier and an admissible probe whose selected finite-window
mass gives a positive constant strictly dominating the complementary tail.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction
namespace FiniteWindow

open scoped ENNReal

theorem positive_norm_of_lt_norm
    (tailNorm : ℝ)
    (windowNorm : ℝ)
    (htailNonnegative : 0 ≤ tailNorm)
    (hdominates : tailNorm < windowNorm) :
    0 < windowNorm :=
  lt_of_le_of_lt htailNonnegative hdominates

theorem exists_positive_gap_of_lt
    (tailNorm : ℝ)
    (windowNorm : ℝ)
    (hdominates : tailNorm < windowNorm) :
    ∃ gap : ℝ, 0 < gap ∧ tailNorm + gap ≤ windowNorm :=
  match exists_between hdominates with
  | ⟨middle, htailMiddle, hmiddleWindow⟩ =>
      let gap : ℝ := middle - tailNorm
      have hgapPositive : 0 < gap :=
        sub_pos.mpr htailMiddle
      have htailAddGap : tailNorm + gap = middle :=
        Eq.trans
          (add_comm tailNorm gap)
          (sub_add_cancel middle tailNorm)
      have htailAddGapLe : tailNorm + gap ≤ windowNorm :=
        Eq.subst
          (motive := fun value : ℝ => value ≤ windowNorm)
          htailAddGap.symm
          (le_of_lt hmiddleWindow)
      ⟨gap, hgapPositive, htailAddGapLe⟩

theorem norm_sub_norm_gap_le_norm_add
    (finiteWindow : ℂ)
    (tail : ℂ)
    (carrierGap : ℝ)
    (htailGapLe : norm tail + carrierGap ≤ norm finiteWindow) :
    carrierGap ≤ norm (finiteWindow + tail) :=
  let hfiniteTail :
      norm finiteWindow ≤ norm (finiteWindow + tail) + norm tail :=
    let hfiniteEq :
        norm finiteWindow =
          norm ((finiteWindow + tail) + -tail) :=
      congrArg norm (add_neg_cancel_right finiteWindow tail).symm
    let hfiniteTriangle :
        norm ((finiteWindow + tail) + -tail) ≤
          norm (finiteWindow + tail) + norm (-tail) :=
      norm_add_le (finiteWindow + tail) (-tail)
    let hfiniteLeNegTail :
        norm finiteWindow ≤ norm (finiteWindow + tail) + norm (-tail) :=
      Eq.subst
        (motive := fun value : ℝ =>
          value ≤ norm (finiteWindow + tail) + norm (-tail))
        hfiniteEq.symm
        hfiniteTriangle
    let hnegNorm :
        norm (finiteWindow + tail) + norm (-tail) =
          norm (finiteWindow + tail) + norm tail :=
      congrArg
        (fun value : ℝ => norm (finiteWindow + tail) + value)
        (norm_neg tail)
    Eq.subst
      (motive := fun value : ℝ => norm finiteWindow ≤ value)
      hnegNorm
      hfiniteLeNegTail
  have hgapTailLe :
      carrierGap + norm tail ≤ norm finiteWindow :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ norm finiteWindow)
      (add_comm (norm tail) carrierGap)
      htailGapLe
  have hgapTailLeNormAddTail :
      carrierGap + norm tail ≤ norm (finiteWindow + tail) + norm tail :=
    le_trans hgapTailLe hfiniteTail
  (add_le_add_iff_right (norm tail)).mp hgapTailLeNormAddTail

theorem annihilator_norm_gap_bound_of_finiteWindow_gap_bound
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
    (f : ZetaAdmissibleFunction)
    (carrierGap : ℝ)
    (htailGapLe :
      norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) +
          carrierGap ≤
        norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f)) :
    carrierGap ≤
      norm
        (zetaCompletedZeroSideAnnihilator
          b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f) :=
  let finiteWindow : ℂ := zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f
  let tail : ℂ := zetaCompletedZeroSideAnnihilatorComplementaryTail b S f
  let hannihilatorSplit :
      zetaCompletedZeroSideAnnihilator
          b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f =
        finiteWindow + tail :=
    zetaCompletedZeroSideAnnihilator_eq_finiteWindow_add_complementaryTail
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S hS f
  let hgapNormAdd : carrierGap ≤ norm (finiteWindow + tail) :=
    norm_sub_norm_gap_le_norm_add finiteWindow tail carrierGap htailGapLe
  Eq.subst
    (motive := fun value : ℂ => carrierGap ≤ norm value)
    hannihilatorSplit.symm
    hgapNormAdd

theorem tail_norm_lt_of_positive_gap_bound
    (tailNorm : ℝ)
    (carrierBound : ℝ)
    (carrierGap : ℝ)
    (hcarrierGapPositive : 0 < carrierGap)
    (htailGapLe : tailNorm + carrierGap ≤ carrierBound) :
    tailNorm < carrierBound :=
  lt_of_lt_of_le
    (lt_add_of_pos_right tailNorm hcarrierGapPositive)
    htailGapLe

theorem tail_gap_le_finiteWindow_norm_of_carrier_identity
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
    (f : ZetaAdmissibleFunction)
    (carrierBound : ℝ)
    (carrierGap : ℝ)
    (hcarrierIdentity :
      carrierBound =
        norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f))
    (htailGapLe :
      norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) +
          carrierGap ≤
        carrierBound) :
    norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) +
        carrierGap ≤
      norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) :=
  Eq.subst
    (motive := fun value : ℝ =>
      norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) +
          carrierGap ≤ value)
    hcarrierIdentity
    htailGapLe

theorem exists_zetaCompletedZeroSideAnnihilator_quantitativeCarrierSeparation_with_gap
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate)
    (hrho : b rho ≠ 0) :
    ∃ (S : Finset ℂ)
      (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
      (f : ZetaAdmissibleFunction)
      (carrierBound : ℝ)
      (carrierGap : ℝ),
      (rho : ℂ) ∈ S ∧
        0 < carrierBound ∧
          0 < carrierGap ∧
            carrierBound =
                norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) ∧
              norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) +
                  carrierGap ≤
                carrierBound :=
  match
    exists_zetaCompletedZeroSideAnnihilator_finiteWindow_dominates_complementaryTail_from_kernelDensity
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      b rho hrho with
  | ⟨S, hS, f, hrhoS, hdominates⟩ =>
      let tailNorm : ℝ :=
        norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f)
      let carrierBound : ℝ :=
        norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f)
      have htailNonnegative : 0 ≤ tailNorm :=
        norm_nonneg (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f)
      have hcarrierPositive : 0 < carrierBound :=
        positive_norm_of_lt_norm tailNorm carrierBound htailNonnegative hdominates
      match exists_positive_gap_of_lt tailNorm carrierBound hdominates with
      | ⟨carrierGap, hcarrierGapPositive, htailGapLe⟩ =>
          have hcarrierIdentity :
              carrierBound =
                norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) :=
            Eq.refl carrierBound
          ⟨S, hS, f, carrierBound, carrierGap, hrhoS, hcarrierPositive,
            hcarrierGapPositive, hcarrierIdentity, htailGapLe⟩

theorem exists_zetaCompletedZeroSideAnnihilator_quantitativeCarrierSeparation
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate)
    (hrho : b rho ≠ 0) :
    ∃ (S : Finset ℂ)
      (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
      (f : ZetaAdmissibleFunction)
      (carrierBound : ℝ),
      (rho : ℂ) ∈ S ∧
        0 < carrierBound ∧
          carrierBound =
              norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) ∧
            norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) <
              carrierBound :=
  match
    exists_zetaCompletedZeroSideAnnihilator_quantitativeCarrierSeparation_with_gap
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      b rho hrho with
  | ⟨S, hS, f, carrierBound, carrierGap, hpayload⟩ =>
      let hrhoS : (rho : ℂ) ∈ S := hpayload.1
      let hcarrierPositive : 0 < carrierBound := hpayload.2.1
      let hcarrierGapPositive : 0 < carrierGap := hpayload.2.2.1
      let hcarrierIdentity :
          carrierBound =
            norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) :=
        hpayload.2.2.2.1
      let htailGapLe :
          norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) +
              carrierGap ≤
            carrierBound :=
        hpayload.2.2.2.2
      let htailBound :
          norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) <
            carrierBound :=
        tail_norm_lt_of_positive_gap_bound
          (norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f))
          carrierBound
          carrierGap
          hcarrierGapPositive
          htailGapLe
      ⟨S, hS, f, carrierBound, hrhoS, hcarrierPositive,
        hcarrierIdentity, htailBound⟩

theorem exists_zetaCompletedZeroSideAnnihilator_quantitativeCarrierSeparation_constant_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate)
    (hrho : b rho ≠ 0) :
    ∃ (S : Finset ℂ)
      (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
      (f : ZetaAdmissibleFunction)
      (carrierBound : ℝ)
      (carrierGap : ℝ),
      (rho : ℂ) ∈ S ∧
        0 < carrierBound ∧
          0 < carrierGap ∧
            carrierBound =
                norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) ∧
              norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) +
                  carrierGap ≤
                carrierBound ∧
                carrierGap ≤
                  norm
                    (zetaCompletedZeroSideAnnihilator
                      b hbranch hpartialOneTwo hcompactOneTwo hfinite
                        hpartialLeft hcompactBoundary f) :=
  match
    exists_zetaCompletedZeroSideAnnihilator_quantitativeCarrierSeparation_with_gap
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      b rho hrho with
  | ⟨S, hS, f, carrierBound, carrierGap, hpayload⟩ =>
      let htailGapLe :
          norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) +
              carrierGap ≤
            carrierBound :=
        hpayload.2.2.2.2
      let hcarrierIdentity :
          carrierBound =
            norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) :=
        hpayload.2.2.2.1
      let htailGapNormLe :
          norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) +
              carrierGap ≤
            norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) :=
        tail_gap_le_finiteWindow_norm_of_carrier_identity
          b S hS f carrierBound carrierGap hcarrierIdentity htailGapLe
      let hannihilatorBound :
          carrierGap ≤
            norm
              (zetaCompletedZeroSideAnnihilator
                b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
                  hcompactBoundary f) :=
        annihilator_norm_gap_bound_of_finiteWindow_gap_bound
          b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
          S hS f carrierGap htailGapNormLe
      ⟨S, hS, f, carrierBound, carrierGap, hpayload.1, hpayload.2.1,
        hpayload.2.2.1, hcarrierIdentity, htailGapLe, hannihilatorBound⟩

theorem exists_zetaCompletedZeroSideAnnihilator_positive_norm_lower_bound_with_carrier
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate)
    (hrho : b rho ≠ 0) :
    ∃ (S : Finset ℂ)
      (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
      (f : ZetaAdmissibleFunction)
      (constant : ℝ),
      (rho : ℂ) ∈ S ∧
        0 < constant ∧
          constant ≤
            norm
              (zetaCompletedZeroSideAnnihilator
                b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
                  hcompactBoundary f) :=
  match
    exists_zetaCompletedZeroSideAnnihilator_quantitativeCarrierSeparation_constant_bound
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      b rho hrho with
  | ⟨S, hS, f, carrierBound, carrierGap, hpayload⟩ =>
      let hrhoS : (rho : ℂ) ∈ S :=
        hpayload.1
      let hconstantPositive : 0 < carrierGap :=
        hpayload.2.2.1
      let hconstantBound :
          carrierGap ≤
            norm
              (zetaCompletedZeroSideAnnihilator
                b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
                  hcompactBoundary f) :=
        hpayload.2.2.2.2.2
      ⟨S, hS, f, carrierGap, hrhoS, hconstantPositive,
        hconstantBound⟩

theorem exists_zetaCompletedZeroSideAnnihilator_positive_norm_lower_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate)
    (hrho : b rho ≠ 0) :
    ∃ (f : ZetaAdmissibleFunction)
      (constant : ℝ),
      0 < constant ∧
        constant ≤
          norm
            (zetaCompletedZeroSideAnnihilator
              b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
                hcompactBoundary f) :=
  match
    exists_zetaCompletedZeroSideAnnihilator_positive_norm_lower_bound_with_carrier
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      b rho hrho with
  | ⟨S, hS, f, constant, hpayload⟩ =>
      let hconstantPositive : 0 < constant :=
        hpayload.2.1
      let hconstantBound :
          constant ≤
            norm
              (zetaCompletedZeroSideAnnihilator
                b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
                  hcompactBoundary f) :=
        hpayload.2.2
      ⟨f, constant, hconstantPositive, hconstantBound⟩

end FiniteWindow
end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
