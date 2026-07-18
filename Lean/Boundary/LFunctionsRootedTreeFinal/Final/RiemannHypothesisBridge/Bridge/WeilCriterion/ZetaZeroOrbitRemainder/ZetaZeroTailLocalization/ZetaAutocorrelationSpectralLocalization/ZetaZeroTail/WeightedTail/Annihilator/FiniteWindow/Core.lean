import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.FiniteComplement.Owner

/-!
# Finite-window completed-zero annihilator core

This file owns the exact split of a bounded completed-zero distribution into a
finite coordinate sum and its absolutely convergent complement.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction
namespace FiniteWindow

noncomputable def zetaCompletedZeroSideAnnihilatorFiniteWindow
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑ eta in S.attach,
    b ⟨eta, hS eta eta.2⟩ * zetaZeroSideContribution eta f

noncomputable def zetaCompletedZeroSideAnnihilatorComplementaryTail
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (S : Finset ℂ)
    (f : ZetaAdmissibleFunction) : ℂ :=
  tsum (fun rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} =>
    b ⟨rho, rho.2.1⟩ * zetaZeroSideContribution (rho : ℂ) f)

theorem finiteWindow_sum_attach_eq_sum
    (S : Finset ℂ)
    (g : ℂ → ℂ) :
    (∑ eta in S.attach, g (eta : ℂ)) = ∑ eta in S, g eta := by
  exact Finset.sum_attach S g

theorem finiteWindow_sideContribution_sum_attach_eq_sum
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
    (f : ZetaAdmissibleFunction) :
    (∑ eta in S.attach,
      b ⟨eta, hS eta eta.2⟩ * zetaZeroSideContribution eta f) =
      ∑ eta in S,
        (if heta : eta ∈ S then
          b ⟨eta, hS eta heta⟩ * zetaZeroSideContribution eta f
        else
          0) := by
  let g : ℂ → ℂ := fun eta =>
    if heta : eta ∈ S then
      b ⟨eta, hS eta heta⟩ * zetaZeroSideContribution eta f
    else
      0
  have hattach :
      (∑ eta in S.attach, g (eta : ℂ)) = ∑ eta in S, g eta := by
    exact finiteWindow_sum_attach_eq_sum S g
  calc
    (∑ eta in S.attach,
        b ⟨eta, hS eta eta.2⟩ * zetaZeroSideContribution eta f) =
        ∑ eta in S.attach, g (eta : ℂ) := by
      apply Finset.sum_congr rfl
      intro eta heta
      exact dif_pos eta.2
    _ = ∑ eta in S, g eta := hattach
    _ = ∑ eta in S,
        (if heta : eta ∈ S then
          b ⟨eta, hS eta heta⟩ * zetaZeroSideContribution eta f
        else
          0) := by
      apply Finset.sum_congr rfl
      intro eta heta
      exact dif_pos heta

theorem zetaCompletedZeroSideAnnihilatorFiniteWindow_smul
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
    (c : ℂ)
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS (c • f) =
      c * zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f := by
  unfold zetaCompletedZeroSideAnnihilatorFiniteWindow
  calc
    (∑ eta in S.attach,
        b ⟨eta, hS eta eta.2⟩ * zetaZeroSideContribution eta (c • f)) =
        ∑ eta in S.attach,
          b ⟨eta, hS eta eta.2⟩ *
            (c * zetaZeroSideContribution eta f) := by
      exact Finset.sum_congr rfl
        (fun eta heta =>
          congrArg
            (fun value : ℂ => b ⟨eta, hS eta eta.2⟩ * value)
            (zetaZeroSideContribution_smul eta c f))
    (∑ eta in S.attach,
        b ⟨eta, hS eta eta.2⟩ *
          (c * zetaZeroSideContribution eta f)) =
        ∑ eta in S.attach,
          c * (b ⟨eta, hS eta eta.2⟩ * zetaZeroSideContribution eta f) := by
      exact Finset.sum_congr rfl
        (fun eta heta =>
          calc
            b ⟨eta, hS eta eta.2⟩ *
                (c * zetaZeroSideContribution eta f) =
                (b ⟨eta, hS eta eta.2⟩ * c) *
                  zetaZeroSideContribution eta f :=
              (mul_assoc
                (b ⟨eta, hS eta eta.2⟩)
                c
                (zetaZeroSideContribution eta f)).symm
            (b ⟨eta, hS eta eta.2⟩ * c) *
                zetaZeroSideContribution eta f =
                (c * b ⟨eta, hS eta eta.2⟩) *
                  zetaZeroSideContribution eta f :=
              congrArg
                (fun value : ℂ => value * zetaZeroSideContribution eta f)
                (mul_comm
                  (b ⟨eta, hS eta eta.2⟩)
                  c)
            (c * b ⟨eta, hS eta eta.2⟩) *
                zetaZeroSideContribution eta f =
                c *
                (b ⟨eta, hS eta eta.2⟩ * zetaZeroSideContribution eta f) :=
              mul_assoc c
                (b ⟨eta, hS eta eta.2⟩)
                (zetaZeroSideContribution eta f))
    (∑ eta in S.attach,
          c * (b ⟨eta, hS eta eta.2⟩ * zetaZeroSideContribution eta f)) =
        c *
          (∑ eta in S.attach,
            b ⟨eta, hS eta eta.2⟩ * zetaZeroSideContribution eta f) := by
      exact (Finset.mul_sum S.attach
        (fun eta : {eta : ℂ // eta ∈ S} =>
          b ⟨eta, hS eta eta.2⟩ * zetaZeroSideContribution eta f)
        c).symm

theorem zetaCompletedZeroSideAnnihilatorFiniteWindow_eq_zero_of_forall_zero
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
    (f : ZetaAdmissibleFunction)
    (hzero : ∀ eta : S,
      b ⟨(eta : ℂ), hS eta eta.property⟩ *
          zetaZeroSideContribution (eta : ℂ) f = 0) :
    zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f = 0 := by
  unfold zetaCompletedZeroSideAnnihilatorFiniteWindow
  apply Finset.sum_eq_zero
  intro eta heta
  exact hzero ⟨(eta : ℂ), eta.property⟩

theorem zetaCompletedZeroSideAnnihilatorFiniteWindow_add
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
    (f : ZetaAdmissibleFunction)
    (g : ZetaAdmissibleFunction) :
    zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS (f + g) =
      zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f +
        zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS g := by
  unfold zetaCompletedZeroSideAnnihilatorFiniteWindow
  calc
    (∑ eta in S.attach,
        b ⟨eta, hS eta eta.2⟩ * zetaZeroSideContribution eta (f + g)) =
        ∑ eta in S.attach,
          b ⟨eta, hS eta eta.2⟩ *
            (zetaZeroSideContribution eta f + zetaZeroSideContribution eta g) := by
      exact Finset.sum_congr rfl
        (fun eta heta =>
          congrArg
            (fun value : ℂ => b ⟨eta, hS eta eta.2⟩ * value)
            (zetaZeroSideContribution_add eta f g))
    _ = ∑ eta in S.attach,
          (b ⟨eta, hS eta eta.2⟩ * zetaZeroSideContribution eta f +
            b ⟨eta, hS eta eta.2⟩ * zetaZeroSideContribution eta g) := by
      exact Finset.sum_congr rfl
        (fun eta heta =>
          (mul_add
            (b ⟨eta, hS eta eta.2⟩)
            (zetaZeroSideContribution eta f)
            (zetaZeroSideContribution eta g)).symm)
    _ =
        (∑ eta in S.attach,
          b ⟨eta, hS eta eta.2⟩ * zetaZeroSideContribution eta f) +
          (∑ eta in S.attach,
            b ⟨eta, hS eta eta.2⟩ * zetaZeroSideContribution eta g) := by
      exact Finset.sum_add_distrib

theorem zetaCompletedZeroSideAnnihilatorComplementaryTail_smul
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (c : ℂ)
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroSideAnnihilatorComplementaryTail b S (c • f) =
      c * zetaCompletedZeroSideAnnihilatorComplementaryTail b S f := by
  have hsum :
      Summable
        (fun rho : ZetaCompletedZeroCoordinate =>
          b rho * zetaZeroSideContribution (rho : ℂ) f) :=
    summable_zetaCompletedZeroSideAnnihilator
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f
  have htail :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} =>
          b ⟨rho, rho.2.1⟩ * zetaZeroSideContribution (rho : ℂ) f) := by
    exact hsum.subtype {rho : ZetaCompletedZeroCoordinate | (rho : ℂ) ∉ S}
  unfold zetaCompletedZeroSideAnnihilatorComplementaryTail
  calc
    tsum
        (fun rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} =>
          b ⟨rho, rho.2.1⟩ * zetaZeroSideContribution (rho : ℂ) (c • f)) =
        tsum
          (fun rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} =>
            c *
              (b ⟨rho, rho.2.1⟩ *
                zetaZeroSideContribution (rho : ℂ) f)) := by
      exact tsum_congr
        (fun rho =>
          calc
            b ⟨rho, rho.2.1⟩ * zetaZeroSideContribution (rho : ℂ) (c • f) =
                b ⟨rho, rho.2.1⟩ *
                  (c * zetaZeroSideContribution (rho : ℂ) f) :=
              congrArg
                (fun value : ℂ => b ⟨rho, rho.2.1⟩ * value)
                (zetaZeroSideContribution_smul (rho : ℂ) c f)
            b ⟨rho, rho.2.1⟩ *
                (c * zetaZeroSideContribution (rho : ℂ) f) =
                (b ⟨rho, rho.2.1⟩ * c) *
                  zetaZeroSideContribution (rho : ℂ) f :=
              (mul_assoc
                (b ⟨rho, rho.2.1⟩)
                c
                (zetaZeroSideContribution (rho : ℂ) f)).symm
            (b ⟨rho, rho.2.1⟩ * c) *
                zetaZeroSideContribution (rho : ℂ) f =
                (c * b ⟨rho, rho.2.1⟩) *
                  zetaZeroSideContribution (rho : ℂ) f :=
              congrArg
                (fun value : ℂ => value * zetaZeroSideContribution (rho : ℂ) f)
                (mul_comm (b ⟨rho, rho.2.1⟩) c)
            (c * b ⟨rho, rho.2.1⟩) *
                zetaZeroSideContribution (rho : ℂ) f =
                c *
                  (b ⟨rho, rho.2.1⟩ *
                    zetaZeroSideContribution (rho : ℂ) f) :=
              mul_assoc c (b ⟨rho, rho.2.1⟩)
                (zetaZeroSideContribution (rho : ℂ) f))
    tsum
          (fun rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} =>
            c *
              (b ⟨rho, rho.2.1⟩ *
                zetaZeroSideContribution (rho : ℂ) f)) =
        c * tsum
          (fun rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} =>
            b ⟨rho, rho.2.1⟩ * zetaZeroSideContribution (rho : ℂ) f) :=
      (htail.tsum_mul_left c).symm

theorem zetaCompletedZeroSideAnnihilatorComplementaryTail_add
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (f : ZetaAdmissibleFunction)
    (g : ZetaAdmissibleFunction) :
    zetaCompletedZeroSideAnnihilatorComplementaryTail b S (f + g) =
      zetaCompletedZeroSideAnnihilatorComplementaryTail b S f +
        zetaCompletedZeroSideAnnihilatorComplementaryTail b S g := by
  have hsumf :=
    summable_zetaCompletedZeroSideAnnihilator
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f
  have hsumg :=
    summable_zetaCompletedZeroSideAnnihilator
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary g
  have htailf :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} =>
          b ⟨rho, rho.2.1⟩ * zetaZeroSideContribution (rho : ℂ) f) := by
    exact hsumf.subtype {rho : ZetaCompletedZeroCoordinate | (rho : ℂ) ∉ S}
  have htailg :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} =>
          b ⟨rho, rho.2.1⟩ * zetaZeroSideContribution (rho : ℂ) g) := by
    exact hsumg.subtype {rho : ZetaCompletedZeroCoordinate | (rho : ℂ) ∉ S}
  unfold zetaCompletedZeroSideAnnihilatorComplementaryTail
  calc
    tsum
        (fun rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} =>
          b ⟨rho, rho.2.1⟩ * zetaZeroSideContribution (rho : ℂ) (f + g)) =
        tsum
          (fun rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} =>
            (b ⟨rho, rho.2.1⟩ * zetaZeroSideContribution (rho : ℂ) f) +
              (b ⟨rho, rho.2.1⟩ * zetaZeroSideContribution (rho : ℂ) g)) := by
      exact tsum_congr
        (fun rho =>
          calc
            b ⟨rho, rho.2.1⟩ * zetaZeroSideContribution (rho : ℂ) (f + g) =
                b ⟨rho, rho.2.1⟩ *
                  (zetaZeroSideContribution (rho : ℂ) f +
                    zetaZeroSideContribution (rho : ℂ) g) :=
              congrArg
                (fun value : ℂ => b ⟨rho, rho.2.1⟩ * value)
                (zetaZeroSideContribution_add (rho : ℂ) f g)
            _ =
                (b ⟨rho, rho.2.1⟩ * zetaZeroSideContribution (rho : ℂ) f) +
                  (b ⟨rho, rho.2.1⟩ * zetaZeroSideContribution (rho : ℂ) g) :=
              mul_add
                (b ⟨rho, rho.2.1⟩)
                (zetaZeroSideContribution (rho : ℂ) f)
                (zetaZeroSideContribution (rho : ℂ) g))
    _ =
        tsum
          (fun rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} =>
            b ⟨rho, rho.2.1⟩ * zetaZeroSideContribution (rho : ℂ) f) +
          tsum
            (fun rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} =>
              b ⟨rho, rho.2.1⟩ * zetaZeroSideContribution (rho : ℂ) g) :=
      tsum_add htailf htailg

theorem zetaCompletedZeroSideAnnihilator_eq_finiteWindow_add_complementaryTail
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroSideAnnihilator
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f =
      zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f +
        zetaCompletedZeroSideAnnihilatorComplementaryTail b S f := by
  have hsum :
      Summable (fun rho : ZetaCompletedZeroCoordinate =>
        b rho * zetaZeroSideContribution (rho : ℂ) f) :=
    summable_zetaCompletedZeroSideAnnihilator
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f
  have hsplit :=
    completedZeroSubtype_tsum_eq_finite_add_complement
      S
      (fun rho : ZetaCompletedZeroCoordinate =>
        b rho * zetaZeroSideContribution (rho : ℂ) f)
      hS
      hsum
  unfold zetaCompletedZeroSideAnnihilator
  unfold zetaCompletedZeroSideL1DualPairing
  unfold zetaCompletedZeroSideAnnihilatorFiniteWindow
  unfold zetaCompletedZeroSideAnnihilatorComplementaryTail
  exact hsplit

theorem zetaCompletedZeroSideAnnihilatorFiniteWindow_eq_neg_complementaryTail_of_annihilates
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
    (hannihilates :
      zetaCompletedZeroSideAnnihilator
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f = 0) :
    zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f =
      - zetaCompletedZeroSideAnnihilatorComplementaryTail b S f := by
  have hsplit :=
    zetaCompletedZeroSideAnnihilator_eq_finiteWindow_add_complementaryTail
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary S hS f
  have hsumZero :
      zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f +
        zetaCompletedZeroSideAnnihilatorComplementaryTail b S f = 0 := by
    exact Eq.trans hsplit.symm hannihilates
  exact eq_neg_of_add_eq_zero_left hsumZero

theorem zetaCompletedZeroSideAnnihilatorComplementaryTail_eq_annihilator_sub_finiteWindow
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroSideAnnihilatorComplementaryTail b S f =
      zetaCompletedZeroSideAnnihilator
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f -
        zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f := by
  apply (eq_sub_iff_add_eq).2
  have hsplit :=
    zetaCompletedZeroSideAnnihilator_eq_finiteWindow_add_complementaryTail
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary S hS f
  calc
    zetaCompletedZeroSideAnnihilatorComplementaryTail b S f +
        zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f =
        zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f +
          zetaCompletedZeroSideAnnihilatorComplementaryTail b S f :=
      add_comm
        (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f)
        (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f)
    zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f +
          zetaCompletedZeroSideAnnihilatorComplementaryTail b S f =
        zetaCompletedZeroSideAnnihilator
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f :=
      hsplit.symm

end FiniteWindow
end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
