import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.ScheduledConcreteLogDerivControl
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.ScheduledPointwiseRegularity
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.AutocorrelationAnalyticPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalAnalyticInputs

/-!
# Canonical scheduled analytic package

This owner constructs the canonical scheduled horizontal carrier for the
autocorrelation contour.  The remaining analytic sink is a factor bound on this
single concrete carrier, not arbitrary completed-zero excised strips.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- A supplied horizontal avoiding schedule gives the autocorrelation cofinal
boundary-avoiding schedule. -/
def zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule_of_horizontalAvoidingSchedule
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)) :
    ExplicitFormulaCofinalHeightSchedule
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  explicitFormulaCofinalHeightSchedule_of_horizontalAvoidingSchedule
    (CleanAutocorrelationVerticalRegularity.zetaCompletedExplicitFormula_autocorrelation_verticallyRegularContourFamily f)
    schedule

/-- The cofinal boundary-avoiding schedule from the canonical
autocorrelation horizontal avoiding schedule. -/
def zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule
    (f : ZetaAdmissibleFunction) :
    ExplicitFormulaCofinalHeightSchedule
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  explicitFormulaCofinalHeightSchedule_canonical
    (CleanAutocorrelationVerticalRegularity.zetaCompletedExplicitFormulaAutocorrelation_verticallyRegularContourFamily f)

/-- The set of all top and bottom horizontal points on a supplied autocorrelation
cofinal schedule. -/
def zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrierSet_of_cofinalSchedule
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)) :
    Set ℂ :=
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  {z : ℂ |
    (∃ u x : ℝ,
      x ∈ Set.uIcc family.c (1 - family.c) ∧
      z = zetaCompletedExplicitFormulaTopPath
        (family.rectangle (schedule.height u)) x) ∨
    (∃ u x : ℝ,
      x ∈ Set.uIcc family.c (1 - family.c) ∧
      z = zetaCompletedExplicitFormulaBottomPath
        (family.rectangle (schedule.height u)) x)}

/-- The set of all top and bottom horizontal points on the canonical schedule. -/
def zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrierSet
    (f : ZetaAdmissibleFunction) : Set ℂ :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrierSet_of_cofinalSchedule
    f
    (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f)

/-- The top horizontal point belongs to the carrier set for a supplied cofinal
schedule. -/
theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem_set_of_cofinalSchedule
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (u x : ℝ)
    (hx :
      x ∈
        Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    zetaCompletedExplicitFormulaTopPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          (schedule.height u))
        x ∈
      zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrierSet_of_cofinalSchedule
        f schedule :=
  Or.inl
    (Exists.intro u
      (Exists.intro x
        (And.intro hx rfl)))

/-- The bottom horizontal point belongs to the carrier set for a supplied cofinal
schedule. -/
theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bottom_mem_set_of_cofinalSchedule
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (u x : ℝ)
    (hx :
      x ∈
        Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    zetaCompletedExplicitFormulaBottomPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          (schedule.height u))
        x ∈
      zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrierSet_of_cofinalSchedule
        f schedule :=
  Or.inr
    (Exists.intro u
      (Exists.intro x
        (And.intro hx rfl)))

/-- The top scheduled horizontal point belongs to the canonical scheduled carrier set. -/
theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem_set
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hx :
      x ∈
        Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    zetaCompletedExplicitFormulaTopPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
        x ∈
      zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrierSet f :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem_set_of_cofinalSchedule
    f
    (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f)
    u
    x
    hx

/-- The bottom scheduled horizontal point belongs to the canonical scheduled carrier set. -/
theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bottom_mem_set
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hx :
      x ∈
        Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    zetaCompletedExplicitFormulaBottomPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
        x ∈
      zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrierSet f :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bottom_mem_set_of_cofinalSchedule
    f
    (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f)
    u
    x
    hx

/-- The scheduled horizontal carrier for a supplied autocorrelation cofinal
schedule. -/
def zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)) :
    CompletedZetaZeroExcisedStrip
      (min (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
      (max (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :=
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  { carrier :=
      zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrierSet_of_cofinalSchedule
        f schedule
    in_strip :=
      fun z hz =>
        Or.elim hz
          (fun htop =>
            Exists.elim htop
              (fun u htop_u =>
                Exists.elim htop_u
                  (fun x htop_x =>
                    Eq.subst
                      (motive := fun w : ℂ =>
                        min family.c (1 - family.c) ≤ w.re ∧
                          w.re ≤ max family.c (1 - family.c))
                      htop_x.2.symm
                      (schedule.topPath_zeroExcisedPointwise u x htop_x.1).1)))
          (fun hbottom =>
            Exists.elim hbottom
              (fun u hbottom_u =>
                Exists.elim hbottom_u
                  (fun x hbottom_x =>
                    Eq.subst
                      (motive := fun w : ℂ =>
                        min family.c (1 - family.c) ≤ w.re ∧
                          w.re ≤ max family.c (1 - family.c))
                      hbottom_x.2.symm
                      (schedule.bottomPath_zeroExcisedPointwise u x hbottom_x.1).1)))
    ne_zero :=
      fun z hz =>
        Or.elim hz
          (fun htop =>
            Exists.elim htop
              (fun u htop_u =>
                Exists.elim htop_u
                  (fun x htop_x =>
                    Eq.subst
                      (motive := fun w : ℂ => w ≠ 0)
                      htop_x.2.symm
                      (schedule.topPath_zeroExcisedPointwise u x htop_x.1).2.1)))
          (fun hbottom =>
            Exists.elim hbottom
              (fun u hbottom_u =>
                Exists.elim hbottom_u
                  (fun x hbottom_x =>
                    Eq.subst
                      (motive := fun w : ℂ => w ≠ 0)
                      hbottom_x.2.symm
                      (schedule.bottomPath_zeroExcisedPointwise u x hbottom_x.1).2.1)))
    ne_one :=
      fun z hz =>
        Or.elim hz
          (fun htop =>
            Exists.elim htop
              (fun u htop_u =>
                Exists.elim htop_u
                  (fun x htop_x =>
                    Eq.subst
                      (motive := fun w : ℂ => w ≠ 1)
                      htop_x.2.symm
                      (schedule.topPath_zeroExcisedPointwise u x htop_x.1).2.2.1)))
          (fun hbottom =>
            Exists.elim hbottom
              (fun u hbottom_u =>
                Exists.elim hbottom_u
                  (fun x hbottom_x =>
                    Eq.subst
                      (motive := fun w : ℂ => w ≠ 1)
                      hbottom_x.2.symm
                      (schedule.bottomPath_zeroExcisedPointwise u x hbottom_x.1).2.2.1)))
    zeta_ne_zero :=
      fun z hz =>
        Or.elim hz
          (fun htop =>
            Exists.elim htop
              (fun u htop_u =>
                Exists.elim htop_u
                  (fun x htop_x =>
                    Eq.subst
                      (motive := fun w : ℂ => completedRiemannZeta w ≠ 0)
                      htop_x.2.symm
                      (schedule.topPath_zeroExcisedPointwise u x htop_x.1).2.2.2.1)))
          (fun hbottom =>
            Exists.elim hbottom
              (fun u hbottom_u =>
                Exists.elim hbottom_u
                  (fun x hbottom_x =>
                    Eq.subst
                      (motive := fun w : ℂ => completedRiemannZeta w ≠ 0)
                      hbottom_x.2.symm
                      (schedule.bottomPath_zeroExcisedPointwise u x hbottom_x.1).2.2.2.1)))
    gamma_ne_zero :=
      fun z hz =>
        Or.elim hz
          (fun htop =>
            Exists.elim htop
              (fun u htop_u =>
                Exists.elim htop_u
                  (fun x htop_x =>
                    Eq.subst
                      (motive := fun w : ℂ => Complex.Gammaℝ w ≠ 0)
                      htop_x.2.symm
                      (schedule.topPath_zeroExcisedPointwise u x htop_x.1).2.2.2.2.1)))
          (fun hbottom =>
            Exists.elim hbottom
              (fun u hbottom_u =>
                Exists.elim hbottom_u
                  (fun x hbottom_x =>
                    Eq.subst
                      (motive := fun w : ℂ => Complex.Gammaℝ w ≠ 0)
                      hbottom_x.2.symm
                      (schedule.bottomPath_zeroExcisedPointwise u x hbottom_x.1).2.2.2.2.1))) }

/-- The canonical scheduled horizontal carrier for the autocorrelation contour. -/
def zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
    (f : ZetaAdmissibleFunction) :
    CompletedZetaZeroExcisedStrip
      (min (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
      (max (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
    f
    (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f)

/-! The carrier representation is exported at the owner boundary.  Keeping
this equality named prevents downstream Cauchy and separation arguments from
unfolding the `CompletedZetaZeroExcisedStrip` package and accidentally treating
the scheduled union of horizontal paths as a compact set. -/

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_carrier_eq_set
    (f : ZetaAdmissibleFunction) :
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier =
      zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrierSet f :=
  rfl

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_carrier_eq_set_of_cofinalSchedule
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)) :
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
      f schedule).carrier =
      zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrierSet_of_cofinalSchedule
        f schedule :=
  rfl

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_mem_cases
    (f : ZetaAdmissibleFunction) (z : ℂ)
    (hz : z ∈
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier) :
    (∃ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) ∧
      z = zetaCompletedExplicitFormulaTopPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x) ∨
    (∃ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) ∧
      z = zetaCompletedExplicitFormulaBottomPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x) :=
  Eq.subst
    (motive := fun s : Set ℂ => z ∈ s)
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_carrier_eq_set f)
    hz

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_mem_cases_of_cofinalSchedule
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (z : ℂ)
    (hz : z ∈
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
        f schedule).carrier) :
    (∃ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) ∧
      z = zetaCompletedExplicitFormulaTopPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          (schedule.height u)) x) ∨
    (∃ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) ∧
      z = zetaCompletedExplicitFormulaBottomPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          (schedule.height u)) x) :=
  Eq.subst
    (motive := fun s : Set ℂ => z ∈ s)
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_carrier_eq_set_of_cofinalSchedule
      f schedule)
    hz

/-- Top scheduled horizontal points lie in the supplied scheduled carrier. -/
theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem_of_cofinalSchedule
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (u x : ℝ)
    (hx :
      x ∈
        Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    zetaCompletedExplicitFormulaTopPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          (schedule.height u))
        x ∈
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
        f schedule).carrier :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem_set_of_cofinalSchedule
    f
    schedule
    u
    x
    hx

/-- Bottom scheduled horizontal points lie in the supplied scheduled carrier. -/
theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bottom_mem_of_cofinalSchedule
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (u x : ℝ)
    (hx :
      x ∈
        Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    zetaCompletedExplicitFormulaBottomPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          (schedule.height u))
        x ∈
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
        f schedule).carrier :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bottom_mem_set_of_cofinalSchedule
    f
    schedule
    u
    x
    hx

/-- Top scheduled horizontal points lie in the canonical scheduled carrier. -/
theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hx :
      x ∈
        Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    zetaCompletedExplicitFormulaTopPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
        x ∈
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem_set
    f u x hx

/-- Bottom scheduled horizontal points lie in the canonical scheduled carrier. -/
theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bottom_mem
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hx :
      x ∈
        Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    zetaCompletedExplicitFormulaBottomPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
        x ∈
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bottom_mem_set
    f u x hx

/-- Separate zeta-side and inverse-Gamma bounds on a supplied scheduled
horizontal carrier assemble into factor data. -/
def zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_factorData_of_parts_of_cofinalSchedule
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (zetaData :
      CompletedZetaZeroExcisedStrip.ZetaSideBoundData
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
          f schedule))
    (gammaData :
      CompletedZetaZeroExcisedStrip.InverseGammaBoundData
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
          f schedule)) :
    CompletedZetaZeroExcisedStrip.FactorBoundData
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
        f schedule) :=
  CompletedZetaZeroExcisedStrip.FactorBoundData.ofParts
    zetaData
    gammaData

/-- Separate zeta-side and inverse-Gamma bounds on the canonical scheduled
horizontal carrier assemble into canonical factor data. -/
def zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_factorData_of_parts
    (f : ZetaAdmissibleFunction)
    (zetaData :
      CompletedZetaZeroExcisedStrip.ZetaSideBoundData
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (gammaData :
      CompletedZetaZeroExcisedStrip.InverseGammaBoundData
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)) :
    CompletedZetaZeroExcisedStrip.FactorBoundData
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f) :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_factorData_of_parts_of_cofinalSchedule
    f
    (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f)
    zetaData
    gammaData

/-- A factor bound on a supplied scheduled carrier constructs the scheduled
autocorrelation analytic package. -/
def zetaCompletedExplicitFormulaAutocorrelationScheduledFamilyAnalyticPackage_of_cofinalScheduleCarrierFactorData
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi :
      ZetaPhiAnalyticControl
        (convolutionAutocorrelation f))
    (factorData :
      CompletedZetaZeroExcisedStrip.FactorBoundData
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
          f schedule)) :
    ExplicitFormulaScheduledFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  ExplicitFormulaScheduledFamilyAnalyticPackage.ofFactorBoundData
    hPhi
    schedule
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
      f schedule)
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem_of_cofinalSchedule
      f schedule)
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bottom_mem_of_cofinalSchedule
      f schedule)
    factorData

/-- A factor bound on the canonical scheduled carrier constructs the scheduled
autocorrelation analytic package. -/
def zetaCompletedExplicitFormulaAutocorrelationScheduledFamilyAnalyticPackage_of_carrierFactorData
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl
        (convolutionAutocorrelation f))
    (factorData :
      CompletedZetaZeroExcisedStrip.FactorBoundData
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)) :
    ExplicitFormulaScheduledFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledFamilyAnalyticPackage_of_cofinalScheduleCarrierFactorData
    f
    (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f)
    hPhi
    factorData

/-- Separate factor bounds on the canonical scheduled carrier construct the
scheduled autocorrelation analytic package. -/
def zetaCompletedExplicitFormulaAutocorrelationScheduledFamilyAnalyticPackage_of_carrierBoundData
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl
        (convolutionAutocorrelation f))
    (zetaData :
      CompletedZetaZeroExcisedStrip.ZetaSideBoundData
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (gammaData :
      CompletedZetaZeroExcisedStrip.InverseGammaBoundData
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)) :
    ExplicitFormulaScheduledFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledFamilyAnalyticPackage_of_carrierFactorData
    f
    hPhi
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_factorData_of_parts
      f
      zetaData
      gammaData)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
