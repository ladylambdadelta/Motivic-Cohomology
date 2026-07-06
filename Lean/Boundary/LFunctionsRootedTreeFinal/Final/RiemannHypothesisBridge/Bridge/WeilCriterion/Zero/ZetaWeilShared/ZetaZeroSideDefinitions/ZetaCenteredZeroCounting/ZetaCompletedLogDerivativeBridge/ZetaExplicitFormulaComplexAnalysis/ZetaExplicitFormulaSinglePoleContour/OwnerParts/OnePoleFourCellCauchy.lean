import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaSinglePoleContour.OwnerParts.PositiveHeightRawCauchy

/-!
# Four-cell Cauchy specialization for the isolated `s = 1` correction pole

This file specializes the general four-cell Cauchy-Goursat theorem from the
single-pole contour owner to the isolated correction kernel

`z ↦ zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z`

and the one-point exceptional set `{1}`.  The remaining hypotheses are the real
analytic facts that the kernel is continuous on each closed cell and
differentiable on each open cell away from the pole.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The one-point exceptional set for the isolated `s = 1` correction kernel is
countable. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_singleton_countable :
    ({(1 : ℂ)} : Set ℂ).Countable :=
  Set.countable_singleton (1 : ℂ)

/-- A complex point with negative imaginary coordinate is not the pole `1`. -/
theorem zetaExplicitFormulaOnePole_ne_one_of_im_lt_zero
    {z : ℂ} (hz : z.im < 0) :
    z - 1 ≠ 0 := by
  intro hzero
  have hz_one : z = 1 :=
    sub_eq_zero.mp hzero
  have him_eq : z.im = (1 : ℂ).im :=
    congrArg Complex.im hz_one
  have him_zero : z.im = 0 := by
    calc
      z.im = (1 : ℂ).im := him_eq
      _ = 0 := Complex.ofReal_im (1 : ℝ)
  exact (lt_irrefl (0 : ℝ)) (Eq.subst (motive := fun y : ℝ => y < 0) him_zero hz)

/-- A complex point with positive imaginary coordinate is not the pole `1`. -/
theorem zetaExplicitFormulaOnePole_ne_one_of_zero_lt_im
    {z : ℂ} (hz : 0 < z.im) :
    z - 1 ≠ 0 := by
  intro hzero
  have hz_one : z = 1 :=
    sub_eq_zero.mp hzero
  have him_eq : z.im = (1 : ℂ).im :=
    congrArg Complex.im hz_one
  have him_zero : z.im = 0 := by
    calc
      z.im = (1 : ℂ).im := him_eq
      _ = 0 := Complex.ofReal_im (1 : ℝ)
  exact (lt_irrefl (0 : ℝ)) (Eq.subst (motive := fun y : ℝ => 0 < y) him_zero hz)

/-- A complex point with real coordinate below `1` is not the pole `1`. -/
theorem zetaExplicitFormulaOnePole_ne_one_of_re_lt_one
    {z : ℂ} (hz : z.re < 1) :
    z - 1 ≠ 0 := by
  intro hzero
  have hz_one : z = 1 :=
    sub_eq_zero.mp hzero
  have hre_eq : z.re = (1 : ℂ).re :=
    congrArg Complex.re hz_one
  have hre_one : z.re = 1 := by
    calc
      z.re = (1 : ℂ).re := hre_eq
      _ = 1 := Complex.ofReal_re (1 : ℝ)
  exact (lt_irrefl (1 : ℝ)) (Eq.subst (motive := fun x : ℝ => x < 1) hre_one hz)

/-- A complex point with real coordinate above `1` is not the pole `1`. -/
theorem zetaExplicitFormulaOnePole_ne_one_of_one_lt_re
    {z : ℂ} (hz : 1 < z.re) :
    z - 1 ≠ 0 := by
  intro hzero
  have hz_one : z = 1 :=
    sub_eq_zero.mp hzero
  have hre_eq : z.re = (1 : ℂ).re :=
    congrArg Complex.re hz_one
  have hre_one : z.re = 1 := by
    calc
      z.re = (1 : ℂ).re := hre_eq
      _ = 1 := Complex.ofReal_re (1 : ℝ)
  exact (lt_irrefl (1 : ℝ)) (Eq.subst (motive := fun x : ℝ => 1 < x) hre_one hz)

/-- Membership in the deleted singleton `{1}` is the same off-pole condition
needed by the correction-kernel differentiability theorem. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleKernel_differentiableAt_of_not_mem_singleton
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ} (hz : z ∉ ({(1 : ℂ)} : Set ℂ)) :
    DifferentiableAt ℂ
      (fun w : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
      z := by
  have hz_ne_one : z ≠ 1 := by
    intro hz_one
    have hz_mem : z ∈ ({(1 : ℂ)} : Set ℂ) :=
      hz_one
    exact hz hz_mem
  exact
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel_differentiableAt_off_pole
      f hPhi (sub_ne_zero.mpr hz_ne_one)

/-- The lower canonical four-cell lies strictly below the real axis, hence
avoids the isolated pole `1`. -/
theorem zetaExplicitFormulaOnePole_canonicalBottomCell_avoids_one_of_pos_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    ∀ z : ℂ,
      z ∈
          (Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).re ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re ×ℂ
            Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im) →
        z - 1 ≠ 0 := by
  intro z hz
  have hR_pos :
      0 < zetaExplicitFormulaOnePolePunctureRadius F T :=
    zetaCompletedExplicitFormulaCorrectionOnePole_punctureRadius_pos_of_pos_height
      F hT
  have hbottom_left :
      (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im < 0 := by
    calc
      (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im = -T :=
        zetaExplicitFormulaOnePole_horizontalAffine_im (1 - F.c) (-T)
      _ < 0 := neg_lt_zero.mpr hT
  have hbottom_right :
      ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im < 0 := by
    calc
      ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im =
          -(zetaExplicitFormulaOnePolePunctureRadius F T) :=
        zetaExplicitFormulaOnePole_horizontalAffine_im
          F.c (-(zetaExplicitFormulaOnePolePunctureRadius F T))
      _ < 0 := neg_lt_zero.mpr hR_pos
  have him_mem :
      z.im ∈
        Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im :=
    (Complex.mem_reProdIm.mp hz).2
  have him_sup_lt :
      ((((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im ⊔
        ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im) < 0 :=
    sup_lt_iff.mpr (And.intro hbottom_left hbottom_right)
  have him_lt_zero : z.im < 0 :=
    lt_of_le_of_lt him_mem.2 him_sup_lt
  exact zetaExplicitFormulaOnePole_ne_one_of_im_lt_zero him_lt_zero

/-- The upper canonical four-cell lies strictly above the real axis, hence
avoids the isolated pole `1`. -/
theorem zetaExplicitFormulaOnePole_canonicalTopCell_avoids_one_of_pos_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    ∀ z : ℂ,
      z ∈
          (Set.uIcc (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re ((F.c : ℂ) + (T : ℂ) * Complex.I).re ×ℂ
            Set.uIcc (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im ((F.c : ℂ) + (T : ℂ) * Complex.I).im) →
        z - 1 ≠ 0 := by
  intro z hz
  have hR_pos :
      0 < zetaExplicitFormulaOnePolePunctureRadius F T :=
    zetaCompletedExplicitFormulaCorrectionOnePole_punctureRadius_pos_of_pos_height
      F hT
  have htop_left :
      (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im >
        0 := by
    calc
      0 < zetaExplicitFormulaOnePolePunctureRadius F T := hR_pos
      _ =
          (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im := by
        exact
          (zetaExplicitFormulaOnePole_horizontalAffine_im
            (1 - F.c) (zetaExplicitFormulaOnePolePunctureRadius F T)).symm
  have htop_right :
      ((F.c : ℂ) + (T : ℂ) * Complex.I).im > 0 := by
    calc
      0 < T := hT
      _ = ((F.c : ℂ) + (T : ℂ) * Complex.I).im := by
        exact (zetaExplicitFormulaOnePole_horizontalAffine_im F.c T).symm
  have him_mem :
      z.im ∈
        Set.uIcc (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im ((F.c : ℂ) + (T : ℂ) * Complex.I).im :=
    (Complex.mem_reProdIm.mp hz).2
  have him_inf_pos :
      0 <
        ((((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im ⊓
          ((F.c : ℂ) + (T : ℂ) * Complex.I).im) :=
    lt_inf_iff.mpr (And.intro htop_left htop_right)
  have hzero_lt_im : 0 < z.im :=
    lt_of_lt_of_le him_inf_pos him_mem.1
  exact zetaExplicitFormulaOnePole_ne_one_of_zero_lt_im hzero_lt_im

/-- The left canonical four-cell lies strictly to the left of the pole's real
coordinate. -/
theorem zetaExplicitFormulaOnePole_canonicalLeftCell_avoids_one_of_pos_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    ∀ z : ℂ,
      z ∈
          (Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re ×ℂ
            Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im) →
        z - 1 ≠ 0 := by
  intro z hz
  have hR_pos :
      0 < zetaExplicitFormulaOnePolePunctureRadius F T :=
    zetaCompletedExplicitFormulaCorrectionOnePole_punctureRadius_pos_of_pos_height
      F hT
  have hc_pos : 0 < F.c :=
    lt_trans zero_lt_one F.c_gt_one
  have hleft_lower :
      (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re < 1 := by
    calc
      (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re = 1 - F.c :=
        zetaExplicitFormulaOnePole_verticalAffine_re
          (1 - F.c) (-(zetaExplicitFormulaOnePolePunctureRadius F T))
      _ < 1 := sub_lt_self 1 hc_pos
  have hleft_upper :
      (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re < 1 := by
    calc
      (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re =
          1 - zetaExplicitFormulaOnePolePunctureRadius F T :=
        zetaExplicitFormulaOnePole_verticalAffine_re
          (1 - zetaExplicitFormulaOnePolePunctureRadius F T)
          (zetaExplicitFormulaOnePolePunctureRadius F T)
      _ < 1 := sub_lt_self 1 hR_pos
  have hre_mem :
      z.re ∈
        Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re :=
    (Complex.mem_reProdIm.mp hz).1
  have hre_sup_lt :
      ((((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re ⊔
        (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re) < 1 :=
    sup_lt_iff.mpr (And.intro hleft_lower hleft_upper)
  have hre_lt_one : z.re < 1 :=
    lt_of_le_of_lt hre_mem.2 hre_sup_lt
  exact zetaExplicitFormulaOnePole_ne_one_of_re_lt_one hre_lt_one

/-- The right canonical four-cell lies strictly to the right of the pole's real
coordinate. -/
theorem zetaExplicitFormulaOnePole_canonicalRightCell_avoids_one_of_pos_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    ∀ z : ℂ,
      z ∈
          (Set.uIcc (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re ×ℂ
            Set.uIcc (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im) →
        z - 1 ≠ 0 := by
  intro z hz
  have hR_pos :
      0 < zetaExplicitFormulaOnePolePunctureRadius F T :=
    zetaCompletedExplicitFormulaCorrectionOnePole_punctureRadius_pos_of_pos_height
      F hT
  have hright_lower :
      1 <
        (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re := by
    calc
      1 < 1 + zetaExplicitFormulaOnePolePunctureRadius F T :=
        lt_add_of_pos_right 1 hR_pos
      _ =
          (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re := by
        exact
          (zetaExplicitFormulaOnePole_verticalAffine_re
            (1 + zetaExplicitFormulaOnePolePunctureRadius F T)
            (-(zetaExplicitFormulaOnePolePunctureRadius F T))).symm
  have hright_upper :
      1 <
        ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re := by
    calc
      1 < F.c := F.c_gt_one
      _ =
          ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re := by
        exact
          (zetaExplicitFormulaOnePole_verticalAffine_re
            F.c (zetaExplicitFormulaOnePolePunctureRadius F T)).symm
  have hre_mem :
      z.re ∈
        Set.uIcc (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re :=
    (Complex.mem_reProdIm.mp hz).1
  have hre_inf_gt :
      1 <
        ((((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re ⊓
          ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re) :=
    lt_inf_iff.mpr (And.intro hright_lower hright_upper)
  have hone_lt_re : 1 < z.re :=
    lt_of_lt_of_le hre_inf_gt hre_mem.1
  exact zetaExplicitFormulaOnePole_ne_one_of_one_lt_re hone_lt_re

/-- Four-cell Cauchy cancellation for the isolated `s = 1` correction kernel,
with the exceptional set fixed to the pole `{1}` on every cell. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_fourCellBoundary_eq_zero_of_cellRegularity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (HcBottom :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).re ((F.c : ℂ) + ((-R : ℝ) : ℂ) * Complex.I).re ×ℂ
          Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im ((F.c : ℂ) + ((-R : ℝ) : ℂ) * Complex.I).im))
    (HdBottom :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).re
                  ((F.c : ℂ) + ((-R : ℝ) : ℂ) * Complex.I).re)
                (max (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).re
                  ((F.c : ℂ) + ((-R : ℝ) : ℂ) * Complex.I).re) ×ℂ
              Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im
                  ((F.c : ℂ) + ((-R : ℝ) : ℂ) * Complex.I).im)
                (max (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im
                  ((F.c : ℂ) + ((-R : ℝ) : ℂ) * Complex.I).im) \ ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x)
    (HcTop :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (Set.uIcc (((1 - F.c : ℝ) : ℂ) + (R : ℂ) * Complex.I).re ((F.c : ℂ) + (T : ℂ) * Complex.I).re ×ℂ
          Set.uIcc (((1 - F.c : ℝ) : ℂ) + (R : ℂ) * Complex.I).im ((F.c : ℂ) + (T : ℂ) * Complex.I).im))
    (HdTop :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + (R : ℂ) * Complex.I).re
                  ((F.c : ℂ) + (T : ℂ) * Complex.I).re)
                (max (((1 - F.c : ℝ) : ℂ) + (R : ℂ) * Complex.I).re
                  ((F.c : ℂ) + (T : ℂ) * Complex.I).re) ×ℂ
              Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + (R : ℂ) * Complex.I).im
                  ((F.c : ℂ) + (T : ℂ) * Complex.I).im)
                (max (((1 - F.c : ℝ) : ℂ) + (R : ℂ) * Complex.I).im
                  ((F.c : ℂ) + (T : ℂ) * Complex.I).im) \ ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x)
    (HcLeft :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * Complex.I).re (((1 - R : ℝ) : ℂ) + (R : ℂ) * Complex.I).re ×ℂ
          Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * Complex.I).im (((1 - R : ℝ) : ℂ) + (R : ℂ) * Complex.I).im))
    (HdLeft :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * Complex.I).re
                  (((1 - R : ℝ) : ℂ) + (R : ℂ) * Complex.I).re)
                (max (((1 - F.c : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * Complex.I).re
                  (((1 - R : ℝ) : ℂ) + (R : ℂ) * Complex.I).re) ×ℂ
              Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * Complex.I).im
                  (((1 - R : ℝ) : ℂ) + (R : ℂ) * Complex.I).im)
                (max (((1 - F.c : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * Complex.I).im
                  (((1 - R : ℝ) : ℂ) + (R : ℂ) * Complex.I).im) \ ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x)
    (HcRight :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (Set.uIcc (((1 + R : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * Complex.I).re ((F.c : ℂ) + (R : ℂ) * Complex.I).re ×ℂ
          Set.uIcc (((1 + R : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * Complex.I).im ((F.c : ℂ) + (R : ℂ) * Complex.I).im))
    (HdRight :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min (((1 + R : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * Complex.I).re
                  ((F.c : ℂ) + (R : ℂ) * Complex.I).re)
                (max (((1 + R : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * Complex.I).re
                  ((F.c : ℂ) + (R : ℂ) * Complex.I).re) ×ℂ
              Set.Ioo
                (min (((1 + R : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * Complex.I).im
                  ((F.c : ℂ) + (R : ℂ) * Complex.I).im)
                (max (((1 + R : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * Complex.I).im
                  ((F.c : ℂ) + (R : ℂ) * Complex.I).im) \ ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x) :
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
      F T R = 0 := by
  exact
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum_eq_zero_of_cauchy
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
      F T R
      ({(1 : ℂ)} : Set ℂ)
      ({(1 : ℂ)} : Set ℂ)
      ({(1 : ℂ)} : Set ℂ)
      ({(1 : ℂ)} : Set ℂ)
      zetaCompletedExplicitFormulaCorrectionOnePole_singleton_countable
      zetaCompletedExplicitFormulaCorrectionOnePole_singleton_countable
      zetaCompletedExplicitFormulaCorrectionOnePole_singleton_countable
      zetaCompletedExplicitFormulaCorrectionOnePole_singleton_countable
      HcBottom HdBottom HcTop HdTop HcLeft HdLeft HcRight HdRight

/-- Canonical-puncture-radius four-cell Cauchy cancellation for the isolated
`s = 1` correction kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_fourCellBoundary_eq_zero_of_cellRegularity_canonicalRadius
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) {T : ℝ}
    (HcBottom :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).re ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re ×ℂ
          Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im))
    (HdBottom :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).re
                  ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re)
                (max (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).re
                  ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re) ×ℂ
              Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im
                  ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im)
                (max (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im
                  ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im) \
                  ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x)
    (HcTop :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (Set.uIcc (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re ((F.c : ℂ) + (T : ℂ) * Complex.I).re ×ℂ
          Set.uIcc (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im ((F.c : ℂ) + (T : ℂ) * Complex.I).im))
    (HdTop :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re
                  ((F.c : ℂ) + (T : ℂ) * Complex.I).re)
                (max (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re
                  ((F.c : ℂ) + (T : ℂ) * Complex.I).re) ×ℂ
              Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im
                  ((F.c : ℂ) + (T : ℂ) * Complex.I).im)
                (max (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im
                  ((F.c : ℂ) + (T : ℂ) * Complex.I).im) \ ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x)
    (HcLeft :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re ×ℂ
          Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im))
    (HdLeft :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re
                  (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re)
                (max (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re
                  (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re) ×ℂ
              Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im
                  (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im)
                (max (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im
                  (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im) \
                  ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x)
    (HcRight :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (Set.uIcc (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re ×ℂ
          Set.uIcc (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im))
    (HdRight :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re
                  ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re)
                (max (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re
                  ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re) ×ℂ
              Set.Ioo
                (min (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im
                  ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im)
                (max (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im
                  ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im) \
                  ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x) :
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
      F T (zetaExplicitFormulaOnePolePunctureRadius F T) = 0 := by
  exact
    zetaCompletedExplicitFormulaCorrectionOnePole_fourCellBoundary_eq_zero_of_cellRegularity
      f F T (zetaExplicitFormulaOnePolePunctureRadius F T)
      HcBottom HdBottom HcTop HdTop HcLeft HdLeft HcRight HdRight

/-- Positive-height raw standard Cauchy value from the canonical four-cell
Cauchy regularity hypotheses, the square-punctured boundary decomposition, and
the inner-square residue calculation. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_cellRegularity_boundary_inner
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T : ℝ}
    (hT : 0 < T)
    (hboundary :
      zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T) =
      zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T))
    (HcBottom :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).re ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re ×ℂ
          Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im))
    (HdBottom :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).re
                  ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re)
                (max (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).re
                  ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re) ×ℂ
              Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im
                  ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im)
                (max (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im
                  ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im) \
                  ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x)
    (HcTop :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (Set.uIcc (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re ((F.c : ℂ) + (T : ℂ) * Complex.I).re ×ℂ
          Set.uIcc (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im ((F.c : ℂ) + (T : ℂ) * Complex.I).im))
    (HdTop :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re
                  ((F.c : ℂ) + (T : ℂ) * Complex.I).re)
                (max (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re
                  ((F.c : ℂ) + (T : ℂ) * Complex.I).re) ×ℂ
              Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im
                  ((F.c : ℂ) + (T : ℂ) * Complex.I).im)
                (max (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im
                  ((F.c : ℂ) + (T : ℂ) * Complex.I).im) \ ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x)
    (HcLeft :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re ×ℂ
          Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im))
    (HdLeft :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re
                  (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re)
                (max (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re
                  (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re) ×ℂ
              Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im
                  (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im)
                (max (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im
                  (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im) \
                  ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x)
    (HcRight :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (Set.uIcc (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re ×ℂ
          Set.uIcc (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im))
    (HdRight :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re
                  ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re)
                (max (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re
                  ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re) ×ℂ
              Set.Ioo
                (min (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im
                  ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im)
                (max (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im
                  ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im) \
                  ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x)
    (hinner :
      zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (zetaExplicitFormulaOnePolePunctureRadius F T) =
        (2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) :
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
      f F T =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2)) := by
  have hfour :
      zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T) = 0 :=
    zetaCompletedExplicitFormulaCorrectionOnePole_fourCellBoundary_eq_zero_of_cellRegularity_canonicalRadius
      f F HcBottom HdBottom HcTop HdTop HcLeft HdLeft HcRight HdRight
  exact
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height_geometric_inputs
      f F hT hboundary hfour hinner

/-- Canonical four-cell Cauchy cancellation for the isolated `s = 1`
correction kernel at positive height.  The proof is the regularity discharge
for the four concrete cells in
`zetaCompletedExplicitFormulaCorrectionOnePole_fourCellBoundary_eq_zero_of_cellRegularity_canonicalRadius`. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_canonicalFourCellBoundary_eq_zero_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (T : ℝ)
    (hT : 0 < T) :
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T) = 0 := by
  have HcBottom :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).re ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re ×ℂ
          Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im) :=
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel_continuousOn_of_avoids_pole
      f h.phi_control
      (Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).re ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re ×ℂ
        Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im)
      (zetaExplicitFormulaOnePole_canonicalBottomCell_avoids_one_of_pos_height
        F hT)
  have HdBottom :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).re
                  ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re)
                (max (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).re
                  ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re) ×ℂ
              Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im
                  ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im)
                (max (((1 - F.c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im
                  ((F.c : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im) \
                  ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x := by
    intro x hx
    exact
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel_differentiableAt_of_not_mem_singleton
        f h.phi_control hx.2
  have HcTop :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (Set.uIcc (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re ((F.c : ℂ) + (T : ℂ) * Complex.I).re ×ℂ
          Set.uIcc (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im ((F.c : ℂ) + (T : ℂ) * Complex.I).im) :=
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel_continuousOn_of_avoids_pole
      f h.phi_control
      (Set.uIcc (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re ((F.c : ℂ) + (T : ℂ) * Complex.I).re ×ℂ
        Set.uIcc (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im ((F.c : ℂ) + (T : ℂ) * Complex.I).im)
      (zetaExplicitFormulaOnePole_canonicalTopCell_avoids_one_of_pos_height
        F hT)
  have HdTop :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re
                  ((F.c : ℂ) + (T : ℂ) * Complex.I).re)
                (max (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re
                  ((F.c : ℂ) + (T : ℂ) * Complex.I).re) ×ℂ
              Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im
                  ((F.c : ℂ) + (T : ℂ) * Complex.I).im)
                (max (((1 - F.c : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im
                  ((F.c : ℂ) + (T : ℂ) * Complex.I).im) \ ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x := by
    intro x hx
    exact
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel_differentiableAt_of_not_mem_singleton
        f h.phi_control hx.2
  have HcLeft :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re ×ℂ
          Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im) :=
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel_continuousOn_of_avoids_pole
      f h.phi_control
      (Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re ×ℂ
        Set.uIcc (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im)
      (zetaExplicitFormulaOnePole_canonicalLeftCell_avoids_one_of_pos_height
        F hT)
  have HdLeft :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re
                  (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re)
                (max (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re
                  (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re) ×ℂ
              Set.Ioo
                (min (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im
                  (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im)
                (max (((1 - F.c : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im
                  (((1 - zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im) \
                  ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x := by
    intro x hx
    exact
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel_differentiableAt_of_not_mem_singleton
        f h.phi_control hx.2
  have HcRight :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (Set.uIcc (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re ×ℂ
          Set.uIcc (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im) :=
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel_continuousOn_of_avoids_pole
      f h.phi_control
      (Set.uIcc (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re ×ℂ
        Set.uIcc (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im)
      (zetaExplicitFormulaOnePole_canonicalRightCell_avoids_one_of_pos_height
        F hT)
  have HdRight :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re
                  ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re)
                (max (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).re
                  ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).re) ×ℂ
              Set.Ioo
                (min (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im
                  ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im)
                (max (((1 + zetaExplicitFormulaOnePolePunctureRadius F T : ℝ) : ℂ) + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I).im
                  ((F.c : ℂ) + (zetaExplicitFormulaOnePolePunctureRadius F T : ℂ) * Complex.I).im) \
                  ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x := by
    intro x hx
    exact
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel_differentiableAt_of_not_mem_singleton
        f h.phi_control hx.2
  exact
    zetaCompletedExplicitFormulaCorrectionOnePole_fourCellBoundary_eq_zero_of_cellRegularity_canonicalRadius
      f F
      HcBottom HdBottom
      HcTop HdTop
      HcLeft HdLeft
      HcRight HdRight

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
