import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseConnectorParametrization

/-!
# Horizontal assembly for semicircle staircase cells

This file owns the finite horizontal-side telescoping identity used by the
staircase geometry assembly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- Paired horizontal sides of the staircase-cell rectangles telescope to the
outer bottom side minus the outer top side and the staircase horizontal
connectors. -/
theorem Complex.sum_rightSemicircleStaircaseCellHorizontal_eq_outerHorizontal_sub_arcHorizontal
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    (∑ k in Finset.range (m + 1),
        ((∫ x : ℝ in
            (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
            f ((x : ℂ) +
              Complex.I *
                (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))) -
          (∫ x : ℝ in
            (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
            f ((x : ℂ) +
              Complex.I *
                (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ)))))) =
      (∫ x : ℝ in c.re..(c.re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) -
        (∫ x : ℝ in c.re..(c.re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) -
        (∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) -
        Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m := by
  let F : ℕ → ℝ → ℂ := fun k x =>
    f ((x : ℂ) +
      Complex.I *
        (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))
  let X : ℕ → ℝ := fun k =>
    c.re + Complex.rightSemicircleStaircasePrevSafeRe ρ m k
  let B : ℝ := c.re + ρ
  have hconn :
      ∀ k ∈ Finset.range (m + 1),
        IntervalIntegrable (F k) volume (X k) (X (k + 1)) := by
    intro k hk
    have hnext :
        X (k + 1) =
          c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k := by
      exact
        Complex.rightSemicircleStaircasePrevSafeRe_succ_add_re c ρ m k
    have habs :
        IntervalIntegrable (F k) volume (X k)
          (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k) :=
      Complex.intervalIntegrable_rightSemicircleStaircaseHorizontal_absolute
        f c hρ m k hk hcont
    exact
      Eq.subst
        (motive := fun b : ℝ => IntervalIntegrable (F k) volume (X k) b)
        (Eq.symm hnext)
        habs
  have htail :
      ∀ k ∈ Finset.range (m + 1),
        IntervalIntegrable (F k) volume (X (k + 1)) B := by
    intro k hk
    have hnext :
        X (k + 1) =
          c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k := by
      exact
        Complex.rightSemicircleStaircasePrevSafeRe_succ_add_re c ρ m k
    have htail_abs :
        IntervalIntegrable (F k) volume
          (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k) B :=
      Complex.intervalIntegrable_rightSemicircleStaircaseCellBottomTail
        f c hρ m k hk hcont
    exact
      Eq.subst
        (motive := fun a : ℝ => IntervalIntegrable (F k) volume a B)
        (Eq.symm hnext)
        htail_abs
  have hFtop :
      F (m + 1) =
        fun x : ℝ =>
          f ((x : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) :=
    Complex.rightSemicircleStaircaseHorizontalTailIntegrand_last f c ρ m
  have hend_seg :
      IntervalIntegrable (F (m + 1)) volume (X 0) (X (m + 1)) := by
    have hzero :
        X 0 = c.re := by
      exact Complex.rightSemicircleStaircasePrevSafeRe_zero_add_re c ρ m
    have hnext :
        X (m + 1) =
          c.re + Complex.rightSemicircleStaircaseSafeRe ρ m m := by
      exact
        Complex.rightSemicircleStaircasePrevSafeRe_succ_add_re c ρ m m
    have habs_symm :
        IntervalIntegrable (F (m + 1)) volume
          c.re (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m m) := by
      exact
        Eq.subst
          (motive := fun G : ℝ → ℂ =>
            IntervalIntegrable G volume
              c.re (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m m))
          (Eq.symm hFtop)
          ((Complex.intervalIntegrable_rightSemicircleStaircaseTopConnector_absolute
            f c hρ m hcont).symm)
    exact
      Eq.subst
        (motive := fun a : ℝ =>
          IntervalIntegrable (F (m + 1)) volume a (X (m + 1)))
        (Eq.symm hzero)
        (Eq.subst
          (motive := fun b : ℝ =>
            IntervalIntegrable (F (m + 1)) volume c.re b)
          (Eq.symm hnext)
          habs_symm)
  have hend_tail :
      IntervalIntegrable (F (m + 1)) volume (X (m + 1)) B := by
    have hm : m ∈ Finset.range (m + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_self m)
    have hnext :
        X (m + 1) =
          c.re + Complex.rightSemicircleStaircaseSafeRe ρ m m := by
      exact
        Complex.rightSemicircleStaircasePrevSafeRe_succ_add_re c ρ m m
    have hB : B = c.re + ρ := rfl
    have htail_abs :
        IntervalIntegrable (F (m + 1)) volume
          (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m m) B :=
      Eq.subst
        (motive := fun b : ℝ =>
          IntervalIntegrable (F (m + 1)) volume
            (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m m) b)
        (Eq.symm hB)
        (Complex.intervalIntegrable_rightSemicircleStaircaseCellTopTail
          f c hρ m m hm hcont)
    exact
      Eq.subst
        (motive := fun a : ℝ => IntervalIntegrable (F (m + 1)) volume a B)
        (Eq.symm hnext)
        htail_abs
  have htail_tel :=
    Complex.sum_rightTail_integral_sub_successor_eq_endpoint_sub_connectors
      F X B m hconn htail hend_seg hend_tail
  have hconnectors :
      (∑ k in Finset.range (m + 1),
          ∫ t : ℝ in X k..X (k + 1), F k t) =
        ∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k := by
    apply Finset.sum_congr rfl
    intro k _hk
    have hnext :
        X (k + 1) =
          c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k := by
      exact
        Complex.rightSemicircleStaircasePrevSafeRe_succ_add_re c ρ m k
    have habs :
        (∫ t : ℝ in X k..
            (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k),
            F k t) =
          Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k :=
      (Complex.rightSemicircleStaircaseHorizontalIntegral_eq_absolute
        f c ρ m k).symm
    exact
      Eq.subst
        (motive := fun b : ℝ =>
          (∫ t : ℝ in X k..b, F k t) =
            Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k)
        (Eq.symm hnext)
        habs
  have htop :
      (∫ t : ℝ in X (m + 1)..X 0, F (m + 1) t) =
        Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m := by
    have hzero :
        X 0 = c.re := by
      exact Complex.rightSemicircleStaircasePrevSafeRe_zero_add_re c ρ m
    have hnext :
        X (m + 1) =
          c.re + Complex.rightSemicircleStaircaseSafeRe ρ m m := by
      exact
        Complex.rightSemicircleStaircasePrevSafeRe_succ_add_re c ρ m m
    have habs :
        (∫ t : ℝ in
            (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m m)..c.re,
            F (m + 1) t) =
          Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m :=
      Eq.subst
        (motive := fun G : ℝ → ℂ =>
          (∫ t : ℝ in
            (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m m)..c.re,
            G t) =
          Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m)
        (Eq.symm hFtop)
        ((Complex.rightSemicircleStaircaseTopConnectorIntegral_eq_absolute
          f c ρ m).symm)
    exact
      Eq.subst
        (motive := fun a : ℝ =>
          (∫ t : ℝ in a..X 0, F (m + 1) t) =
            Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m)
        (Eq.symm hnext)
        (Eq.subst
          (motive := fun b : ℝ =>
            (∫ t : ℝ in
              (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m m)..b,
              F (m + 1) t) =
            Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m)
          (Eq.symm hzero)
          habs)
  have hFbottom :
      F 0 =
        fun x : ℝ =>
          f ((x : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) :=
    Complex.rightSemicircleStaircaseHorizontalTailIntegrand_zero f c ρ m
  have hXzero :
      X 0 = c.re := by
    exact Complex.rightSemicircleStaircasePrevSafeRe_zero_add_re c ρ m
  have hleft :
      (∑ k in Finset.range (m + 1),
          ((∫ x : ℝ in
              (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
              f ((x : ℂ) +
                Complex.I *
                  (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))) -
            (∫ x : ℝ in
              (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
              f ((x : ℂ) +
                Complex.I *
                  (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ)))))) =
        ∑ k in Finset.range (m + 1),
          ((∫ t : ℝ in X (k + 1)..B, F k t) -
            (∫ t : ℝ in X (k + 1)..B, F (k + 1) t)) := by
    apply Finset.sum_congr rfl
    intro k _hk
    have hnext :
        X (k + 1) =
          c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k := by
      show
        c.re + Complex.rightSemicircleStaircasePrevSafeRe ρ m (k + 1) =
          c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k
      exact
        congrArg
          (fun x : ℝ => c.re + x)
          (Complex.rightSemicircleStaircasePrevSafeRe_succ ρ m k)
    exact
      Eq.symm
        (congrArg₂
          (fun A B : ℂ => A - B)
          (Eq.subst
            (motive := fun a : ℝ =>
              (∫ t : ℝ in a..B, F k t) =
                ∫ x : ℝ in
                  (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
                  f ((x : ℂ) +
                    Complex.I *
                      (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))
            )
            (Eq.symm hnext)
            rfl)
          (Eq.subst
            (motive := fun a : ℝ =>
              (∫ t : ℝ in a..B, F (k + 1) t) =
                ∫ x : ℝ in
                  (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
                  f ((x : ℂ) +
                    Complex.I *
                      (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ)))
            )
            (Eq.symm hnext)
            rfl))
  have hbottom_outer :
      (∫ t : ℝ in (X 0)..B, F 0 t) =
        ∫ x : ℝ in c.re..(c.re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) := by
    exact
      Eq.subst
        (motive := fun a : ℝ =>
          (∫ t : ℝ in a..B, F 0 t) =
            ∫ x : ℝ in c.re..(c.re + ρ),
              f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
        (Eq.symm hXzero)
        (Eq.subst
          (motive := fun G : ℝ → ℂ =>
            (∫ t : ℝ in c.re..B, G t) =
              ∫ x : ℝ in c.re..(c.re + ρ),
                f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
          (Eq.symm hFbottom)
          rfl)
  have htop_outer :
      (∫ t : ℝ in (X 0)..B, F (m + 1) t) =
        ∫ x : ℝ in c.re..(c.re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) := by
    exact
      Eq.subst
        (motive := fun a : ℝ =>
          (∫ t : ℝ in a..B, F (m + 1) t) =
            ∫ x : ℝ in c.re..(c.re + ρ),
              f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
        (Eq.symm hXzero)
        (Eq.subst
          (motive := fun G : ℝ → ℂ =>
            (∫ t : ℝ in c.re..B, G t) =
              ∫ x : ℝ in c.re..(c.re + ρ),
                f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
          (Eq.symm hFtop)
          rfl)
  have hright :
      (∫ t : ℝ in (X 0)..B, F 0 t) -
        (∫ t : ℝ in (X 0)..B, F (m + 1) t) -
          (∑ k in Finset.range (m + 1),
            ∫ t : ℝ in X k..X (k + 1), F k t) -
          (∫ t : ℝ in X (m + 1)..X 0, F (m + 1) t) =
      (∫ x : ℝ in c.re..(c.re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) -
        (∫ x : ℝ in c.re..(c.re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) -
        (∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) -
        Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m := by
    exact
      congrArg₂
        (fun A B : ℂ => A - B)
        (congrArg₂
          (fun A B : ℂ => A - B)
          (congrArg₂
            (fun A B : ℂ => A - B)
            hbottom_outer
            htop_outer)
          hconnectors)
        htop
  exact
    Eq.trans hleft
      (Eq.trans htail_tel hright)

end

end LFunctions
end Boundary
