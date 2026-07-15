import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedOutsideEquiv

/-!
# Phase-adapted outside-range packet budget

The outside-range packet sum is reindexed through the exact tail-sum
equivalence and split into far-negative and positive series.  Their proved
phase-adapted tail bounds yield the replacement outside-range budget.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Interval

theorem Complex.norm_logarithmicPhaseEnhancedPositiveModePacket_le_closedMajorant
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : Complex.logarithmicPhasePoissonPositiveTailModes) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
      Complex.logarithmicPhaseAdaptedClosedMajorant t a b
        (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m) := by
  have hleftRight :
      Complex.logarithmicPhaseQuantitativeSupportLeft a ≤
        Complex.logarithmicPhaseQuantitativeSupportRight b :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab
  have hgap :
      0 < Complex.logarithmicPhaseEnhancedPositiveModeGap t b m :=
    Complex.logarithmicPhaseEnhancedPositiveModeGap_pos
      t a b m ha hab m.property
  have hlower : ∀ x ∈
      [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]],
      Complex.logarithmicPhaseEnhancedPositiveModeGap t b m ≤
        ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖ :=
    fun x hx =>
      have hxIcc : x ∈ Set.Icc
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)
          (Complex.logarithmicPhaseQuantitativeSupportRight b) :=
        Eq.mp
          (congrArg (fun support : Set ℝ => x ∈ support)
            (Set.uIcc_of_le hleftRight))
          hx
      have hxPos : 0 < x :=
        Complex.logarithmicPhaseQuantitativeSupport_mem_positive
          a b ha hab hx
      have hdivision :
          ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b ≤
            ‖t‖ / x :=
        Real.div_antitone_on_pos (norm_nonneg t) hxPos hxIcc.2
      have hadd :
          ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b +
              Complex.logarithmicPhasePositiveModeGap m ≤
            ‖t‖ / x + Complex.logarithmicPhasePositiveModeGap m :=
        add_le_add_right hdivision
          (Complex.logarithmicPhasePositiveModeGap m)
      have habs :=
        Complex.abs_logarithmicPhasePositiveModeDerivative
          t x m hxPos (le_of_lt m.property)
      le_trans hadd (le_of_eq habs.symm)
  exact Complex.norm_logarithmicPhaseAdaptedPacket_le_closedMajorant
    t a b m
    (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m)
    ha hab hgap hlower

theorem Complex.logarithmicPhaseEnhancedPositiveClosedMajorant_le_integerEnvelope
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : Complex.logarithmicPhasePoissonPositiveTailModes) :
    Complex.logarithmicPhaseAdaptedClosedMajorant t a b
        (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m) ≤
      Complex.logarithmicPhasePositiveModeIntegerEnvelope t a b m := by
  have hright :
      0 < Complex.logarithmicPhaseQuantitativeSupportRight b :=
    Complex.logarithmicPhaseQuantitativeSupportRight_pos a b ha hab
  have hquotient :
      0 ≤ ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b :=
    div_nonneg (norm_nonneg t) hright.le
  have hgapOrder :
      Complex.logarithmicPhasePositiveModeGap m ≤
        Complex.logarithmicPhaseEnhancedPositiveModeGap t b m := by
    have hzeroAdd :
        (0 : ℝ) + Complex.logarithmicPhasePositiveModeGap m =
          Complex.logarithmicPhasePositiveModeGap m :=
      zero_add _
    exact le_trans (le_of_eq hzeroAdd.symm)
      (add_le_add_right hquotient
        (Complex.logarithmicPhasePositiveModeGap m))
  have hleft :
      0 ≤ Complex.logarithmicPhaseQuantitativeSupportLeft a :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have hbaseGap : 0 < Complex.logarithmicPhasePositiveModeGap m :=
    Complex.logarithmicPhasePositiveModeGap_pos m m.property
  have hcoarse :
      Complex.logarithmicPhaseAdaptedClosedMajorant t a b
          (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m) ≤
        Complex.logarithmicPhasePositiveModeClosedMajorant t a b m :=
    Complex.logarithmicPhaseAdaptedClosedMajorant_gap_antitone
      t a b hab hleft hbaseGap hgapOrder
  have henvelope :
      Complex.logarithmicPhasePositiveModeClosedMajorant t a b m ≤
        Complex.logarithmicPhasePositiveModeInverseSquareEnvelope t a b m :=
    Complex.logarithmicPhasePositiveModeClosedMajorant_le_envelope
      t a b m hab hleft m.property
  have hnormalize :
      Complex.logarithmicPhasePositiveModeInverseSquareEnvelope t a b m =
        Complex.logarithmicPhasePositiveModeIntegerEnvelope t a b m :=
    Complex.logarithmicPhasePositiveModeEnvelope_eq_integerEnvelope
      t a b m m.property
  exact le_trans hcoarse
    (le_trans henvelope (le_of_eq hnormalize))

theorem Complex.summable_logarithmicPhaseEnhancedPositiveClosedMajorant
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Summable (fun m : Complex.logarithmicPhasePoissonPositiveTailModes =>
      Complex.logarithmicPhaseAdaptedClosedMajorant t a b
        (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m)) := by
  have hleft :
      0 ≤ Complex.logarithmicPhaseQuantitativeSupportLeft a :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have hmajorant :
      Summable (fun m : Complex.logarithmicPhasePoissonPositiveTailModes =>
        Complex.logarithmicPhasePositiveModeIntegerEnvelope t a b m) :=
    Complex.summable_logarithmicPhaseAdaptedPositiveTailEnvelope t a b
  exact Summable.of_nonneg_of_le
    (fun m =>
      Complex.logarithmicPhaseAdaptedClosedMajorant_nonneg
        t a b
        (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m)
        hab hleft
        (Complex.logarithmicPhaseEnhancedPositiveModeGap_pos
          t a b m ha hab m.property).le)
    (fun m =>
      Complex.logarithmicPhaseEnhancedPositiveClosedMajorant_le_integerEnvelope
        t a b ha hab m)
    hmajorant

theorem Complex.norm_logarithmicPhaseEnhancedPositivePacket_tsum_le_budget
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
      Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b := by
  have hsummable :
      Summable (fun m : Complex.logarithmicPhasePoissonPositiveTailModes =>
        Complex.logarithmicPhaseAdaptedClosedMajorant t a b
          (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m)) :=
    Complex.summable_logarithmicPhaseEnhancedPositiveClosedMajorant
      t a b ha hab
  have hpointwise :
      ∀ m : Complex.logarithmicPhasePoissonPositiveTailModes,
        ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
          Complex.logarithmicPhaseAdaptedClosedMajorant t a b
            (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m) :=
    fun m =>
      Complex.norm_logarithmicPhaseEnhancedPositiveModePacket_le_closedMajorant
        t a b ha hab m
  have hbound :
      ‖∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
        ∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
          Complex.logarithmicPhaseAdaptedClosedMajorant t a b
            (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m) :=
    tsum_norm_le hsummable hpointwise
  have hbudget :
      (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
        Complex.logarithmicPhaseAdaptedClosedMajorant t a b
          (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m)) =
        Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b :=
    rfl
  exact le_trans hbound (le_of_eq hbudget)

def Complex.logarithmicPhaseTailSumPacket
    (t : ℝ) (a b : ℤ) :
    Sum
      (Complex.logarithmicPhasePoissonFarNegativeModes t a)
      Complex.logarithmicPhasePoissonPositiveTailModes → ℂ
  | Sum.inl m =>
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m
  | Sum.inr m =>
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m

def Complex.logarithmicPhaseTailSigmaIndex
    (t : ℝ) (a : ℤ) : Type :=
  Σ side : Bool,
    side.casesOn
      (Complex.logarithmicPhasePoissonFarNegativeModes t a)
      Complex.logarithmicPhasePoissonPositiveTailModes

def Complex.logarithmicPhaseTailSumEquivSigma
    (t : ℝ) (a : ℤ) :
    Sum
      (Complex.logarithmicPhasePoissonFarNegativeModes t a)
      Complex.logarithmicPhasePoissonPositiveTailModes ≃
      Complex.logarithmicPhaseTailSigmaIndex t a :=
  Equiv.sumEquivSigmaBool
    (Complex.logarithmicPhasePoissonFarNegativeModes t a)
    Complex.logarithmicPhasePoissonPositiveTailModes

def Complex.logarithmicPhaseTailSigmaPacket
    (t : ℝ) (a b : ℤ)
    (m : Complex.logarithmicPhaseTailSigmaIndex t a) : ℂ :=
  Complex.logarithmicPhaseTailSumPacket t a b
    ((Complex.logarithmicPhaseTailSumEquivSigma t a).symm m)

theorem Complex.logarithmicPhaseTailSumPacket_comp_outsideEquiv
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a)
    (m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a}) :
    Complex.logarithmicPhaseTailSumPacket t a b
        (Complex.logarithmicPhaseOutsideEquivTailSum t a ha m) =
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m := by
  change Complex.logarithmicPhaseTailSumPacket t a b
      (Complex.logarithmicPhaseOutsideToTailSum t a m) =
    Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m
  have hvalue := Complex.logarithmicPhaseOutsideToTailSum_value t a m
  match hselected : Complex.logarithmicPhaseOutsideToTailSum t a m with
  | Sum.inl n =>
      have hn : (n : ℤ) = (m : ℤ) :=
        Eq.trans
          (congrArg
            (Sum.elim
              (fun value : Complex.logarithmicPhasePoissonFarNegativeModes t a =>
                (value : ℤ))
              (fun value : Complex.logarithmicPhasePoissonPositiveTailModes =>
                (value : ℤ)))
            hselected.symm)
          hvalue
      exact congrArg
        (fun mode : ℤ =>
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b mode)
        hn
  | Sum.inr n =>
      have hn : (n : ℤ) = (m : ℤ) :=
        Eq.trans
          (congrArg
            (Sum.elim
              (fun value : Complex.logarithmicPhasePoissonFarNegativeModes t a =>
                (value : ℤ))
              (fun value : Complex.logarithmicPhasePoissonPositiveTailModes =>
                (value : ℤ)))
            hselected.symm)
          hvalue
      exact congrArg
        (fun mode : ℤ =>
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b mode)
        hn

theorem Complex.logarithmicPhaseTailSigmaPacket_comp_tailSumEquiv
    (t : ℝ) (a b : ℤ)
    (m : Sum
      (Complex.logarithmicPhasePoissonFarNegativeModes t a)
      Complex.logarithmicPhasePoissonPositiveTailModes) :
    Complex.logarithmicPhaseTailSigmaPacket t a b
        (Complex.logarithmicPhaseTailSumEquivSigma t a m) =
      Complex.logarithmicPhaseTailSumPacket t a b m := by
  exact congrArg
    (Complex.logarithmicPhaseTailSumPacket t a b)
    ((Complex.logarithmicPhaseTailSumEquivSigma t a).symm_apply_apply m)

theorem Complex.logarithmicPhaseTailSigmaPacket_false
    (t : ℝ) (a b : ℤ)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    Complex.logarithmicPhaseTailSigmaPacket t a b ⟨false, m⟩ =
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m := by
  exact rfl

theorem Complex.logarithmicPhaseTailSigmaPacket_true
    (t : ℝ) (a b : ℤ)
    (m : Complex.logarithmicPhasePoissonPositiveTailModes) :
    Complex.logarithmicPhaseTailSigmaPacket t a b ⟨true, m⟩ =
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m := by
  exact rfl

theorem Complex.logarithmicPhaseOutsidePacket_tsum_eq_tailSum_tsum
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) :
    (∑' m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) =
    ∑' m : Sum
      (Complex.logarithmicPhasePoissonFarNegativeModes t a)
      Complex.logarithmicPhasePoissonPositiveTailModes,
      Complex.logarithmicPhaseTailSumPacket t a b m := by
  let e := Complex.logarithmicPhaseOutsideEquivTailSum t a ha
  have hreindex := e.tsum_eq (Complex.logarithmicPhaseTailSumPacket t a b)
  have hleft := tsum_congr
    (fun m =>
      Complex.logarithmicPhaseTailSumPacket_comp_outsideEquiv
        t a b ha m)
  exact Eq.trans hleft.symm hreindex

theorem Complex.summable_logarithmicPhaseTailSumPacket
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) :
    Summable (Complex.logarithmicPhaseTailSumPacket t a b) := by
  let e := Complex.logarithmicPhaseOutsideEquivTailSum t a ha
  have hall :=
    Complex.summable_logarithmicPhaseQuantitativeBlockFourierPacket
      ‖t‖ a b ha
  have houtside :
      Summable
        (fun m : {m : ℤ //
            m ∉ Complex.logarithmicPhasePoissonModeRange t a} =>
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) :=
    hall.subtype
      {m : ℤ | m ∉ Complex.logarithmicPhasePoissonModeRange t a}
  have hfunction :
      Complex.logarithmicPhaseTailSumPacket t a b ∘ e =
        (fun m : {m : ℤ //
            m ∉ Complex.logarithmicPhasePoissonModeRange t a} =>
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) :=
    funext (fun m =>
      Complex.logarithmicPhaseTailSumPacket_comp_outsideEquiv
        t a b ha m)
  have hcomp :
      Summable (Complex.logarithmicPhaseTailSumPacket t a b ∘ e) :=
    Eq.subst
      (motive := fun function :
          {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a} → ℂ =>
        Summable function)
      hfunction.symm
      houtside
  exact e.summable_iff.mp hcomp

theorem Complex.summable_logarithmicPhaseTailSigmaPacket
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) :
    Summable (Complex.logarithmicPhaseTailSigmaPacket t a b) := by
  exact
    (Complex.logarithmicPhaseTailSumEquivSigma t a).symm.summable_iff.mpr
      (Complex.summable_logarithmicPhaseTailSumPacket t a b ha)

theorem Complex.logarithmicPhaseTailSumPacket_tsum_eq_sigma_tsum
    (t : ℝ) (a b : ℤ) :
    (∑' m : Sum
      (Complex.logarithmicPhasePoissonFarNegativeModes t a)
      Complex.logarithmicPhasePoissonPositiveTailModes,
      Complex.logarithmicPhaseTailSumPacket t a b m) =
      ∑' m : Complex.logarithmicPhaseTailSigmaIndex t a,
        Complex.logarithmicPhaseTailSigmaPacket t a b m := by
  let e := Complex.logarithmicPhaseTailSumEquivSigma t a
  have hreindex :=
    e.tsum_eq (Complex.logarithmicPhaseTailSigmaPacket t a b)
  have hsource := tsum_congr
    (fun m =>
      Complex.logarithmicPhaseTailSigmaPacket_comp_tailSumEquiv
        t a b m)
  exact Eq.trans hsource.symm hreindex

theorem Complex.logarithmicPhaseTailSigmaPacket_tsum_eq_add
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) :
    (∑' m : Complex.logarithmicPhaseTailSigmaIndex t a,
      Complex.logarithmicPhaseTailSigmaPacket t a b m) =
      (∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) +
      (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) := by
  have hsummable :=
    Complex.summable_logarithmicPhaseTailSigmaPacket t a b ha
  have hdecompose :
      (∑' m : Complex.logarithmicPhaseTailSigmaIndex t a,
        Complex.logarithmicPhaseTailSigmaPacket t a b m) =
        ∑' side : Bool,
          ∑' m : side.casesOn
              (Complex.logarithmicPhasePoissonFarNegativeModes t a)
              Complex.logarithmicPhasePoissonPositiveTailModes,
            Complex.logarithmicPhaseTailSigmaPacket t a b ⟨side, m⟩ :=
    tsum_sigma hsummable
  have hbool :
      (∑' side : Bool,
        ∑' m : side.casesOn
            (Complex.logarithmicPhasePoissonFarNegativeModes t a)
            Complex.logarithmicPhasePoissonPositiveTailModes,
          Complex.logarithmicPhaseTailSigmaPacket t a b ⟨side, m⟩) =
        (∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
          Complex.logarithmicPhaseTailSigmaPacket t a b ⟨false, m⟩) +
        (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
          Complex.logarithmicPhaseTailSigmaPacket t a b ⟨true, m⟩) :=
    tsum_bool _
  have hnegative :
      (∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
        Complex.logarithmicPhaseTailSigmaPacket t a b ⟨false, m⟩) =
        ∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m :=
    tsum_congr (fun m =>
      Complex.logarithmicPhaseTailSigmaPacket_false t a b m)
  have hpositive :
      (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
        Complex.logarithmicPhaseTailSigmaPacket t a b ⟨true, m⟩) =
        ∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m :=
    tsum_congr (fun m =>
      Complex.logarithmicPhaseTailSigmaPacket_true t a b m)
  have hnormalize := congrArg₂
    (fun negative positive : ℂ => negative + positive)
    hnegative hpositive
  exact Eq.trans hdecompose (Eq.trans hbool hnormalize)

theorem Complex.logarithmicPhaseTailSumPacket_tsum_eq_add
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) :
    (∑' m : Sum
      (Complex.logarithmicPhasePoissonFarNegativeModes t a)
      Complex.logarithmicPhasePoissonPositiveTailModes,
      Complex.logarithmicPhaseTailSumPacket t a b m) =
      (∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) +
      (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) := by
  exact Eq.trans
    (Complex.logarithmicPhaseTailSumPacket_tsum_eq_sigma_tsum t a b)
    (Complex.logarithmicPhaseTailSigmaPacket_tsum_eq_add t a b ha)

theorem Complex.logarithmicPhaseOutsidePacket_tsum_eq_farNegative_add_positive
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) :
    (∑' m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) =
      (∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) +
      (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) := by
  exact Eq.trans
    (Complex.logarithmicPhaseOutsidePacket_tsum_eq_tailSum_tsum t a b ha)
    (Complex.logarithmicPhaseTailSumPacket_tsum_eq_add t a b ha)

theorem Complex.norm_logarithmicPhaseOutsidePacket_tsum_le_adaptedBudget
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
      Complex.logarithmicPhaseAdaptedOutsideRangeBudget t a b := by
  have hsplit :=
    Complex.logarithmicPhaseOutsidePacket_tsum_eq_farNegative_add_positive
      t a b ha
  have htriangle := norm_add_le
    (∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m)
    (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m)
  have hnegative :=
    Complex.norm_logarithmicPhaseEnhancedFarNegativeTail_tsum_le
      t a b ha hab
  have hpositive :=
    Complex.norm_logarithmicPhaseEnhancedPositivePacket_tsum_le_budget
      t a b ha hab
  unfold Complex.logarithmicPhaseAdaptedOutsideRangeBudget
  exact le_trans (le_of_eq (congrArg norm hsplit))
    (le_trans htriangle (add_le_add hnegative hpositive))

end
end LFunctions
end Boundary
