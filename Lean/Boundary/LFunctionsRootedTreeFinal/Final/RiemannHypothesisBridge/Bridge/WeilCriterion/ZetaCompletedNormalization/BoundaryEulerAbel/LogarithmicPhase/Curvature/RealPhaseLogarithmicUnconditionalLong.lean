import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicEightyClosure

/-!
# Unconditional logarithmic long branch

This owner is the public analytic endpoint of the quantitative Poisson packet
library.  Exact Poisson reconstruction identifies the real-phase block with
the packet total; the sharp packet budget bounds that total; exact arithmetic
bounds the budget by eighty refined-scale units.  The theorem accepts only the
intrinsic long dyadic geometry and has no packet-family, tail, radicand, or
stationary-window arguments.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

theorem Complex.logarithmicPhaseRealPhase_block_eq_quantitativePacket_tsum
    (t : ℝ) (a b : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))) =
      ∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket
          t (a : ℤ) (b : ℤ) m := by
  have haInt : (1 : ℤ) ≤ (a : ℤ) := Int.ofNat_le.mpr ha
  have habInt : (a : ℤ) ≤ (b : ℤ) := Int.ofNat_le.mpr hab
  have hsumCast :
      (∑ n ∈ Finset.Icc a b,
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                t (n : ℝ) : ℂ))) =
        ∑ n ∈ Finset.Icc (a : ℤ) (b : ℤ),
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                t (n : ℝ) : ℂ)) := by
    exact Finset.sum_bij
      (fun n hn => (n : ℤ))
      (fun n hn => Finset.mem_Icc.mpr
        ⟨Int.ofNat_le.mpr (Finset.mem_Icc.mp hn).1,
          Int.ofNat_le.mpr (Finset.mem_Icc.mp hn).2⟩)
      (fun n₁ hn₁ n₂ hn₂ heq => Int.ofNat_inj.mp heq)
      (fun n hn => by
        have hna : (a : ℤ) ≤ n := (Finset.mem_Icc.mp hn).1
        have hnb : n ≤ (b : ℤ) := (Finset.mem_Icc.mp hn).2
        have hnLower : (0 : ℤ) ≤ n :=
          le_trans (Int.ofNat_zero_le a) hna
        have hnatLower :=
          Int.toNat_le_toNat hna
        have hnatUpper :=
          Int.toNat_le_toNat hnb
        exact ⟨n.toNat,
          Finset.mem_Icc.mpr
            ⟨Eq.subst (motive := fun value : ℕ => value ≤ n.toNat)
                (Int.toNat_natCast a) hnatLower,
              Eq.subst (motive := fun value : ℕ => n.toNat ≤ value)
                (Int.toNat_natCast b).symm hnatUpper⟩,
          Int.toNat_of_nonneg hnLower⟩)
      (fun n hn => by
        have hcast : ((n : ℤ) : ℝ) = (n : ℝ) := rfl
        exact congrArg
          (fun value : ℝ =>
            Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                  t value : ℂ))) hcast.symm)
  exact Eq.trans hsumCast
    (Complex.logarithmicPhase_quantitativeBlock_poisson_packet_reconstruction
      t (a : ℤ) (b : ℤ) haInt habInt)

theorem Complex.logarithmicPhaseRealPhase_block_norm_eq_quantitativePacket_tsum_norm
    (t : ℝ) (a b : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ =
      ‖∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket
          t (a : ℤ) (b : ℤ) m‖ :=
  congrArg norm
    (Complex.logarithmicPhaseRealPhase_block_eq_quantitativePacket_tsum
      t a b ha hab)

theorem Complex.logarithmicPhaseRealPhase_block_norm_eq_adaptedQuantitativePacket_tsum_norm_of_nonneg
    (t : ℝ) (ht_nonneg : 0 ≤ t) (a b : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ =
      ‖∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket
          ‖t‖ (a : ℤ) (b : ℤ) m‖ := by
  have hraw :=
    Complex.logarithmicPhaseRealPhase_block_norm_eq_quantitativePacket_tsum_norm
      t a b ha hab
  have hparameter : t = ‖t‖ :=
    (Real.norm_of_nonneg ht_nonneg).symm
  have hadapted :
      ‖∑' m : ℤ,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket
            t (a : ℤ) (b : ℤ) m‖ =
        ‖∑' m : ℤ,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket
            ‖t‖ (a : ℤ) (b : ℤ) m‖ :=
    congrArg
      (fun parameter : ℝ =>
        ‖∑' m : ℤ,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket
            parameter (a : ℤ) (b : ℤ) m‖)
      hparameter
  exact Eq.trans hraw hadapted

theorem Complex.logarithmicPhaseRealPhase_block_norm_le_sharpBProcessBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      Complex.logarithmicPhaseSharpBProcessBudget
        t (a : ℤ) (b : ℤ) := by
  have ha := Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry
  have hab := Real.logarithmicPhaseLongBranchGeometry_order hgeometry
  have hparameter : t = ‖t‖ :=
    (Real.norm_of_nonneg ht_nonneg).symm
  have hnorm_norm : ‖‖t‖‖ = ‖t‖ :=
    Real.norm_of_nonneg (norm_nonneg t)
  have ht_adapted : 1 ≤ ‖‖t‖‖ :=
    Eq.subst
      (motive := fun value : ℝ => 1 ≤ value)
      hnorm_norm.symm
      ht
  have hgeometry_adapted :
      Real.logarithmicPhaseLongBranchGeometry ‖t‖ a b :=
    Eq.subst
      (motive := fun parameter : ℝ =>
        Real.logarithmicPhaseLongBranchGeometry parameter a b)
      hparameter
      hgeometry
  have hreconstruction :=
    Complex.logarithmicPhaseRealPhase_block_norm_eq_adaptedQuantitativePacket_tsum_norm_of_nonneg
      t ht_nonneg a b ha hab
  have hpacket :=
    Complex.norm_logarithmicPhaseQuantitativePacket_tsum_le_sharpBProcessBudget
      ‖t‖ ht_adapted (norm_nonneg t) a b hgeometry_adapted
  have hbudget_parameter :
      Complex.logarithmicPhaseSharpBProcessBudget
          ‖t‖ (a : ℤ) (b : ℤ) =
        Complex.logarithmicPhaseSharpBProcessBudget
          t (a : ℤ) (b : ℤ) :=
    congrArg
      (fun parameter : ℝ =>
        Complex.logarithmicPhaseSharpBProcessBudget
          parameter (a : ℤ) (b : ℤ))
      (Real.norm_of_nonneg ht_nonneg)
  have hpacket_at_t :
      ‖∑' m : ℤ,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket
            ‖t‖ (a : ℤ) (b : ℤ) m‖ ≤
        Complex.logarithmicPhaseSharpBProcessBudget
          t (a : ℤ) (b : ℤ) :=
    Eq.subst
      (motive := fun budget : ℝ =>
        ‖∑' m : ℤ,
            Complex.logarithmicPhaseQuantitativeBlockFourierPacket
              ‖t‖ (a : ℤ) (b : ℤ) m‖ ≤ budget)
      hbudget_parameter
      hpacket
  exact Eq.subst
    (motive := fun value : ℝ =>
      value ≤ Complex.logarithmicPhaseSharpBProcessBudget
        t (a : ℤ) (b : ℤ))
    hreconstruction.symm hpacket_at_t

theorem Complex.logarithmicPhaseRealPhase_long_nonneg_unconditional_refined
    (t : ℝ) (ht_nonneg : 0 ≤ t) (ht : 1 ≤ ‖t‖)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      80 * Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  have hpacket :=
    Complex.logarithmicPhaseRealPhase_block_norm_le_sharpBProcessBudget
      t ht ht_nonneg a b hgeometry
  have hparameter : t = ‖t‖ :=
    (Real.norm_of_nonneg ht_nonneg).symm
  have hnorm_norm : ‖‖t‖‖ = ‖t‖ :=
    Real.norm_of_nonneg (norm_nonneg t)
  have ht_adapted : 1 ≤ ‖‖t‖‖ :=
    Eq.subst
      (motive := fun value : ℝ => 1 ≤ value)
      hnorm_norm.symm
      ht
  have hgeometry_adapted :
      Real.logarithmicPhaseLongBranchGeometry ‖t‖ a b :=
    Eq.subst
      (motive := fun parameter : ℝ =>
        Real.logarithmicPhaseLongBranchGeometry parameter a b)
      hparameter
      hgeometry
  have harithmetic_adapted :=
    Complex.logarithmicPhaseSharpBProcessBudget_le_eighty_refined
      ‖t‖ ht_adapted (norm_nonneg t) a b hgeometry_adapted
  have hbudget_parameter :
      Complex.logarithmicPhaseSharpBProcessBudget
          ‖t‖ (a : ℤ) (b : ℤ) =
        Complex.logarithmicPhaseSharpBProcessBudget
          t (a : ℤ) (b : ℤ) :=
    congrArg
      (fun parameter : ℝ =>
        Complex.logarithmicPhaseSharpBProcessBudget
          parameter (a : ℤ) (b : ℤ))
      (Real.norm_of_nonneg ht_nonneg)
  have hrefined_parameter :
      Real.logarithmicPhaseRefinedScale ‖t‖ (b : ℤ) =
        Real.logarithmicPhaseRefinedScale t (b : ℤ) :=
    congrArg
      (fun parameter : ℝ =>
        Real.logarithmicPhaseRefinedScale parameter (b : ℤ))
      (Real.norm_of_nonneg ht_nonneg)
  have harithmetic_target :
      Complex.logarithmicPhaseSharpBProcessBudget
          ‖t‖ (a : ℤ) (b : ℤ) ≤
        80 * Real.logarithmicPhaseRefinedScale t (b : ℤ) :=
    Eq.subst
      (motive := fun scale : ℝ =>
        Complex.logarithmicPhaseSharpBProcessBudget
            ‖t‖ (a : ℤ) (b : ℤ) ≤
          80 * scale)
      hrefined_parameter
      harithmetic_adapted
  have harithmetic :
      Complex.logarithmicPhaseSharpBProcessBudget
          t (a : ℤ) (b : ℤ) ≤
        80 * Real.logarithmicPhaseRefinedScale t (b : ℤ) :=
    Eq.subst
      (motive := fun budget : ℝ =>
        budget ≤ 80 * Real.logarithmicPhaseRefinedScale t (b : ℤ))
      hbudget_parameter
      harithmetic_target
  exact le_trans hpacket harithmetic

theorem Real.logarithmicPhaseRefinedScale_nat_eq_target
    (t : ℝ) (b : ℕ) :
    Real.logarithmicPhaseRefinedScale t (b : ℤ) =
      (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) := by
  unfold Real.logarithmicPhaseRefinedScale
  have hInt : ((b : ℤ) : ℝ) = (b : ℝ) := rfl
  have hSucc : (((b + 1 : ℕ) : ℝ)) = (b : ℝ) + 1 := by
    exact Eq.trans (Nat.cast_add b 1)
      (congrArg (fun value : ℝ => (b : ℝ) + value) Nat.cast_one)
  have hNumerator : ((b : ℤ) : ℝ) + 1 = (((b + 1 : ℕ) : ℝ)) :=
    Eq.trans (congrArg (fun value : ℝ => value + 1) hInt) hSucc.symm
  exact congrArg₂ (fun numerator root : ℝ => numerator / ‖t‖ + root)
    hNumerator rfl

theorem Complex.logarithmicPhaseRealPhase_long_nonneg_unconditional
    (t : ℝ) (ht_nonneg : 0 ≤ t) (ht : 1 ≤ ‖t‖)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖) +
        Real.sqrt (1 + ‖t‖)) := by
  have hrefined :=
    Complex.logarithmicPhaseRealPhase_long_nonneg_unconditional_refined
      t ht_nonneg ht a b hgeometry
  exact Eq.subst
    (motive := fun value : ℝ => _ ≤ 80 * value)
    (Real.logarithmicPhaseRefinedScale_nat_eq_target t b)
    hrefined

theorem Real.logarithmicPhaseLongBranchGeometry_mk
    (t : ℝ) (a b : ℕ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hstrict : a < b)
    (hsqrt : Real.sqrt (1 + ‖t‖) <
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hendpoint : (((b + 1 : ℕ) : ℝ) / ‖t‖) <
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hcomparable : b + 1 ≤ 2 * a) :
    Real.logarithmicPhaseLongBranchGeometry t a b := by
  exact Real.logarithmicPhaseLongBranchGeometry_of_endpoint_hypotheses
    ha hab hstrict hsqrt hendpoint hcomparable

theorem Complex.logarithmicPhaseRealPhase_long_nonneg_unconditional_of_explicit_geometry
    (t : ℝ) (ht_nonneg : 0 ≤ t) (ht : 1 ≤ ‖t‖)
    (a b : ℕ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hstrict : a < b)
    (hsqrt : Real.sqrt (1 + ‖t‖) <
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hendpoint : (((b + 1 : ℕ) : ℝ) / ‖t‖) <
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hcomparable : b + 1 ≤ 2 * a) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖) +
        Real.sqrt (1 + ‖t‖)) := by
  have hgeometry := Real.logarithmicPhaseLongBranchGeometry_mk
    t a b ha hab hstrict hsqrt hendpoint hcomparable
  exact Complex.logarithmicPhaseRealPhase_long_nonneg_unconditional
    t ht_nonneg ht a b hgeometry

end

end LFunctions
end Boundary
