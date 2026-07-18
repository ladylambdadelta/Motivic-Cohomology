import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.FiniteTomographyParts.QuantitativeSeparation.SeedDaggerProductNorm
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.Owner

/-!
# Affine kernel approximation and seed-dagger control

Adding a finite-evaluation kernel probe to the seed preserves its
autocorrelation fiber.  Small completed-zero coordinates outside the forced
finite set then give a small seed/dagger product tail.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction
namespace QuantitativeSeparation

theorem daggerReflection_not_mem_of_not_mem_daggerClosed
    (P : Finset ℂ)
    (z : ℂ)
    (hz : z ∉ daggerClosedSpectralSampleFinset P) :
    -star z ∉ daggerClosedSpectralSampleFinset P := by
  intro hreflected
  have hdouble : -star (-star z) ∈ daggerClosedSpectralSampleFinset P :=
    mem_daggerClosedSpectralSampleFinset_reflection_of_mem P (-star z) hreflected
  exact hz
    (Eq.mp
      (congrArg
        (fun value : ℂ => value ∈ daggerClosedSpectralSampleFinset P)
        (daggerReflection_involutive z))
      hdouble)

theorem affineKernel_preserves_autocorrelationFiber
    (P : Finset ℂ)
    (f₀ h : ZetaAdmissibleFunction)
    (hkernel :
      ∀ z : ℂ,
        z ∈ daggerClosedSpectralSampleFinset P → zetaSpectralEval h z = 0) :
    f₀ + h ∈ AutocorrelationSpectralEvalFiberOf P f₀ := by
  intro z hz
  have hleft : zetaSpectralEval h z = 0 :=
    hkernel z (mem_daggerClosedSpectralSampleFinset_self P z hz)
  have hright : zetaSpectralEval h (-star z) = 0 :=
    hkernel (-star z)
      (mem_daggerClosedSpectralSampleFinset_reflection P z hz)
  have haddLeft :
      zetaSpectralEval (f₀ + h) z = zetaSpectralEval f₀ z :=
    Eq.trans
      (zetaSpectralEval_add f₀ h z)
      (Eq.trans
        (congrArg (fun value : ℂ => zetaSpectralEval f₀ z + value) hleft)
        (add_zero (zetaSpectralEval f₀ z)))
  have haddRight :
      zetaSpectralEval (f₀ + h) (-star z) =
        zetaSpectralEval f₀ (-star z) :=
    Eq.trans
      (zetaSpectralEval_add f₀ h (-star z))
      (Eq.trans
        (congrArg
          (fun value : ℂ => zetaSpectralEval f₀ (-star z) + value)
          hright)
        (add_zero (zetaSpectralEval f₀ (-star z))))
  exact Eq.trans
    (zetaSpectralEval_convolutionAutocorrelation_eq_seed_daggerProduct
      (f₀ + h) z)
    (Eq.trans
      (congrArg₂
        (fun left right : ℂ => left * star right)
        haddLeft
        haddRight)
      (zetaSpectralEval_convolutionAutocorrelation_eq_seed_daggerProduct
        f₀ z).symm)

theorem affineCoordinateComplement_summand_eq
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (P : Finset ℂ)
    (f₀ h : ZetaAdmissibleFunction)
    (rho : ZetaCompletedZeroCoordinate) :
    (if (rho : ℂ) ∈ P then 0
      else
        ‖(-(zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f₀)) rho -
          zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary h rho‖) =
      if (rho : ℂ) ∈ P then 0
      else ‖zetaZeroSideContribution (rho : ℂ) (f₀ + h)‖ := by
  if hmembership : (rho : ℂ) ∈ P then
    exact Eq.trans (if_pos hmembership) (if_pos hmembership).symm
  else
    have hcoordinateAdd :
        zetaZeroSideContribution (rho : ℂ) (f₀ + h) =
          zetaZeroSideContribution (rho : ℂ) f₀ +
            zetaZeroSideContribution (rho : ℂ) h :=
      zetaZeroSideContribution_add (rho : ℂ) f₀ h
    have hnegative :
        -(zetaZeroSideContribution (rho : ℂ) f₀) -
            zetaZeroSideContribution (rho : ℂ) h =
          -(zetaZeroSideContribution (rho : ℂ) (f₀ + h)) :=
      Eq.trans
        (sub_eq_add_neg
          (-(zetaZeroSideContribution (rho : ℂ) f₀))
          (zetaZeroSideContribution (rho : ℂ) h))
        (Eq.trans
          (neg_add
            (zetaZeroSideContribution (rho : ℂ) f₀)
            (zetaZeroSideContribution (rho : ℂ) h)).symm
          (congrArg Neg.neg hcoordinateAdd.symm))
    have hnorm :
        ‖-(zetaZeroSideContribution (rho : ℂ) f₀) -
            zetaZeroSideContribution (rho : ℂ) h‖ =
          ‖zetaZeroSideContribution (rho : ℂ) (f₀ + h)‖ :=
      Eq.trans
        (congrArg norm hnegative)
        (norm_neg (zetaZeroSideContribution (rho : ℂ) (f₀ + h)))
    exact Eq.trans
      (if_neg hmembership)
      (Eq.trans hnorm (if_neg hmembership).symm)

theorem if_zero_else_norm_nonnegative
    (proposition : Prop)
    [Decidable proposition]
    (value : ℂ) :
    0 ≤ if proposition then 0 else ‖value‖ := by
  if hproposition : proposition then
    exact Eq.subst
      (motive := fun result : ℝ => 0 ≤ result)
      (if_pos hproposition).symm
      (le_refl 0)
  else
    exact Eq.subst
      (motive := fun result : ℝ => 0 ≤ result)
      (if_neg hproposition).symm
      (norm_nonneg value)

theorem if_zero_else_norm_le_norm
    (proposition : Prop)
    [Decidable proposition]
    (value : ℂ) :
    (if proposition then 0 else ‖value‖) ≤ ‖value‖ := by
  if hproposition : proposition then
    exact Eq.subst
      (motive := fun result : ℝ => result ≤ ‖value‖)
      (if_pos hproposition).symm
      (norm_nonneg value)
  else
    exact Eq.subst
      (motive := fun result : ℝ => result ≤ ‖value‖)
      (if_neg hproposition).symm
      (le_refl ‖value‖)

theorem affineCoordinateComplementDistance_eq
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (P : Finset ℂ)
    (f₀ h : ZetaAdmissibleFunction) :
    zetaCompletedZeroCoordinateComplementL1Distance P
        (-(zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f₀))
        (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary h) =
      ∑' rho : ZetaCompletedZeroCoordinate,
        if (rho : ℂ) ∈ P then 0
        else ‖zetaZeroSideContribution (rho : ℂ) (f₀ + h)‖ := by
  unfold zetaCompletedZeroCoordinateComplementL1Distance
  exact tsum_congr
    (affineCoordinateComplement_summand_eq
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      P f₀ h)

theorem nonnegative_subtype_product_tsum_le_square
    {index : Type*}
    (coordinate : index → ℝ)
    (predicate : index → Prop)
    (partner : {value : index // predicate value} → index)
    (hcoordinateNonnegative : ∀ value : index, 0 ≤ coordinate value)
    (hcoordinateSummable : Summable coordinate) :
    (∑' value : {value : index // predicate value},
        coordinate (value : index) * coordinate (partner value)) ≤
      (∑' value : index, coordinate value) ^ 2 := by
  let total : ℝ := ∑' value : index, coordinate value
  have hpartnerBound :
      ∀ value : {value : index // predicate value},
        coordinate (partner value) ≤ total :=
    fun value =>
      le_tsum hcoordinateSummable (partner value)
        (fun other _ => hcoordinateNonnegative other)
  have hsubtypeSummable :
      Summable
        (fun value : {value : index // predicate value} =>
          coordinate (value : index)) :=
    hcoordinateSummable.subtype predicate
  have hmajorantSummable :
      Summable
        (fun value : {value : index // predicate value} =>
          coordinate (value : index) * total) :=
    hsubtypeSummable.mul_right total
  have hproductSummable :
      Summable
        (fun value : {value : index // predicate value} =>
          coordinate (value : index) * coordinate (partner value)) :=
    Summable.of_nonneg_of_le
      (fun value =>
        mul_nonneg
          (hcoordinateNonnegative (value : index))
          (hcoordinateNonnegative (partner value)))
      (fun value =>
        mul_le_mul_of_nonneg_left
          (hpartnerBound value)
          (hcoordinateNonnegative (value : index)))
      hmajorantSummable
  have hproductLe :
      (∑' value : {value : index // predicate value},
          coordinate (value : index) * coordinate (partner value)) ≤
        ∑' value : {value : index // predicate value},
          coordinate (value : index) * total :=
    tsum_le_tsum
      (fun value =>
        mul_le_mul_of_nonneg_left
          (hpartnerBound value)
          (hcoordinateNonnegative (value : index)))
      hproductSummable
      hmajorantSummable
  have hsubtypeLe :
      (∑' value : {value : index // predicate value},
        coordinate (value : index)) ≤ total :=
    tsum_subtype_le coordinate predicate hcoordinateNonnegative hcoordinateSummable
  have htotalNonnegative : 0 ≤ total :=
    tsum_nonneg hcoordinateNonnegative
  calc
    (∑' value : {value : index // predicate value},
        coordinate (value : index) * coordinate (partner value)) ≤
        ∑' value : {value : index // predicate value},
          coordinate (value : index) * total := hproductLe
    _ = (∑' value : {value : index // predicate value},
          coordinate (value : index)) * total :=
      hsubtypeSummable.tsum_mul_right total
    _ ≤ total * total :=
      mul_le_mul_of_nonneg_right hsubtypeLe htotalNonnegative
    _ = total ^ 2 := (pow_two total).symm

theorem nonnegative_subtype_tsum_le_square_of_le_product
    {index : Type*}
    (coordinate : index → ℝ)
    (predicate : index → Prop)
    (partner : {value : index // predicate value} → index)
    (target : {value : index // predicate value} → ℝ)
    (hcoordinateNonnegative : ∀ value : index, 0 ≤ coordinate value)
    (hcoordinateSummable : Summable coordinate)
    (htargetSummable : Summable target)
    (htargetLe :
      ∀ value : {value : index // predicate value},
        target value ≤
          coordinate (value : index) * coordinate (partner value)) :
    (∑' value : {value : index // predicate value}, target value) ≤
      (∑' value : index, coordinate value) ^ 2 := by
  have hpartnerBound :
      ∀ value : {value : index // predicate value},
        coordinate (partner value) ≤ ∑' other : index, coordinate other :=
    fun value =>
      le_tsum hcoordinateSummable (partner value)
        (fun other _ => hcoordinateNonnegative other)
  have hsubtypeSummable :
      Summable
        (fun value : {value : index // predicate value} =>
          coordinate (value : index)) :=
    hcoordinateSummable.subtype predicate
  have hproductSummable :
      Summable
        (fun value : {value : index // predicate value} =>
          coordinate (value : index) * coordinate (partner value)) :=
    Summable.of_nonneg_of_le
      (fun value =>
        mul_nonneg
          (hcoordinateNonnegative (value : index))
          (hcoordinateNonnegative (partner value)))
      (fun value =>
        mul_le_mul_of_nonneg_left
          (hpartnerBound value)
          (hcoordinateNonnegative (value : index)))
      (hsubtypeSummable.mul_right
        (∑' other : index, coordinate other))
  exact le_trans
    (tsum_le_tsum htargetLe htargetSummable hproductSummable)
    (nonnegative_subtype_product_tsum_le_square
      coordinate predicate partner hcoordinateNonnegative hcoordinateSummable)

theorem completedZeroSeedDaggerProductL1Norm_le_affineComplementDistance_square
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S P : Finset ℂ)
    (f₀ h : ZetaAdmissibleFunction)
    (hSeparated :
      ∀ rho : ℂ,
        ZetaCompletedZero rho → rho ∉ S →
          rho ∉ daggerClosedSpectralSampleFinset P) :
    completedZeroSeedDaggerProductL1Norm S (f₀ + h) ≤
      (zetaCompletedZeroCoordinateComplementL1Distance
        (daggerClosedSpectralSampleFinset P)
        (-(zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f₀))
        (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary h)) ^ 2 := by
  let corrected : ZetaAdmissibleFunction := f₀ + h
  let closedSamples : Finset ℂ := daggerClosedSpectralSampleFinset P
  let coordinate : ZetaCompletedZeroCoordinate → ℝ :=
    fun rho : ZetaCompletedZeroCoordinate =>
      if (rho : ℂ) ∈ closedSamples then 0
      else ‖zetaZeroSideContribution (rho : ℂ) corrected‖
  let tailPredicate : ZetaCompletedZeroCoordinate → Prop :=
    fun rho : ZetaCompletedZeroCoordinate => (rho : ℂ) ∉ S
  let partner : {rho : ZetaCompletedZeroCoordinate // tailPredicate rho} →
      ZetaCompletedZeroCoordinate :=
    fun rho => zetaCompletedZeroDagger (rho : ZetaCompletedZeroCoordinate)
  let target : {rho : ZetaCompletedZeroCoordinate // tailPredicate rho} → ℝ :=
    fun rho =>
      (zetaZeroMultiplicity ((rho : ZetaCompletedZeroCoordinate) : ℂ) : ℝ) *
        (‖zetaSpectralEval corrected ((rho : ZetaCompletedZeroCoordinate) : ℂ)‖ *
          ‖zetaSpectralEval corrected
            (-star ((rho : ZetaCompletedZeroCoordinate) : ℂ))‖)
  let tailCoordinateEquiv :
      {rho : ZetaCompletedZeroCoordinate // tailPredicate rho} ≃
        {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} :=
    { toFun := fun rho =>
        ⟨((rho : ZetaCompletedZeroCoordinate) : ℂ),
          ⟨(rho : ZetaCompletedZeroCoordinate).property, rho.property⟩⟩
      invFun := fun rho =>
        ⟨⟨(rho : ℂ), rho.property.1⟩, rho.property.2⟩
      left_inv := fun rho => Subtype.ext (Subtype.ext (Eq.refl _))
      right_inv := fun rho => Subtype.ext (Eq.refl _) }
  have hdirectSummable :
      Summable
        (fun rho : ZetaCompletedZeroCoordinate =>
          ‖zetaZeroSideContribution (rho : ℂ) corrected‖) :=
    (summable_zetaZeroSideContribution
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      corrected).norm
  have hcoordinateNonnegative :
      ∀ rho : ZetaCompletedZeroCoordinate, 0 ≤ coordinate rho :=
    fun rho =>
      if_zero_else_norm_nonnegative
        ((rho : ℂ) ∈ closedSamples)
        (zetaZeroSideContribution (rho : ℂ) corrected)
  have hcoordinateLe :
      ∀ rho : ZetaCompletedZeroCoordinate,
        coordinate rho ≤ ‖zetaZeroSideContribution (rho : ℂ) corrected‖ :=
    fun rho =>
      if_zero_else_norm_le_norm
        ((rho : ℂ) ∈ closedSamples)
        (zetaZeroSideContribution (rho : ℂ) corrected)
  have hcoordinateSummable : Summable coordinate :=
    Summable.of_nonneg_of_le
      hcoordinateNonnegative
      hcoordinateLe
      hdirectSummable
  have htargetSummable : Summable target := by
    have hautocorrelationSummable :
        Summable
          (fun rho : ZetaCompletedZeroCoordinate =>
            ‖zetaCompletedZeroAutocorrelationSideCoordinate corrected rho‖) := by
      have hsideSummable :=
        (summable_zetaZeroSideContribution
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
          (convolutionAutocorrelation corrected)).norm
      exact hsideSummable.congr
        (fun rho : ZetaCompletedZeroCoordinate =>
          congrArg norm
            (zetaCompletedZeroAutocorrelationSideCoordinate_eq corrected rho).symm)
    exact (hautocorrelationSummable.subtype tailPredicate).congr
      (fun rho =>
        norm_zetaCompletedZeroAutocorrelationSideCoordinate
          corrected (rho : ZetaCompletedZeroCoordinate))
  have htargetLe :
      ∀ rho : {rho : ZetaCompletedZeroCoordinate // tailPredicate rho},
        target rho ≤
          coordinate (rho : ZetaCompletedZeroCoordinate) * coordinate (partner rho) := by
    intro rho
    have hnotClosed :
        ((rho : ZetaCompletedZeroCoordinate) : ℂ) ∉ closedSamples :=
      hSeparated
        ((rho : ZetaCompletedZeroCoordinate) : ℂ)
        (rho : ZetaCompletedZeroCoordinate).2
        rho.2
    have hdaggerNotClosed :
        ((partner rho : ZetaCompletedZeroCoordinate) : ℂ) ∉ closedSamples := by
      have hreflected := daggerReflection_not_mem_of_not_mem_daggerClosed P
        ((rho : ZetaCompletedZeroCoordinate) : ℂ) hnotClosed
      exact Eq.mp
        (congrArg
          (fun value : ℂ => value ∉ closedSamples)
          (zetaCompletedZeroDagger_coe
            (rho : ZetaCompletedZeroCoordinate)).symm)
        hreflected
    have hcoordinateSelf :
        coordinate (rho : ZetaCompletedZeroCoordinate) =
          ‖zetaZeroSideContribution
            ((rho : ZetaCompletedZeroCoordinate) : ℂ) corrected‖ :=
      if_neg hnotClosed
    have hcoordinatePartner :
        coordinate (partner rho) =
          ‖zetaZeroSideContribution
            ((partner rho : ZetaCompletedZeroCoordinate) : ℂ) corrected‖ :=
      if_neg hdaggerNotClosed
    have htargetCoordinate :
        target rho =
          ‖zetaCompletedZeroAutocorrelationSideCoordinate
            corrected (rho : ZetaCompletedZeroCoordinate)‖ :=
      (norm_zetaCompletedZeroAutocorrelationSideCoordinate
        corrected (rho : ZetaCompletedZeroCoordinate)).symm
    exact Eq.subst
      (motive := fun value : ℝ => value ≤
        coordinate (rho : ZetaCompletedZeroCoordinate) * coordinate (partner rho))
      htargetCoordinate.symm
      (Eq.subst
        (motive := fun value : ℝ =>
          ‖zetaCompletedZeroAutocorrelationSideCoordinate
            corrected (rho : ZetaCompletedZeroCoordinate)‖ ≤ value)
        (congrArg₂ HMul.hMul hcoordinateSelf hcoordinatePartner).symm
        (norm_zetaCompletedZeroAutocorrelationSideCoordinate_le_directProduct
          corrected (rho : ZetaCompletedZeroCoordinate)))
  have htailBound :
      (∑' rho : {rho : ZetaCompletedZeroCoordinate // tailPredicate rho}, target rho) ≤
        (∑' rho : ZetaCompletedZeroCoordinate, coordinate rho) ^ 2 :=
    nonnegative_subtype_tsum_le_square_of_le_product
      coordinate tailPredicate partner target
      hcoordinateNonnegative hcoordinateSummable htargetSummable htargetLe
  have hleft :
      completedZeroSeedDaggerProductL1Norm S corrected =
        ∑' rho : {rho : ZetaCompletedZeroCoordinate // tailPredicate rho}, target rho :=
    by
      unfold completedZeroSeedDaggerProductL1Norm
      have htransport :=
        (tailCoordinateEquiv.tsum_eq
          (fun rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} =>
            (zetaZeroMultiplicity (rho : ℂ) : ℝ) *
              (‖zetaSpectralEval corrected (rho : ℂ)‖ *
                ‖zetaSpectralEval corrected (-star (rho : ℂ))‖))).symm
      exact Eq.trans htransport
        (tsum_congr (fun rho => Eq.refl (target rho)))
  have hright :
      zetaCompletedZeroCoordinateComplementL1Distance closedSamples
          (-(zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f₀))
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary h) =
        ∑' rho : ZetaCompletedZeroCoordinate, coordinate rho := by
    unfold closedSamples
    unfold coordinate
    unfold corrected
    exact affineCoordinateComplementDistance_eq
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      (daggerClosedSpectralSampleFinset P) f₀ h
  exact Eq.subst
    (motive := fun value : ℝ =>
      value ≤
        (zetaCompletedZeroCoordinateComplementL1Distance closedSamples
          (-(zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f₀))
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary h)) ^ 2)
    hleft.symm
    (Eq.subst
      (motive := fun value : ℝ =>
        (∑' rho : {rho : ZetaCompletedZeroCoordinate // tailPredicate rho}, target rho) ≤
          value ^ 2)
      hright.symm
      htailBound)

theorem fixedFiber_seedDaggerProduct_lt_of_kernelApproximation
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ h : ZetaAdmissibleFunction)
    (hSeparated :
      ∀ rho : ℂ,
        ZetaCompletedZero rho →
          rho ∉ S →
            rho ∉ daggerClosedSpectralSampleFinset P)
    (epsilon delta : ℝ)
    (hdeltaPositive : 0 < delta)
    (hdeltaSubunit : delta < 1)
    (hdeltaEpsilon : delta < epsilon)
    (hkernel :
      ∀ z : ℂ,
        z ∈ daggerClosedSpectralSampleFinset P → zetaSpectralEval h z = 0)
    (happroximation :
      zetaCompletedZeroCoordinateComplementL1Distance
          (daggerClosedSpectralSampleFinset P)
          (-(zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
            f₀))
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
            h) < delta) :
    f₀ + h ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
      completedZeroSeedDaggerProductL1Norm S (f₀ + h) < epsilon := by
  have hfiber :
      f₀ + h ∈ AutocorrelationSpectralEvalFiberOf P f₀ :=
    affineKernel_preserves_autocorrelationFiber P f₀ h hkernel
  let distance : ℝ :=
    zetaCompletedZeroCoordinateComplementL1Distance
      (daggerClosedSpectralSampleFinset P)
      (-(zetaCompletedZeroSideCoordinateL1LinearMap
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f₀))
      (zetaCompletedZeroSideCoordinateL1LinearMap
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary h)
  have hdistanceNonnegative : 0 ≤ distance := by
    unfold distance
    unfold zetaCompletedZeroCoordinateComplementL1Distance
    exact tsum_nonneg
      (fun rho : ZetaCompletedZeroCoordinate =>
        if_zero_else_norm_nonnegative
          ((rho : ℂ) ∈ daggerClosedSpectralSampleFinset P)
          ((-(zetaCompletedZeroSideCoordinateL1LinearMap
              hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
              f₀)) rho -
            zetaCompletedZeroSideCoordinateL1LinearMap
              hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
              h rho))
  have hproductBound :
      completedZeroSeedDaggerProductL1Norm S (f₀ + h) ≤ distance ^ 2 :=
    completedZeroSeedDaggerProductL1Norm_le_affineComplementDistance_square
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S P f₀ h hSeparated
  have hsquareDistance : distance ^ 2 < delta ^ 2 := by
    calc
      distance ^ 2 = distance * distance := pow_two distance
      _ < delta * delta :=
        mul_self_lt_mul_self hdistanceNonnegative happroximation
      _ = delta ^ 2 := (pow_two delta).symm
  have hsquareDelta : delta ^ 2 < delta := by
    calc
      delta ^ 2 = delta * delta := pow_two delta
      _ < delta * 1 :=
        mul_lt_mul_of_pos_left hdeltaSubunit hdeltaPositive
      _ = delta := mul_one delta
  exact And.intro hfiber
    (lt_of_le_of_lt hproductBound
      (lt_trans hsquareDistance (lt_trans hsquareDelta hdeltaEpsilon)))

end QuantitativeSeparation
end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
