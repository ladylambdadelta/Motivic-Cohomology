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
    -star z ∉ daggerClosedSpectralSampleFinset P :=
  fun hreflected =>
  let hdouble : -star (-star z) ∈ daggerClosedSpectralSampleFinset P :=
    mem_daggerClosedSpectralSampleFinset_reflection_of_mem P (-star z) hreflected
  hz
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
    f₀ + h ∈ AutocorrelationSpectralEvalFiberOf P f₀ :=
  fun z hz =>
  let hleft : zetaSpectralEval h z = 0 :=
    hkernel z (mem_daggerClosedSpectralSampleFinset_self P z hz)
  let hright : zetaSpectralEval h (-star z) = 0 :=
    hkernel (-star z)
      (mem_daggerClosedSpectralSampleFinset_reflection P z hz)
  let haddLeft :
      zetaSpectralEval (f₀ + h) z = zetaSpectralEval f₀ z :=
    Eq.trans
      (zetaSpectralEval_add f₀ h z)
      (Eq.trans
        (congrArg (fun value : ℂ => zetaSpectralEval f₀ z + value) hleft)
        (add_zero (zetaSpectralEval f₀ z)))
  let haddRight :
      zetaSpectralEval (f₀ + h) (-star z) =
        zetaSpectralEval f₀ (-star z) :=
    Eq.trans
      (zetaSpectralEval_add f₀ h (-star z))
      (Eq.trans
        (congrArg
          (fun value : ℂ => zetaSpectralEval f₀ (-star z) + value)
          hright)
        (add_zero (zetaSpectralEval f₀ (-star z))))
  Eq.trans
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
      else ‖zetaZeroSideContribution (rho : ℂ) (f₀ + h)‖ :=
  if hmembership : (rho : ℂ) ∈ P then
    Eq.trans (if_pos hmembership) (if_pos hmembership).symm
  else
    let hcoordinateAdd :
        zetaZeroSideContribution (rho : ℂ) (f₀ + h) =
          zetaZeroSideContribution (rho : ℂ) f₀ +
            zetaZeroSideContribution (rho : ℂ) h :=
      zetaZeroSideContribution_add (rho : ℂ) f₀ h
    let hnegative :
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
    let hnorm :
        ‖-(zetaZeroSideContribution (rho : ℂ) f₀) -
            zetaZeroSideContribution (rho : ℂ) h‖ =
          ‖zetaZeroSideContribution (rho : ℂ) (f₀ + h)‖ :=
      Eq.trans
        (congrArg norm hnegative)
        (norm_neg (zetaZeroSideContribution (rho : ℂ) (f₀ + h)))
    Eq.trans
      (if_neg hmembership)
      (Eq.trans hnorm (if_neg hmembership).symm)

theorem if_zero_else_norm_nonnegative
    (proposition : Prop)
    [Decidable proposition]
    (value : ℂ) :
    0 ≤ if proposition then 0 else ‖value‖ :=
  if hproposition : proposition then
    Eq.subst
      (motive := fun result : ℝ => 0 ≤ result)
      (if_pos hproposition).symm
      (le_refl 0)
  else
    Eq.subst
      (motive := fun result : ℝ => 0 ≤ result)
      (if_neg hproposition).symm
      (norm_nonneg value)

theorem if_zero_else_norm_le_norm
    (proposition : Prop)
    [Decidable proposition]
    (value : ℂ) :
    (if proposition then 0 else ‖value‖) ≤ ‖value‖ :=
  if hproposition : proposition then
    Eq.subst
      (motive := fun result : ℝ => result ≤ ‖value‖)
      (if_pos hproposition).symm
      (norm_nonneg value)
  else
    Eq.subst
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
        else ‖zetaZeroSideContribution (rho : ℂ) (f₀ + h)‖ :=
  tsum_congr
    (affineCoordinateComplement_summand_eq
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      P f₀ h)

/-- Product-sum domination and subtype-mass domination combine to bound the
product sum by the square of the ambient total. -/
theorem nonnegative_subtype_product_tsum_le_square_of_bounds
    {index : Type*}
    (coordinate : index → ℝ)
    (predicate : index → Prop)
    (partner : {value : index // predicate value} → index)
    (total : ℝ)
    (hproductLe :
      (∑' value : {value : index // predicate value},
          coordinate (value : index) * coordinate (partner value)) ≤
        ∑' value : {value : index // predicate value},
          coordinate (value : index) * total)
    (hsumMul :
      (∑' value : {value : index // predicate value},
          coordinate (value : index) * total) =
        (∑' value : {value : index // predicate value},
          coordinate (value : index)) * total)
    (hsubtypeLe :
      (∑' value : {value : index // predicate value},
        coordinate (value : index)) ≤ total)
    (htotalNonnegative : 0 ≤ total) :
    (∑' value : {value : index // predicate value},
        coordinate (value : index) * coordinate (partner value)) ≤
      total ^ 2 :=
  le_trans
    hproductLe
    (Eq.subst
      (motive := fun square : ℝ =>
        (∑' value : {value : index // predicate value},
            coordinate (value : index) * total) ≤ square)
      (pow_two total).symm
      (Eq.subst
        (motive := fun left : ℝ => left ≤ total * total)
        hsumMul.symm
        (mul_le_mul_of_nonneg_right hsubtypeLe htotalNonnegative)))

theorem nonnegative_subtype_product_tsum_le_square
    {index : Type*}
    (coordinate : index → ℝ)
    (predicate : index → Prop)
    (partner : {value : index // predicate value} → index)
    (hcoordinateNonnegative : ∀ value : index, 0 ≤ coordinate value)
    (hcoordinateSummable : Summable coordinate) :
    (∑' value : {value : index // predicate value},
        coordinate (value : index) * coordinate (partner value)) ≤
      (∑' value : index, coordinate value) ^ 2 :=
  let total : ℝ := ∑' value : index, coordinate value
  let hpartnerBound :
      ∀ value : {value : index // predicate value},
        coordinate (partner value) ≤ total :=
    fun value =>
      le_tsum hcoordinateSummable (partner value)
        (fun other _ => hcoordinateNonnegative other)
  let hsubtypeSummable :
      Summable
        (fun value : {value : index // predicate value} =>
          coordinate (value : index)) :=
    hcoordinateSummable.subtype predicate
  let hmajorantSummable :
      Summable
        (fun value : {value : index // predicate value} =>
          coordinate (value : index) * total) :=
    hsubtypeSummable.mul_right total
  let hproductSummable :
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
  let hproductLe :
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
  let hsubtypeLe :
      (∑' value : {value : index // predicate value},
        coordinate (value : index)) ≤ total :=
    tsum_subtype_le coordinate predicate hcoordinateNonnegative hcoordinateSummable
  let htotalNonnegative : 0 ≤ total :=
    tsum_nonneg hcoordinateNonnegative
  nonnegative_subtype_product_tsum_le_square_of_bounds
    coordinate
    predicate
    partner
    total
    hproductLe
    (hsubtypeSummable.tsum_mul_right total)
    hsubtypeLe
    htotalNonnegative

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
      (∑' value : index, coordinate value) ^ 2 :=
  let hpartnerBound :
      ∀ value : {value : index // predicate value},
        coordinate (partner value) ≤ ∑' other : index, coordinate other :=
    fun value =>
      le_tsum hcoordinateSummable (partner value)
        (fun other _ => hcoordinateNonnegative other)
  let hsubtypeSummable :
      Summable
        (fun value : {value : index // predicate value} =>
          coordinate (value : index)) :=
    hcoordinateSummable.subtype predicate
  let hproductSummable :
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
  le_trans
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
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary h)) ^ 2 :=
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
      left_inv := fun rho =>
        Subtype.ext
          (Subtype.ext (Eq.refl ((rho : ZetaCompletedZeroCoordinate) : ℂ)))
      right_inv := fun rho => Subtype.ext (Eq.refl (rho : ℂ)) }
  let hdirectSummable :
      Summable
        (fun rho : ZetaCompletedZeroCoordinate =>
          ‖zetaZeroSideContribution (rho : ℂ) corrected‖) :=
    (summable_zetaZeroSideContribution
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      corrected).norm
  let hcoordinateNonnegative :
      ∀ rho : ZetaCompletedZeroCoordinate, 0 ≤ coordinate rho :=
    fun rho =>
      if_zero_else_norm_nonnegative
        ((rho : ℂ) ∈ closedSamples)
        (zetaZeroSideContribution (rho : ℂ) corrected)
  let hcoordinateLe :
      ∀ rho : ZetaCompletedZeroCoordinate,
        coordinate rho ≤ ‖zetaZeroSideContribution (rho : ℂ) corrected‖ :=
    fun rho =>
      if_zero_else_norm_le_norm
        ((rho : ℂ) ∈ closedSamples)
        (zetaZeroSideContribution (rho : ℂ) corrected)
  let hcoordinateSummable : Summable coordinate :=
    Summable.of_nonneg_of_le
      hcoordinateNonnegative
      hcoordinateLe
      hdirectSummable
  let htargetSummable : Summable target :=
    let hautocorrelationSummable :
        Summable
          (fun rho : ZetaCompletedZeroCoordinate =>
            ‖zetaCompletedZeroAutocorrelationSideCoordinate corrected rho‖) :=
      let hsideSummable :
          Summable
            (fun rho : ZetaCompletedZeroCoordinate =>
              ‖zetaZeroSideContribution (rho : ℂ)
                (convolutionAutocorrelation corrected)‖) :=
        (summable_zetaZeroSideContribution
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
          (convolutionAutocorrelation corrected)).norm
      hsideSummable.congr
        (fun rho : ZetaCompletedZeroCoordinate =>
          congrArg norm
            (zetaCompletedZeroAutocorrelationSideCoordinate_eq corrected rho).symm)
    (hautocorrelationSummable.subtype tailPredicate).congr
      (fun rho =>
        norm_zetaCompletedZeroAutocorrelationSideCoordinate
          corrected (rho : ZetaCompletedZeroCoordinate))
  let htargetLe :
      ∀ rho : {rho : ZetaCompletedZeroCoordinate // tailPredicate rho},
        target rho ≤
          coordinate (rho : ZetaCompletedZeroCoordinate) * coordinate (partner rho) :=
    fun rho =>
    let hnotClosed :
        ((rho : ZetaCompletedZeroCoordinate) : ℂ) ∉ closedSamples :=
      hSeparated
        ((rho : ZetaCompletedZeroCoordinate) : ℂ)
        (rho : ZetaCompletedZeroCoordinate).2
        rho.2
    let hdaggerNotClosed :
        ((partner rho : ZetaCompletedZeroCoordinate) : ℂ) ∉ closedSamples :=
      let hreflected :
          -star ((rho : ZetaCompletedZeroCoordinate) : ℂ) ∉
            daggerClosedSpectralSampleFinset P :=
        daggerReflection_not_mem_of_not_mem_daggerClosed P
        ((rho : ZetaCompletedZeroCoordinate) : ℂ) hnotClosed
      Eq.mp
        (congrArg
          (fun value : ℂ => value ∉ closedSamples)
          (zetaCompletedZeroDagger_coe
            (rho : ZetaCompletedZeroCoordinate)).symm)
        hreflected
    let hcoordinateSelf :
        coordinate (rho : ZetaCompletedZeroCoordinate) =
          ‖zetaZeroSideContribution
            ((rho : ZetaCompletedZeroCoordinate) : ℂ) corrected‖ :=
      if_neg hnotClosed
    let hcoordinatePartner :
        coordinate (partner rho) =
          ‖zetaZeroSideContribution
            ((partner rho : ZetaCompletedZeroCoordinate) : ℂ) corrected‖ :=
      if_neg hdaggerNotClosed
    let htargetCoordinate :
        target rho =
          ‖zetaCompletedZeroAutocorrelationSideCoordinate
            corrected (rho : ZetaCompletedZeroCoordinate)‖ :=
      (norm_zetaCompletedZeroAutocorrelationSideCoordinate
        corrected (rho : ZetaCompletedZeroCoordinate)).symm
    Eq.subst
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
  let htailBound :
      (∑' rho : {rho : ZetaCompletedZeroCoordinate // tailPredicate rho}, target rho) ≤
        (∑' rho : ZetaCompletedZeroCoordinate, coordinate rho) ^ 2 :=
    nonnegative_subtype_tsum_le_square_of_le_product
      coordinate tailPredicate partner target
      hcoordinateNonnegative hcoordinateSummable htargetSummable htargetLe
  let hleft :
      completedZeroSeedDaggerProductL1Norm S corrected =
        ∑' rho : {rho : ZetaCompletedZeroCoordinate // tailPredicate rho}, target rho :=
    let htransport :
        (∑' rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S},
          (zetaZeroMultiplicity (rho : ℂ) : ℝ) *
            (‖zetaSpectralEval corrected (rho : ℂ)‖ *
              ‖zetaSpectralEval corrected (-star (rho : ℂ))‖)) =
          ∑' rho : {rho : ZetaCompletedZeroCoordinate // tailPredicate rho},
            (zetaZeroMultiplicity
              ((rho : ZetaCompletedZeroCoordinate) : ℂ) : ℝ) *
              (‖zetaSpectralEval corrected
                  ((rho : ZetaCompletedZeroCoordinate) : ℂ)‖ *
                ‖zetaSpectralEval corrected
                  (-star ((rho : ZetaCompletedZeroCoordinate) : ℂ))‖) :=
        (tailCoordinateEquiv.tsum_eq
          (fun rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} =>
            (zetaZeroMultiplicity (rho : ℂ) : ℝ) *
              (‖zetaSpectralEval corrected (rho : ℂ)‖ *
                ‖zetaSpectralEval corrected (-star (rho : ℂ))‖))).symm
    Eq.trans htransport
      (tsum_congr (fun rho => Eq.refl (target rho)))
  let hright :
      zetaCompletedZeroCoordinateComplementL1Distance closedSamples
          (-(zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f₀))
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary h) =
        ∑' rho : ZetaCompletedZeroCoordinate, coordinate rho :=
    affineCoordinateComplementDistance_eq
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      (daggerClosedSpectralSampleFinset P) f₀ h
  Eq.subst
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

/-- A nonnegative strict bound controls the square by the square of the
upper bound. -/
theorem square_lt_square_of_nonnegative_lt
    (distance delta : ℝ)
    (hdistanceNonnegative : 0 ≤ distance)
    (happroximation : distance < delta) :
    distance ^ 2 < delta ^ 2 :=
  Eq.subst
    (motive := fun left : ℝ => left < delta ^ 2)
    (pow_two distance).symm
    (Eq.subst
      (motive := fun right : ℝ => distance * distance < right)
      (pow_two delta).symm
      (mul_self_lt_mul_self hdistanceNonnegative happroximation))

/-- A positive subunit bound makes the square strictly smaller than the
original positive number. -/
theorem square_lt_self_of_positive_lt_one
    (delta : ℝ)
    (hdeltaPositive : 0 < delta)
    (hdeltaSubunit : delta < 1) :
    delta ^ 2 < delta :=
  Eq.subst
    (motive := fun left : ℝ => left < delta)
    (pow_two delta).symm
    (Eq.subst
      (motive := fun right : ℝ => delta * delta < right)
      (mul_one delta)
      (mul_lt_mul_of_pos_left hdeltaSubunit hdeltaPositive))

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
      completedZeroSeedDaggerProductL1Norm S (f₀ + h) < epsilon :=
  let hfiber :
      f₀ + h ∈ AutocorrelationSpectralEvalFiberOf P f₀ :=
    affineKernel_preserves_autocorrelationFiber P f₀ h hkernel
  let distance : ℝ :=
    zetaCompletedZeroCoordinateComplementL1Distance
      (daggerClosedSpectralSampleFinset P)
      (-(zetaCompletedZeroSideCoordinateL1LinearMap
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f₀))
      (zetaCompletedZeroSideCoordinateL1LinearMap
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary h)
  let hdistanceNonnegative : 0 ≤ distance :=
    tsum_nonneg
      (fun rho : ZetaCompletedZeroCoordinate =>
        if_zero_else_norm_nonnegative
          ((rho : ℂ) ∈ daggerClosedSpectralSampleFinset P)
          ((-(zetaCompletedZeroSideCoordinateL1LinearMap
              hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
              f₀)) rho -
            zetaCompletedZeroSideCoordinateL1LinearMap
              hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
              h rho))
  let hproductBound :
      completedZeroSeedDaggerProductL1Norm S (f₀ + h) ≤ distance ^ 2 :=
    completedZeroSeedDaggerProductL1Norm_le_affineComplementDistance_square
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S P f₀ h hSeparated
  let hsquareDistance : distance ^ 2 < delta ^ 2 :=
    square_lt_square_of_nonnegative_lt
      distance
      delta
      hdistanceNonnegative
      happroximation
  let hsquareDelta : delta ^ 2 < delta :=
    square_lt_self_of_positive_lt_one
      delta
      hdeltaPositive
      hdeltaSubunit
  And.intro hfiber
    (lt_of_le_of_lt hproductBound
      (lt_trans hsquareDistance (lt_trans hsquareDelta hdeltaEpsilon)))

end QuantitativeSeparation
end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
