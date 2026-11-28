/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Data.ENat.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Tautological
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.DualClass.Basic
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.ProjectiveSpace
public import SymplecticGeometry.LinearAlgebra.Complex.Finrank
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.ThomPairMap
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Topology
public import TauCeti.Topology.VectorBundle.Orientation.Comap
public import TauCeti.Topology.VectorBundle.Orientation.Complex.EulerClass
import SymplecticGeometry.Geometry.Manifold.IsManifold.Basic
import SymplecticGeometry.LinearAlgebra.Complex.Orientation
import TauCeti.LinearAlgebra.Complex.Orientation
import TauCeti.Topology.VectorBundle.Orientation.FiberwiseEquiv

/-!
# The exceptional class of a blowup

Let `M` be a smooth manifold modelled on `E = Fin (n + 1) → ℂ`, and `c` a chart of its smooth
atlas centred at `p₀`, so that the blowup `Blowup c` and its exceptional divisor
`Z = divisorRealEmbedding c`, a copy of `ℙ ℂ E`, are defined. Near `Z` the map `lift c` is a
local diffeomorphism onto a neighbourhood of the zero section of the model `BlowupModel n`, which
it sends `Z` onto. Its differential therefore identifies the normal bundle of `Z` with that of
the zero section of the model, which `BlowupModel.normalSpaceZeroSectionRealEquiv` identifies with
the tautological line `Projectivization.Tautological ℂ E` (`Blowup.divisorNormalEquiv`). The
complex orientation of the tautological line, carried back along this isomorphism, orients the
normal bundle of `Z` (`Blowup.divisorNormalOrientation`).

The *exceptional class* `e ∈ H²(Blowup c; ℤ)` (`Blowup.exceptionalClass`) is the dual class
`TauCeti.SmoothEmbedding.dualClass` of `Z` for this normal orientation. Its coefficients are
`ULift ℤ`, those of Tau Ceti's `TauCeti.firstChernClass`, so the Chern class formula of the blowup
can use it with no conversion.

## Main definitions

* `SymplecticGeometry.Blowup.divisorNormalEquiv c`: the isomorphism of the normal bundle of the
  exceptional divisor with the tautological line, with its value on normal classes
  `SymplecticGeometry.Blowup.divisorNormalEquiv_normalClass`.
* `SymplecticGeometry.Blowup.divisorNormalOrientation c`: the orientation of the normal bundle
  that this isomorphism carries from the complex orientation of the tautological line.
* `SymplecticGeometry.Blowup.exceptionalClass c`: the exceptional class, with
  `SymplecticGeometry.Blowup.exceptionalClass_def`.

## Main results

* `SymplecticGeometry.Blowup.orientation_map_eq_divisorNormalOrientation`: a complex-linear
  isomorphism `ℂ ≃ ℓ`, read on `ℝ²` through `Complex.orthonormalBasisOneI` and carried to the
  normal space by `divisorNormalEquiv c ℓ`, takes the standard orientation of `ℝ²` to
  `divisorNormalOrientation c ℓ`.
* `SymplecticGeometry.Blowup.divisorNormalEquiv_normalClassL_of_lift_eventuallyEq_curveLift_smul`:
  a curve that `lift c` reads near `0` as the lift of the line `t ↦ t • v` crosses the exceptional
  divisor with normal velocity `v`.
* `SymplecticGeometry.Blowup.exceptionalClass_restrict_compl`: `e` vanishes on the complement of
  the exceptional divisor, and `SymplecticGeometry.Blowup.exceptionalClass_pairing_compl`: it
  pairs to zero with every homology class pushed forward from that complement.
* `SymplecticGeometry.Blowup.exceptionalClass_restrict_divisor_eq_complexEulerClass`: the
  restriction of `e` to the exceptional divisor is the Euler class of the tautological line, and
  `SymplecticGeometry.Blowup.exceptionalClass_restrict_divisor`: in integral cohomology it is
  `-h`, minus the hyperplane class `Projectivization.hyperplaneClass`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1.
-/

public section

noncomputable section

open AlgebraicTopology Bundle CategoryTheory Module Set TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization TauCeti.ComplexManifold

namespace SymplecticGeometry

namespace Blowup

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] {p₀ : M} (c : BlowupChart (n := n) M p₀)
  [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M)]

/-- **The normal bundle of the exceptional divisor is the tautological line.** At a point `ℓ` of
the exceptional divisor, the isomorphism from the normal space of `divisorRealEmbedding c` onto
the line `ℓ`: the differential of `lift c`, onto the normal space of the zero section of the
model, followed by `BlowupModel.normalSpaceZeroSectionRealEquiv`. -/
def divisorNormalEquiv (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    (divisorRealEmbedding c).isImmersion.NormalSpace ℓ ENat.coe_top_ne_zero ≃L[ℝ]
      Projectivization.Tautological ℂ (Fin (n + 1) → ℂ) ℓ :=
  ((divisorRealEmbedding c).normalSpaceEquivOfComp (BlowupModel.zeroSectionRealEmbedding n)
      ENat.coe_top_ne_zero ENat.coe_top_ne_zero
      (isInvertible_mfderiv_lift_divisorRealEmbedding c)
      ((lift_comp_divisorRealEmbedding c).trans
        (BlowupModel.coe_zeroSectionRealEmbedding (n := n)).symm) ℓ).trans
    (BlowupModel.normalSpaceZeroSectionRealEquiv n ENat.coe_top_ne_zero ℓ)

/-- `divisorNormalEquiv c`, unfolded. -/
theorem divisorNormalEquiv_def (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    divisorNormalEquiv c ℓ =
      ((divisorRealEmbedding c).normalSpaceEquivOfComp (BlowupModel.zeroSectionRealEmbedding n)
          ENat.coe_top_ne_zero ENat.coe_top_ne_zero
          (isInvertible_mfderiv_lift_divisorRealEmbedding c)
          ((lift_comp_divisorRealEmbedding c).trans
            (BlowupModel.coe_zeroSectionRealEmbedding (n := n)).symm) ℓ).trans
        (BlowupModel.normalSpaceZeroSectionRealEquiv n ENat.coe_top_ne_zero ℓ) :=
  (rfl)

/-- `divisorNormalEquiv c ℓ` sends the normal class of a tangent vector `w` of the blowup at
`divisorRealEmbedding c ℓ` to the differential of `blowdown` at `zeroSection ℓ` applied to the
image of `w` under the differential of `lift c`, as a vector of the line `ℓ`. -/
@[simp]
theorem divisorNormalEquiv_normalClass (ℓ : ℙ ℂ (Fin (n + 1) → ℂ))
    (w : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) (divisorRealEmbedding c ℓ)) :
    divisorNormalEquiv c ℓ
        ((divisorRealEmbedding c).isImmersion.normalClass ℓ ENat.coe_top_ne_zero w) =
      ⟨mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) BlowupModel.blowdown
          (BlowupModel.zeroSection ℓ)
          (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (lift c)
            (divisorRealEmbedding c ℓ) w),
        BlowupModel.mfderiv_blowdown_zeroSection_mem ℓ _⟩ := by
  rw [divisorNormalEquiv_def, ContinuousLinearEquiv.trans_apply,
    SmoothEmbedding.normalSpaceEquivOfComp_normalClass,
    BlowupModel.normalSpaceZeroSectionRealEquiv_normalClass, tangentSpaceCast_apply]

/-- **A curve along a lifted line crosses the exceptional divisor with normal velocity `v`.**
Let `v ≠ 0`, and `g : ℂ → Blowup c` a curve with `g 0 = divisorRealEmbedding c [v]`, with real
derivative `A` at `0`, and such that `lift c ∘ g` agrees near `0` with the lift
`BlowupModel.curveLift (· • v)` of the line `t ↦ t • v`. Then `divisorNormalEquiv c [v]` sends the
normal class of `A z` to `Projectivization.toTautological hv _ z`, the vector `z • v`, for every
`z : ℂ`. -/
theorem divisorNormalEquiv_normalClassL_of_lift_eventuallyEq_curveLift_smul
    {v : Fin (n + 1) → ℂ} (hv : v ≠ 0) {g : ℂ → Blowup c}
    {A : ℂ →L[ℝ] Fin (n + 1) → ℂ}
    (hA : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) g 0 A)
    (hg0 : g 0 = divisorRealEmbedding c (Projectivization.mk ℂ v hv))
    (hg : lift c ∘ g =ᶠ[nhds 0] BlowupModel.curveLift (· • v)) (z : ℂ) :
    divisorNormalEquiv c (Projectivization.mk ℂ v hv)
        ((divisorRealEmbedding c).isImmersion.normalClassL (Projectivization.mk ℂ v hv)
          ENat.coe_top_ne_zero (A z)) =
      Projectivization.toTautological hv (Projectivization.submodule_mk v hv) z := by
  have hL : HasMFDerivAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (lift c) (g 0)
      (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (lift c)
        (divisorRealEmbedding c (Projectivization.mk ℂ v hv))) := by
    rw [hg0]
    exact ((isLocalDiffeomorphAt_lift_divisorRealEmbedding c _).mdifferentiableAt
      (by simp)).hasMFDerivAt
  have h := ((hL.comp 0 hA).congr_of_eventuallyEq_abuse hg.symm).mfderiv
  refine (congrArg _ (Manifold.IsImmersion.normalClassL_apply _ _ _ _)).trans
    ((divisorNormalEquiv_normalClass c _ _).trans (Subtype.ext ?_))
  rw [Projectivization.coe_toTautological_apply]
  -- `h` says that `mfderiv (curveLift (· • v)) 0` is `mfderiv (lift c) _ ∘L A`. Its value at `z`
  -- is the image of `A z` by unfolding the application of a composition: `comp_apply` does not
  -- elaborate, since the tangent space at `curveLift (· • v) 0` has no `Module ℝ` instance under
  -- that name.
  exact (congrArg (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) BlowupModel.blowdown
      (BlowupModel.zeroSection (Projectivization.mk ℂ v hv)))
      (DFunLike.congr_fun h z).symm).trans
    (BlowupModel.mfderiv_blowdown_mfderiv_curveLift_smul hv z)

/-- The isomorphisms `divisorNormalEquiv c ℓ` form a continuous map from the total space of the
normal bundle of the exceptional divisor to that of the tautological line. -/
theorem continuous_divisorNormalEquiv {K : Type*} :
    Continuous fun p : TotalSpace K
        (fun ℓ ↦ (divisorRealEmbedding c).isImmersion.NormalSpace ℓ ENat.coe_top_ne_zero) ↦
      (⟨p.proj, divisorNormalEquiv c p.proj p.snd⟩ :
        TotalSpace ℂ (Projectivization.Tautological ℂ (Fin (n + 1) → ℂ))) := by
  have h₁ := (divisorRealEmbedding c).continuous_normalSpaceEquivOfComp_of_contMDiffAt (K := K)
    (K' := K) (BlowupModel.zeroSectionRealEmbedding n) ENat.coe_top_ne_zero ENat.coe_top_ne_zero
    (fun ℓ ↦ (isLocalDiffeomorphAt_lift_divisorRealEmbedding c ℓ).contMDiffAt.of_le
      ENat.LEInfty.out)
    (isInvertible_mfderiv_lift_divisorRealEmbedding c) ((lift_comp_divisorRealEmbedding c).trans
      (BlowupModel.coe_zeroSectionRealEmbedding (n := n)).symm)
  exact (BlowupModel.continuous_normalSpaceZeroSectionRealEquiv (n := n)
    ENat.coe_top_ne_zero).comp h₁

/-- **The normal orientation of the exceptional divisor.** The orientation of the normal bundle of
`divisorRealEmbedding c` that `divisorNormalEquiv c` carries from the complex orientation
`TauCeti.VectorBundleOrientation.complex` of the tautological line. -/
def divisorNormalOrientation :
    letI := (divisorRealEmbedding c).normalSpaceFiberBundle ENat.coe_top_ne_zero
      (Complex.finrank_real_eq_finrank_pi_succ_sub n)
    letI := (divisorRealEmbedding c).normalSpaceVectorBundle ENat.coe_top_ne_zero
      (Complex.finrank_real_eq_finrank_pi_succ_sub n)
    VectorBundleOrientation ℂ
      (fun ℓ ↦ (divisorRealEmbedding c).isImmersion.NormalSpace ℓ ENat.coe_top_ne_zero) (Fin 2) :=
  letI := (divisorRealEmbedding c).normalSpaceFiberBundle ENat.coe_top_ne_zero
    (Complex.finrank_real_eq_finrank_pi_succ_sub n)
  letI := (divisorRealEmbedding c).normalSpaceVectorBundle ENat.coe_top_ne_zero
    (Complex.finrank_real_eq_finrank_pi_succ_sub n)
  letI : VectorBundle ℝ ℂ (Projectivization.Tautological ℂ (Fin (n + 1) → ℂ)) :=
    VectorBundle.restrictScalars ℝ ℂ ℂ _
  ((VectorBundleOrientation.complex ℂ
      (Projectivization.Tautological ℂ (Fin (n + 1) → ℂ))).reindex
      (finCongr Complex.two_mul_finrank_self : Fin (2 * finrank ℂ ℂ) ≃ Fin 2)).comap
    (g := ContinuousMap.id _) (by simp) (continuous_divisorNormalEquiv c)

/-- `divisorNormalOrientation c`, unfolded. -/
theorem divisorNormalOrientation_def :
    letI := (divisorRealEmbedding c).normalSpaceFiberBundle ENat.coe_top_ne_zero
      (Complex.finrank_real_eq_finrank_pi_succ_sub n)
    letI := (divisorRealEmbedding c).normalSpaceVectorBundle ENat.coe_top_ne_zero
      (Complex.finrank_real_eq_finrank_pi_succ_sub n)
    letI : VectorBundle ℝ ℂ (Projectivization.Tautological ℂ (Fin (n + 1) → ℂ)) :=
      VectorBundle.restrictScalars ℝ ℂ ℂ _
    divisorNormalOrientation c =
      ((VectorBundleOrientation.complex ℂ
          (Projectivization.Tautological ℂ (Fin (n + 1) → ℂ))).reindex
        (finCongr Complex.two_mul_finrank_self : Fin (2 * finrank ℂ ℂ) ≃ Fin 2)).comap
        (g := ContinuousMap.id _) (by simp) (continuous_divisorNormalEquiv c) :=
  (rfl)

/-- **A complex identification of the line `ℓ` orients the normal space.** Let
`e : ℂ ≃ ℓ` be a complex-linear isomorphism onto the line `ℓ`, and let
`m : ℝ² ≃ ν_ℓ` be the real-linear isomorphism onto the normal space of the exceptional divisor at
`ℓ` that `divisorNormalEquiv c ℓ` turns into `e`, with `w ∈ ℝ²` read in `ℂ` by
`Complex.orthonormalBasisOneI.repr.symm`. Then `m` carries the standard orientation of `ℝ²` to
`divisorNormalOrientation c ℓ`. -/
theorem orientation_map_eq_divisorNormalOrientation {ℓ : ℙ ℂ (Fin (n + 1) → ℂ)}
    (e : ℂ ≃ₗ[ℂ] Projectivization.Tautological ℂ (Fin (n + 1) → ℂ) ℓ)
    (m : EuclideanSpace ℝ (Fin 2) ≃L[ℝ]
      (divisorRealEmbedding c).isImmersion.NormalSpace ℓ ENat.coe_top_ne_zero)
    (hm : ∀ w, divisorNormalEquiv c ℓ (m w) = e (Complex.orthonormalBasisOneI.repr.symm w)) :
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.map (Fin 2) m.toLinearEquiv =
      divisorNormalOrientation c ℓ := by
  let := (divisorRealEmbedding c).normalSpaceFiberBundle ENat.coe_top_ne_zero
    (Complex.finrank_real_eq_finrank_pi_succ_sub n)
  let := (divisorRealEmbedding c).normalSpaceVectorBundle ENat.coe_top_ne_zero
    (Complex.finrank_real_eq_finrank_pi_succ_sub n)
  let : VectorBundle ℝ ℂ (Projectivization.Tautological ℂ (Fin (n + 1) → ℂ)) :=
    VectorBundle.restrictScalars ℝ ℂ ℂ _
  have hm' : m.toLinearEquiv = (Complex.orthonormalBasisOneI.repr.symm.toLinearEquiv.trans
      (e.restrictScalars ℝ)).trans (divisorNormalEquiv c ℓ).symm.toLinearEquiv := by
    ext w
    exact (ContinuousLinearEquiv.eq_symm_apply _).2 (hm w)
  rw [hm', Orientation.map_trans, Orientation.map_trans,
    Complex.orientation_map_orthonormalBasisOneI_repr_symm, divisorNormalOrientation_def]
  refine Eq.trans ?_ (VectorBundleOrientation.comap_apply (g := ContinuousMap.id _) _ _
    (continuous_divisorNormalEquiv c) ℓ).symm
  rw [VectorBundleOrientation.reindex_apply, VectorBundleOrientation.complex_apply,
    ← reindex_complexOrientation_complex, Orientation.map_reindex, e.map_complexOrientation]
  simp only [← Orientation.reindex_trans, ContinuousLinearEquiv.toLinearEquiv_symm]
  congr 1

variable [T2Space M] [SecondCountableTopology M]

/-- **The exceptional class** `e ∈ H²(Blowup c; ℤ)` of the blowup: the dual class
`TauCeti.SmoothEmbedding.dualClass` of the exceptional divisor `divisorRealEmbedding c`, for the
orientation `divisorNormalOrientation c` of its normal bundle carried from the complex orientation
of the tautological line. Its coefficients are `ULift ℤ`.

It is minus the Poincaré dual of the exceptional divisor in McDuff–Salamon's convention: with real
coefficients its relative class pairs to `-1` with a disc that crosses the divisor once,
transversally, with the orientation `divisorNormalOrientation c` in the normal direction
(`TauCeti.SmoothEmbedding.singularKronecker_realRelDualClass_relClass_of_hasFDerivAt_of_eq_comp`).
-/
def exceptionalClass :
    (TopCat.of (Blowup c)).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) 2 :=
  (divisorRealEmbedding c).dualClass ENat.coe_top_ne_zero
    (Complex.finrank_real_eq_finrank_pi_succ_sub n)
    (isClosed_range_divisorRealEmbedding c)
    (divisorNormalOrientation c) Complex.finrank_real_complex

/-- The exceptional class, unfolded. -/
theorem exceptionalClass_def :
    exceptionalClass c = (divisorRealEmbedding c).dualClass ENat.coe_top_ne_zero
      (Complex.finrank_real_eq_finrank_pi_succ_sub n)
      (isClosed_range_divisorRealEmbedding c)
      (divisorNormalOrientation c) Complex.finrank_real_complex :=
  (rfl)

/-- **The exceptional class vanishes off the exceptional divisor**: its restriction to the
complement of the exceptional divisor is zero. -/
theorem exceptionalClass_restrict_compl :
    TopCat.singularCohomologyMap
      (TopPair.ofSubset (X := TopCat.of (Blowup c)) (exceptionalDivisor c)ᶜ).map 2
      (exceptionalClass c) = 0 := by
  -- The closedness proof inside `exceptionalClass c` mentions the range, so rewrite it only after
  -- generalizing.
  have key : ∀ S : Set (Blowup c), range (divisorRealEmbedding c) = S →
      TopCat.singularCohomologyMap (TopPair.ofSubset (X := TopCat.of (Blowup c)) Sᶜ).map 2
        (exceptionalClass c) = 0 := by
    rintro S rfl
    rw [exceptionalClass_def]
    exact (divisorRealEmbedding c).dualClass_restrict_compl _ _ _ _ _
  exact key _ (range_divisorRealEmbedding c)

/-- **The exceptional class pairs to zero with the complement of the exceptional divisor**: its
Kronecker pairing with the image in `H₂(Blowup c; ℤ)` of every class of `H₂` of the complement of
the exceptional divisor is zero. -/
theorem exceptionalClass_pairing_compl
    (x : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).obj
      (TopPair.ofSubset (X := TopCat.of (Blowup c)) (exceptionalDivisor c)ᶜ).snd) :
    ((TopCat.of (Blowup c)).singularKronecker ℤ 2 (exceptionalClass c)).hom
      ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopPair.ofSubset (X := TopCat.of (Blowup c)) (exceptionalDivisor c)ᶜ).map).hom x) =
      0 := by
  have h := congrArg (fun φ ↦ φ.hom x) (TopCat.singularKronecker_naturality
    (TopPair.ofSubset (X := TopCat.of (Blowup c)) (exceptionalDivisor c)ᶜ).map ℤ 2
    (exceptionalClass c))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  -- `h` reads the pair's ambient space as `TopPair.fst`, which is `TopCat.of (Blowup c)` by
  -- definition of `TopPair.ofSubset`; `trans` accepts it up to that unfolding.
  refine h.symm.trans ?_
  rw [exceptionalClass_restrict_compl c, map_zero, ModuleCat.hom_zero, LinearMap.zero_apply]

/-- **The restriction of the exceptional class to the exceptional divisor is the Euler class of
the tautological line**: the pull-back of `e` along `divisorRealEmbedding c` is the Euler class
`TauCeti.complexEulerClass` of the tautological line over `ℙ ℂ (Fin (n + 1) → ℂ)`, with
coefficients `ULift ℤ`. -/
theorem exceptionalClass_restrict_divisor_eq_complexEulerClass :
    TopCat.singularCohomologyMap
        (TopCat.ofHom ⟨divisorRealEmbedding c, (divisorRealEmbedding c).isEmbedding.continuous⟩) 2
        (exceptionalClass c) =
      complexEulerClass (r := 0) ℂ (Projectivization.Tautological ℂ (Fin (n + 1) → ℂ))
        (finrank_self ℂ) := by
  let := (divisorRealEmbedding c).normalSpaceFiberBundle ENat.coe_top_ne_zero
    (Complex.finrank_real_eq_finrank_pi_succ_sub n)
  let := (divisorRealEmbedding c).normalSpaceVectorBundle ENat.coe_top_ne_zero
    (Complex.finrank_real_eq_finrank_pi_succ_sub n)
  let : VectorBundle ℝ ℂ (Projectivization.Tautological ℂ (Fin (n + 1) → ℂ)) :=
    VectorBundle.restrictScalars ℝ ℂ ℂ _
  rw [exceptionalClass_def, (divisorRealEmbedding c).dualClass_restrict_eq_eulerClass (m := 1),
    divisorNormalOrientation_def, VectorBundleOrientation.eulerClass_comap_id,
    complexEulerClass_def]

/-- **The restriction of the exceptional class to the exceptional divisor is minus the hyperplane
class**: in integral cohomology, `ι^* e = -h` for the inclusion `ι = divisorRealEmbedding c` of
the exceptional divisor `ℙ ℂ (Fin (n + 1) → ℂ)` and its hyperplane class `h`
(`Projectivization.hyperplaneClass`). It holds for every `n`, and for a complex manifold `M` and a
holomorphic chart `c` through `Blowup.instFactMemMaximalAtlasReal`. With
`exceptionalClass_pairing_compl` it is the third statement of the milestone below; the second is
`Blowup.nonempty_orientationPreserving_diffeomorph_connectedSum`, the blowup as an oriented
connected sum with the reversed projective space, and the first is
`TauCeti.ConnectedSum.exists_diffeomorph_isOrientationPreservingAt`, the independence of the
oriented connected sum from its balls.

Milestone: *Blowup as a connected sum with the reversed projective space*. -/
theorem exceptionalClass_restrict_divisor :
    ((TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))).uliftIntegralCohomologyIso 2).hom
        (TopCat.singularCohomologyMap
          (TopCat.ofHom ⟨divisorRealEmbedding c, (divisorRealEmbedding c).isEmbedding.continuous⟩)
          2 (exceptionalClass c)) =
      -Projectivization.hyperplaneClass (Fin (n + 1) → ℂ) := by
  rw [exceptionalClass_restrict_divisor_eq_complexEulerClass, Projectivization.hyperplaneClass_def,
    neg_neg]

end Blowup

end SymplecticGeometry

end
