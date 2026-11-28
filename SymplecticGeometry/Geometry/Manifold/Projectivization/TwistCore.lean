/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Topology.VectorBundle.Constructions
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Sum
public import TauCeti.Topology.Algebra.Module.Equiv.Pi
public import TauCeti.Topology.VectorBundle.Core.Trivial
public import TauCeti.Geometry.Manifold.VectorBundle.RestrictScalars
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
public import SymplecticGeometry.Topology.VectorBundle.Core.ScalarCocycle
public import TauCeti.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.TensorProduct.Basic

import Mathlib.Analysis.Analytic.Polynomial
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Core.Section
import SymplecticGeometry.LinearAlgebra.Projectivization.Basic
import SymplecticGeometry.Topology.VectorBundle.Core.Basic
import SymplecticGeometry.Topology.VectorBundle.Coordinates

/-!
# Sums and tensor products of the line bundles `𝒪(k)`

On projective space `ℙ 𝕜 (Fin (n + 1) → 𝕜)`, Tau Ceti's `Projectivization.twistCore k` is the
line bundle `𝒪(k)`, glued from trivial lines over the standard affine opens along the transition
functions `twistTransition k`. This file adds the bundles built from it that the computation of
Chern classes of projective space uses, and the chart-change rules for dehomogenized
polynomials that express sections of `𝒪(d)` in the standard charts.

* `Projectivization.eval_affineChart_dehomogenize_eq_twistTransition_mul`: the dehomogenizations
  of a homogeneous polynomial of degree `d` at two charts, read in those charts, differ on the
  overlap by the transition function of `𝒪(d)`; `HasMFDerivAt.eval_affineChart_dehomogenize`:
  at a zero of the polynomial, so do their differentials;
  `Projectivization.contMDiffOn_eval_affineChart`: a polynomial read in the chart at `i` is
  `C^r` on the affine open `U_i`;
  `Projectivization.trivializationAt_homogeneousSection_chartAt_symm`: in the manifold chart and
  the preferred trivialization of `𝒪(d)` at a point, the section `homogeneousSection d P` reads
  as the dehomogenization of `P` at the index of that chart.
* `Projectivization.twistSumCore_indexAt_eq_twistCore_indexAt`: the preferred chart of Tau
  Ceti's sum `twistSumCore k` at a point is that of every `𝒪(k')`.
* `Projectivization.contMDiff_section_twistSumCore_iff`: a section of Tau Ceti's sum
  `twistSumCore k = ⨁ₗ 𝒪(k l)` is `C^r` exactly when its coordinates in the standard charts are.
  For `𝕜 = ℂ`, `twistSumCore k` and `𝒪(k)` are also smooth real vector bundles over the
  underlying real manifold, by restriction of scalars (the scoped instance
  `VectorBundle.ComplexToReal.vectorBundle` and Tau Ceti's
  `ContMDiffVectorBundle.restrictScalars_modelWithCornersSelf`); files using this real structure
  `open scoped VectorBundle.ComplexToReal`, which also makes real scalar multiplication on the
  fibres of `𝒪(k)` continuous.
* `Projectivization.twistSumCoreOptionEquiv k x`: the splitting
  `⨁_{l : Option κ} 𝒪(k l) ≅ 𝒪(k none) ⊕ ⨁_{l : κ} 𝒪(k (some l))` into Mathlib's direct sum `×ᵇ`
  of bundles, continuous on total spaces in both directions, so that, by induction on `r`,
  `𝒪(k)^{⊕ r}` is an iterated direct sum (for the Whitney formula).
* `Projectivization.twistSumCoreCongr k e x`: the isomorphism
  `⨁_{a : κ} 𝒪(k (e a)) ≅ ⨁_{b : κ'} 𝒪(k b)` that reindexes the coordinates along `e : κ ≃ κ'`,
  continuous on total spaces, so that `Option (Fin r)` above can be read as `Fin (r + 1)`.
* `Projectivization.twistScalarCocycle`: the scalar cocycle of the line bundles `𝒪(k)`, with
  `twistCore k` equal to its line bundle `lineBundleCore k`
  (`Projectivization.twistCore_eq_lineBundleCore`).
* `Projectivization.twistCoreTensorEquiv k l x`: the isomorphism `𝒪(k + l) ≅ 𝒪(k) ⊗ 𝒪(l)` onto
  Tau Ceti's tensor product bundle, `a ↦ a ⊗ 1` in every standard chart
  (`Projectivization.tensorProduct_localTriv_twistCoreTensorEquiv`), continuous on total spaces
  in both directions. It is `SymplecticGeometry.ScalarCocycle.lineBundleCoreTensorEquiv` for
  `twistScalarCocycle`, and its lemmas are those of `lineBundleCoreTensorEquiv`, transported
  along `twistCore_eq_lineBundleCore`.
* `Projectivization.twistCoreZeroTrivialization`: `𝒪(0)` is trivial, by
  `Projectivization.twistTransition_zero` and Tau Ceti's
  `VectorBundleCore.globalTrivializationOfCoordChangeEqId`.

## Implementation notes

The proof of `HasMFDerivAt.eval_affineChart_dehomogenize` adapts that of Tau Ceti's
`TauCeti.fderiv_eval_dehomogenize_transition` from Fréchet derivatives on `Fin n → 𝕜` to
`mfderiv` on projective space.

`contMDiff_section_twistSumCore_iff` is the case of the library's
`VectorBundleCore.contMDiff_section_iff` for Tau Ceti's `twistSumCore`.

The fibres of a vector bundle core are its model fibre under the name `VectorBundleCore.Fiber`,
and the body of `twistCore` is not visible here. The fibrewise maps are therefore built on the
model fibres `𝕜` and `𝕜 × (κ → 𝕜)`. Read in the trivializations at a point `x₀`,
`twistSumCoreOptionEquiv`, its inverse and `twistSumCoreCongr` are one fixed linear map at every
point near `x₀` (by the library's `ContinuousLinearMap.inCoordinates_eq_of_forall_apply`, and
for the inverse by Tau Ceti's `ContinuousLinearMap.inCoordinates_inverse`), so their continuity
on total spaces is Tau Ceti's `TauCeti.continuous_hom_bundle_of_inCoordinates_eq_const` with
Mathlib's `Continuous.clm_bundle_apply`. The continuity of the inverse of
`twistSumCoreOptionEquiv` is proved from its chart expression, rather than by Tau Ceti's
`TauCeti.continuous_bundle_symm`, so that it needs no completeness of `𝕜`.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 1,
  §1 (the line bundles `𝒪(k)` on projective space and their tensor products).
-/

public noncomputable section

open Bundle Set Topology
open scoped Manifold ContDiff LinearAlgebra.Projectivization TensorProduct TauCeti.ModuleTopology

namespace Projectivization

section Transition

variable {K ι : Type*} [Field K]

/-- On the overlap of two standard charts, the transition function of `𝒪(k)` does not
vanish. -/
theorem twistTransition_ne_zero (k : ℤ) {i j : ι} {x : ℙ K (ι → K)} (hi : x ∈ affineOpen i)
    (hj : x ∈ affineOpen j) : twistTransition k i j x ≠ 0 := by
  rw [twistTransition_def]
  exact zpow_ne_zero _
    (div_ne_zero ((mem_affineOpen_iff i x).1 hi) ((mem_affineOpen_iff j x).1 hj))

end Transition

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}

/-- The preferred chart of `𝒪(k)` at the coordinate point `[eᵢ]` is the chart `i`, the only
standard affine open that contains `[eᵢ]`. -/
@[simp]
theorem twistCore_indexAt_mk_single (k : ℤ) (i : Fin (n + 1)) :
    (twistCore (𝕜 := 𝕜) k).indexAt (mk 𝕜 (Pi.single i 1) (by simp)) = i :=
  (mk_single_mem_affineOpen_iff _ _).1 (mem_affineOpen_twistCore_indexAt k _)

/-! ### Dehomogenized polynomials in the standard charts -/

section Dehomogenize

open MvPolynomial TauCeti

variable {d : ℕ}

/-- The dehomogenizations at `i` and at `j` of a polynomial `P`, homogeneous of degree `d`, read
in the affine charts, differ on `U_i ∩ U_j` by the transition function of `𝒪(d)`. -/
theorem eval_affineChart_dehomogenize_eq_twistTransition_mul
    {P : MvPolynomial (Fin (n + 1)) 𝕜} (hP : P.IsHomogeneous d) {i j : Fin (n + 1)}
    {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)} (hi : x ∈ affineOpen i) (hj : x ∈ affineOpen j) :
    eval (affineChart j x) (dehomogenize j P) =
      twistTransition (d : ℤ) i j x * eval (affineChart i x) (dehomogenize i P) := by
  rw [← homogeneousSection_coord hP hi, ← homogeneousSection_coord hP hj, ← mul_assoc,
    twistTransition_mul_twistTransition _ _ _ hi]

/-- At a zero `x` of a polynomial `P`, homogeneous of degree `d`, in `U_i ∩ U_j`: if the
dehomogenization of `P` at `i`, read in the affine chart at `i`, has the derivative `L` at `x`,
then the dehomogenization at `j`, read in the chart at `j`, has the derivative `L` multiplied by
the transition function `twistTransition d i j x` of `𝒪(d)`. -/
theorem _root_.HasMFDerivAt.eval_affineChart_dehomogenize {P : MvPolynomial (Fin (n + 1)) 𝕜}
    (hP : P.IsHomogeneous d) {i j : Fin (n + 1)} {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)}
    (hi : x ∈ affineOpen i) (hj : x ∈ affineOpen j)
    (hx : eval (affineChart i x) (dehomogenize i P) = 0)
    {L : TangentSpace 𝓘(𝕜, Fin n → 𝕜) x →L[𝕜] 𝕜}
    (hL : HasMFDerivAt 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜)
      (fun y ↦ eval (affineChart i y) (dehomogenize i P)) x L) :
    HasMFDerivAt 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜) (fun y ↦ eval (affineChart j y) (dehomogenize j P)) x
      (twistTransition (d : ℤ) i j x • L) := by
  have hU : affineOpen i ∩ affineOpen j ∈ 𝓝 x :=
    ((isOpen_affineOpen i).inter (isOpen_affineOpen j)).mem_nhds ⟨hi, hj⟩
  obtain ⟨T, hT⟩ : ∃ T : TangentSpace 𝓘(𝕜, Fin n → 𝕜) x →L[𝕜] 𝕜,
      HasMFDerivAt 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜) (twistTransition (d : ℤ) i j) x T :=
    ⟨_, (((contMDiffOn_twistTransition (d : ℤ) i j 1).contMDiffAt hU).mdifferentiableAt
      one_ne_zero).hasMFDerivAt⟩
  -- The product rule; the second term vanishes since `x` is a zero of `P`.
  have heq : (twistTransition (d : ℤ) i j x • L +
      eval (affineChart i x) (dehomogenize i P) • T : TangentSpace 𝓘(𝕜, Fin n → 𝕜) x →L[𝕜] 𝕜) =
      twistTransition (d : ℤ) i j x • L := by
    ext v
    simp [hx]
  refine ((hT.mul hL).congr_mfderiv heq).congr_of_eventuallyEq_abuse ?_
  filter_upwards [hU] with y hy
  exact eval_affineChart_dehomogenize_eq_twistTransition_mul hP hy.1 hy.2

/-- Read in the manifold chart at `x₀` and in the preferred trivialization of `𝒪(d)` at `x₀`, the
section `homogeneousSection d P` of a polynomial `P`, homogeneous of degree `d`, is the
dehomogenization of `P` at the index `(twistCore d).indexAt x₀` of that chart. -/
theorem trivializationAt_homogeneousSection_chartAt_symm {P : MvPolynomial (Fin (n + 1)) 𝕜}
    (hP : P.IsHomogeneous d) (x₀ : ℙ 𝕜 (Fin (n + 1) → 𝕜)) (y : Fin n → 𝕜) :
    (trivializationAt 𝕜 (twistCore (𝕜 := 𝕜) (d : ℤ)).Fiber x₀
      ⟨(chartAt (Fin n → 𝕜) x₀).symm y,
        homogeneousSection (𝕜 := 𝕜) (n := n) d P ((chartAt (Fin n → 𝕜) x₀).symm y)⟩).2 =
      eval y (dehomogenize ((twistCore (𝕜 := 𝕜) (d : ℤ)).indexAt x₀) P) := by
  rw [twistCore_trivializationAt_apply_snd,
    chartAt_eq_affineOpenPartialHomeomorph_twistCore_indexAt (d : ℤ),
    coe_affineOpenPartialHomeomorph_symm]
  set i := (twistCore (𝕜 := 𝕜) (d : ℤ)).indexAt x₀
  have ht : y ∈ (affineChart (K := 𝕜) i).target := by simp
  have hy : (affineChart (K := 𝕜) i).symm y ∈ affineOpen i :=
    affineChart_source (K := 𝕜) i ▸ (affineChart i).map_target ht
  rw [homogeneousSection_coord hP hy, (affineChart i).right_inv ht]

/-- A polynomial read in the affine chart at `i` is `C^r` on the affine open `U_i`. -/
theorem contMDiffOn_eval_affineChart (P : MvPolynomial (Fin n) 𝕜) (i : Fin (n + 1))
    (r : ℕ∞ω) :
    ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜) r (fun x ↦ eval (affineChart i x) P) (affineOpen i) :=
  (AnalyticOnNhd.eval_continuousLinearMap (ContinuousLinearMap.id 𝕜 (Fin n → 𝕜))
    P).contDiff.contMDiff.comp_contMDiffOn (contMDiffOn_affineChart i r)

end Dehomogenize

/-! ### The sums `⨁ₗ 𝒪(k l)` -/

section Sum

variable {κ : Type*} [Fintype κ]

/-- The preferred chart of `⨁ₗ 𝒪(k l)` at a point is that of every `𝒪(k')`: both are the affine
open chosen by `exists_mem_affineOpen` (Tau Ceti's `twistSumCore_indexAt` and
`twistCore_indexAt`). -/
theorem twistSumCore_indexAt_eq_twistCore_indexAt (k : κ → ℤ) (k' : ℤ)
    (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    (twistSumCore k).indexAt x = (twistCore k').indexAt x := by
  rw [twistSumCore_indexAt, twistCore_indexAt]

/-- **Sections of `⨁ₗ 𝒪(k l)` in the standard charts.** A section `s` of Tau Ceti's
`twistSumCore k` is `C^r` exactly when, for every `j`, its coordinates
`x ↦ fun l ↦ twistTransition (k l) ((twistSumCore k).indexAt x) j x * s x l` in the frame of the
chart `j` are `C^r` on the standard affine open `U_j`. -/
theorem contMDiff_section_twistSumCore_iff (k : κ → ℤ) {r : ℕ∞ω}
    (s : ∀ x : ℙ 𝕜 (Fin (n + 1) → 𝕜), (twistSumCore k).Fiber x) :
    ContMDiff 𝓘(𝕜, Fin n → 𝕜) (𝓘(𝕜, Fin n → 𝕜).prod 𝓘(𝕜, κ → 𝕜)) r
        (fun x ↦ TotalSpace.mk' (κ → 𝕜) x (s x)) ↔
      ∀ j, ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, κ → 𝕜) r
        (fun x l ↦ twistTransition (k l) ((twistSumCore k).indexAt x) j x * s x l)
        (affineOpen j) := by
  rw [VectorBundleCore.contMDiff_section_iff]
  refine forall_congr' fun j ↦ ?_
  rw [twistSumCore_baseSet]
  exact contMDiffOn_congr fun x _ ↦ funext fun l ↦
    twistSumCore_coordChange_apply k _ j x (s x) l

/-- The fibrewise splitting `⨁_{l : Option κ} 𝒪(k l) ≅ 𝒪(k none) ⊕ ⨁_{l : κ} 𝒪(k (some l))`,
which takes the `none` coordinate to the first summand and the others to the second. It is
continuous on total spaces in both directions (`continuous_twistSumCoreOptionEquiv` and
`continuous_twistSumCoreOptionEquiv_symm`). -/
def twistSumCoreOptionEquiv (k : Option κ → ℤ) (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    (twistSumCore k).Fiber x ≃L[𝕜]
      ((twistCore (k none)).Fiber ×ᵇ (twistSumCore fun l ↦ k (some l)).Fiber) x :=
  ContinuousLinearEquiv.piOptionEquivProd (M := fun _ ↦ 𝕜) 𝕜

variable (k : Option κ → ℤ)

/-- `twistSumCoreOptionEquiv` splits off the `none` coordinate. -/
@[simp]
theorem twistSumCoreOptionEquiv_apply (x : ℙ 𝕜 (Fin (n + 1) → 𝕜))
    (v : (twistSumCore k).Fiber x) :
    twistSumCoreOptionEquiv k x v = (v none, fun l ↦ v (some l)) :=
  ContinuousLinearEquiv.piOptionEquivProd_apply 𝕜 v

/-- The inverse of `twistSumCoreOptionEquiv` has the first summand as its `none` coordinate. -/
@[simp]
theorem twistSumCoreOptionEquiv_symm_apply_none (x : ℙ 𝕜 (Fin (n + 1) → 𝕜))
    (v : ((twistCore (k none)).Fiber ×ᵇ (twistSumCore fun l ↦ k (some l)).Fiber) x) :
    (twistSumCoreOptionEquiv k x).symm v none = v.1 :=
  congrFun (ContinuousLinearEquiv.piOptionEquivProd_symm_apply (M := fun _ ↦ 𝕜) 𝕜 v) none

/-- The inverse of `twistSumCoreOptionEquiv` has the second summand as its `some`
coordinates. -/
@[simp]
theorem twistSumCoreOptionEquiv_symm_apply_some (x : ℙ 𝕜 (Fin (n + 1) → 𝕜))
    (v : ((twistCore (k none)).Fiber ×ᵇ (twistSumCore fun l ↦ k (some l)).Fiber) x) (l : κ) :
    (twistSumCoreOptionEquiv k x).symm v (some l) = v.2 l :=
  congrFun (ContinuousLinearEquiv.piOptionEquivProd_symm_apply (M := fun _ ↦ 𝕜) 𝕜 v) (some l)

/-- In the trivializations at `x₀` of all three bundles, `twistSumCoreOptionEquiv` is
`ContinuousLinearEquiv.piOptionEquivProd`. -/
private theorem inCoordinates_twistSumCoreOptionEquiv (x₀ x : ℙ 𝕜 (Fin (n + 1) → 𝕜))
    (hx : x ∈ (trivializationAt (Option κ → 𝕜) (twistSumCore k).Fiber x₀).baseSet)
    (hx' : x ∈ (trivializationAt (𝕜 × (κ → 𝕜))
      ((twistCore (k none)).Fiber ×ᵇ (twistSumCore fun l ↦ k (some l)).Fiber) x₀).baseSet) :
    ContinuousLinearMap.inCoordinates (Option κ → 𝕜) (twistSumCore k).Fiber (𝕜 × (κ → 𝕜))
        ((twistCore (k none)).Fiber ×ᵇ (twistSumCore fun l ↦ k (some l)).Fiber) x₀ x x₀ x
        (twistSumCoreOptionEquiv k x : (twistSumCore k).Fiber x →L[𝕜] _) =
      (ContinuousLinearEquiv.piOptionEquivProd (ι := κ) (M := fun _ ↦ 𝕜) 𝕜 : _ →L[𝕜] _) := by
  refine ContinuousLinearMap.inCoordinates_eq_of_forall_apply hx hx' fun v ↦ ?_
  -- In both, each coordinate is read in the trivialization of its summand `𝒪(k l)`
  -- (`twistSumCore_trivializationAt_apply_snd_eq_twistCore`).
  simp only [ContinuousLinearEquiv.coe_coe]
  refine Prod.ext ?_ (funext fun l ↦ ?_) <;>
  simp only [FiberBundle.prod_trivializationAt', Trivialization.prod_apply,
    Trivialization.Prod.toFun', twistSumCoreOptionEquiv_apply,
    ContinuousLinearEquiv.piOptionEquivProd_apply]
  · exact (twistSumCore_trivializationAt_apply_snd_eq_twistCore k x₀ x _ none).symm
  · exact (twistSumCore_trivializationAt_apply_snd_eq_twistCore (fun l ↦ k (some l)) x₀ x _ l).trans
      (twistSumCore_trivializationAt_apply_snd_eq_twistCore k x₀ x _ (some l)).symm

/-- `twistSumCoreOptionEquiv` is continuous on total spaces. -/
theorem continuous_twistSumCoreOptionEquiv :
    Continuous fun p : TotalSpace (Option κ → 𝕜) (twistSumCore (𝕜 := 𝕜) (n := n) k).Fiber ↦
      TotalSpace.mk' (𝕜 × (κ → 𝕜))
        (E := (twistCore (k none)).Fiber ×ᵇ (twistSumCore fun l ↦ k (some l)).Fiber) p.proj
        (twistSumCoreOptionEquiv k p.proj p.snd) := by
  have h : Continuous fun x : ℙ 𝕜 (Fin (n + 1) → 𝕜) ↦
      TotalSpace.mk' ((Option κ → 𝕜) →L[𝕜] 𝕜 × (κ → 𝕜))
        (E := fun x ↦ (twistSumCore k).Fiber x →L[𝕜]
          ((twistCore (k none)).Fiber ×ᵇ (twistSumCore fun l ↦ k (some l)).Fiber) x) x
        (twistSumCoreOptionEquiv k x : (twistSumCore k).Fiber x →L[𝕜] _) := by
    refine TauCeti.continuous_hom_bundle_of_inCoordinates_eq_const
      (c := fun _ ↦ (ContinuousLinearEquiv.piOptionEquivProd (ι := κ) (M := fun _ ↦ 𝕜) 𝕜 :
        _ →L[𝕜] _)) ?_
    exact inCoordinates_twistSumCoreOptionEquiv k
  exact Continuous.clm_bundle_apply (F₁ := Option κ → 𝕜) (E₁ := (twistSumCore k).Fiber)
    (F₂ := 𝕜 × (κ → 𝕜))
    (E₂ := (twistCore (k none)).Fiber ×ᵇ (twistSumCore fun l ↦ k (some l)).Fiber)
    (h.comp (FiberBundle.continuous_proj _ _)) continuous_id

/-- In the trivializations at `x₀` of all three bundles, the inverse of
`twistSumCoreOptionEquiv` is the inverse of `ContinuousLinearEquiv.piOptionEquivProd`. -/
private theorem inCoordinates_twistSumCoreOptionEquiv_symm (x₀ x : ℙ 𝕜 (Fin (n + 1) → 𝕜))
    (hx : x ∈ (trivializationAt (𝕜 × (κ → 𝕜))
      ((twistCore (k none)).Fiber ×ᵇ (twistSumCore fun l ↦ k (some l)).Fiber) x₀).baseSet)
    (hx' : x ∈ (trivializationAt (Option κ → 𝕜) (twistSumCore k).Fiber x₀).baseSet) :
    ContinuousLinearMap.inCoordinates (𝕜 × (κ → 𝕜))
        ((twistCore (k none)).Fiber ×ᵇ (twistSumCore fun l ↦ k (some l)).Fiber)
        (Option κ → 𝕜) (twistSumCore k).Fiber x₀ x x₀ x
        ((twistSumCoreOptionEquiv k x).symm : _ →L[𝕜] (twistSumCore k).Fiber x) =
      ((ContinuousLinearEquiv.piOptionEquivProd (ι := κ) (M := fun _ ↦ 𝕜) 𝕜).symm : _ →L[𝕜] _) := by
  rw [← ContinuousLinearMap.inverse_equiv, ContinuousLinearMap.inCoordinates_inverse,
    inCoordinates_twistSumCoreOptionEquiv k x₀ x hx' hx, ContinuousLinearMap.inverse_equiv]

/-- The inverse of `twistSumCoreOptionEquiv` is continuous on total spaces. -/
theorem continuous_twistSumCoreOptionEquiv_symm :
    Continuous fun q : TotalSpace (𝕜 × (κ → 𝕜))
        ((twistCore (𝕜 := 𝕜) (n := n) (k none)).Fiber ×ᵇ
          (twistSumCore fun l ↦ k (some l)).Fiber) ↦
      TotalSpace.mk' (Option κ → 𝕜) (E := (twistSumCore k).Fiber) q.proj
        ((twistSumCoreOptionEquiv k q.proj).symm q.snd) := by
  have h : Continuous fun x : ℙ 𝕜 (Fin (n + 1) → 𝕜) ↦
      TotalSpace.mk' (𝕜 × (κ → 𝕜) →L[𝕜] Option κ → 𝕜)
        (E := fun x ↦ ((twistCore (k none)).Fiber ×ᵇ (twistSumCore fun l ↦ k (some l)).Fiber) x
          →L[𝕜] (twistSumCore k).Fiber x) x
        ((twistSumCoreOptionEquiv k x).symm : _ →L[𝕜] (twistSumCore k).Fiber x) := by
    refine TauCeti.continuous_hom_bundle_of_inCoordinates_eq_const
      (c := fun _ ↦ ((ContinuousLinearEquiv.piOptionEquivProd (ι := κ) (M := fun _ ↦ 𝕜) 𝕜).symm :
        _ →L[𝕜] _)) ?_
    exact inCoordinates_twistSumCoreOptionEquiv_symm k
  exact Continuous.clm_bundle_apply (F₁ := 𝕜 × (κ → 𝕜))
    (E₁ := (twistCore (k none)).Fiber ×ᵇ (twistSumCore fun l ↦ k (some l)).Fiber)
    (F₂ := Option κ → 𝕜) (E₂ := (twistSumCore k).Fiber)
    (h.comp (FiberBundle.continuous_proj _ _)) continuous_id

/-- The fibrewise isomorphism `⨁_{a : κ} 𝒪(k (e a)) ≅ ⨁_{b : κ'} 𝒪(k b)` induced by a bijection
`e : κ ≃ κ'`, which moves the coordinate at `a` to `e a`. It is continuous on total spaces
(`continuous_twistSumCoreCongr`). -/
def twistSumCoreCongr {κ' : Type*} [Fintype κ'] (k : κ' → ℤ) (e : κ ≃ κ')
    (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    (twistSumCore fun a ↦ k (e a)).Fiber x ≃L[𝕜] (twistSumCore k).Fiber x :=
  ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) e

/-- `twistSumCoreCongr k e` moves the coordinate at `a` to `e a`. -/
@[simp]
theorem twistSumCoreCongr_apply {κ' : Type*} [Fintype κ'] (k : κ' → ℤ) (e : κ ≃ κ')
    (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) (v : (twistSumCore fun a ↦ k (e a)).Fiber x) (a : κ) :
    twistSumCoreCongr k e x v (e a) = v a :=
  ContinuousLinearEquiv.piCongrLeft_apply_apply (R := 𝕜) (φ := fun _ ↦ 𝕜) e v a

/-- In the trivializations at `x₀` of both bundles, `twistSumCoreCongr k e` is
`ContinuousLinearEquiv.piCongrLeft`. -/
private theorem inCoordinates_twistSumCoreCongr {κ' : Type*} [Fintype κ'] (k : κ' → ℤ)
    (e : κ ≃ κ') (x₀ x : ℙ 𝕜 (Fin (n + 1) → 𝕜))
    (hx : x ∈ (trivializationAt (κ → 𝕜) (twistSumCore fun a ↦ k (e a)).Fiber x₀).baseSet)
    (hx' : x ∈ (trivializationAt (κ' → 𝕜) (twistSumCore k).Fiber x₀).baseSet) :
    ContinuousLinearMap.inCoordinates (κ → 𝕜) (twistSumCore fun a ↦ k (e a)).Fiber (κ' → 𝕜)
        (twistSumCore k).Fiber x₀ x x₀ x
        (twistSumCoreCongr k e x : _ →L[𝕜] (twistSumCore k).Fiber x) =
      (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) e : (κ → 𝕜) →L[𝕜] κ' → 𝕜) := by
  refine ContinuousLinearMap.inCoordinates_eq_of_forall_apply hx hx' fun v ↦ ?_
  simp only [ContinuousLinearEquiv.coe_coe]
  funext b
  obtain ⟨a, rfl⟩ := e.surjective b
  -- Each coordinate is read in the trivialization of its summand `𝒪(k (e a))`.
  refine (twistSumCore_trivializationAt_apply_snd_eq_twistCore k x₀ x _ (e a)).trans ?_
  rw [ContinuousLinearEquiv.piCongrLeft_apply_apply, twistSumCoreCongr_apply]
  exact (twistSumCore_trivializationAt_apply_snd_eq_twistCore (fun a ↦ k (e a)) x₀ x _ a).symm

/-- `twistSumCoreCongr` is continuous on total spaces: in every standard chart it is the constant
map `ContinuousLinearEquiv.piCongrLeft`, which commutes with the diagonal coordinate changes. -/
theorem continuous_twistSumCoreCongr {κ' : Type*} [Fintype κ'] (k : κ' → ℤ) (e : κ ≃ κ') :
    Continuous fun p : TotalSpace (κ → 𝕜)
        (twistSumCore (𝕜 := 𝕜) (n := n) fun a ↦ k (e a)).Fiber ↦
      TotalSpace.mk' (κ' → 𝕜) (E := (twistSumCore k).Fiber) p.proj
        (twistSumCoreCongr k e p.proj p.snd) := by
  have h : Continuous fun x : ℙ 𝕜 (Fin (n + 1) → 𝕜) ↦
      TotalSpace.mk' ((κ → 𝕜) →L[𝕜] κ' → 𝕜)
        (E := fun x ↦ (twistSumCore fun a ↦ k (e a)).Fiber x →L[𝕜] (twistSumCore k).Fiber x) x
        (twistSumCoreCongr k e x : _ →L[𝕜] (twistSumCore k).Fiber x) := by
    refine TauCeti.continuous_hom_bundle_of_inCoordinates_eq_const
      (c := fun _ ↦ (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) e :
        (κ → 𝕜) →L[𝕜] κ' → 𝕜)) ?_
    exact inCoordinates_twistSumCoreCongr k e
  exact Continuous.clm_bundle_apply (F₁ := κ → 𝕜) (E₁ := (twistSumCore fun a ↦ k (e a)).Fiber)
    (F₂ := κ' → 𝕜) (E₂ := (twistSumCore k).Fiber)
    (h.comp (FiberBundle.continuous_proj _ _)) continuous_id

end Sum

section RestrictScalars

open scoped VectorBundle.ComplexToReal

variable {κ : Type*} [Fintype κ]

/-- `⨁ₗ 𝒪(k l)` on complex projective space is a smooth real vector bundle over the underlying
real manifold. -/
instance (k : κ → ℤ) :
    ContMDiffVectorBundle ∞ (κ → ℂ) (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber 𝓘(ℝ, Fin n → ℂ) :=
  have : ContMDiffVectorBundle ∞ (κ → ℂ) (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber
      𝓘(ℂ, Fin n → ℂ) :=
    ContMDiffVectorBundle.of_le le_top
  ContMDiffVectorBundle.restrictScalars_modelWithCornersSelf ℝ this

variable (k : ℤ)

/-- `𝒪(k)` on complex projective space is a smooth real vector bundle over the underlying real
manifold. -/
instance :
    ContMDiffVectorBundle ∞ ℂ (twistCore (𝕜 := ℂ) (n := n) k).Fiber 𝓘(ℝ, Fin n → ℂ) :=
  have : ContMDiffVectorBundle ∞ ℂ (twistCore (𝕜 := ℂ) (n := n) k).Fiber 𝓘(ℂ, Fin n → ℂ) :=
    ContMDiffVectorBundle.of_le le_top
  ContMDiffVectorBundle.restrictScalars_modelWithCornersSelf ℝ this

end RestrictScalars


/-! ### `𝒪(0)` is trivial -/

/-- The bundle `𝒪(0)` is trivial: its transition functions are `1`, so its total space is the
product of projective space with `𝕜`. -/
def twistCoreZeroTrivialization :
    Trivialization 𝕜 (π 𝕜 (twistCore (𝕜 := 𝕜) (n := n) 0).Fiber) :=
  (twistCore 0).globalTrivializationOfCoordChangeEqId fun _ _ _ _ _ ↦ by simp

/-- The trivialization `twistCoreZeroTrivialization` is defined over the whole base. -/
@[simp]
theorem twistCoreZeroTrivialization_baseSet :
    (twistCoreZeroTrivialization (𝕜 := 𝕜) (n := n)).baseSet = univ :=
  VectorBundleCore.globalTrivializationOfCoordChangeEqId_baseSet _ _

/-- The trivialization `twistCoreZeroTrivialization` keeps the base point and the coordinate in
the preferred chart. -/
@[simp]
theorem twistCoreZeroTrivialization_apply
    (p : TotalSpace 𝕜 (twistCore (𝕜 := 𝕜) (n := n) 0).Fiber) :
    twistCoreZeroTrivialization p = (p.proj, p.snd) :=
  VectorBundleCore.globalTrivializationOfCoordChangeEqId_apply _ _ p

/-- The trivialization `twistCoreZeroTrivialization` is linear on fibres. -/
instance : (twistCoreZeroTrivialization (𝕜 := 𝕜) (n := n)).IsLinear 𝕜 :=
  VectorBundleCore.globalTrivializationOfCoordChangeEqId_isLinear _ _

/-! ### Tensor products -/

section Tensor

/-- The scalar cocycle of the line bundles `𝒪(k)`: the standard affine opens, with the preferred
charts of `twistCore`, and the cocycle `g i j = twistTransition 1 j i`, whose `k`-th powers are
the transition functions of `𝒪(k)` (`twistCore_eq_lineBundleCore`). -/
def twistScalarCocycle :
    SymplecticGeometry.ScalarCocycle 𝕜 (ℙ 𝕜 (Fin (n + 1) → 𝕜)) (Fin (n + 1)) where
  U := affineOpen
  isOpen_U := isOpen_affineOpen
  indexAt := (twistCore 0).indexAt
  mem_U_indexAt := mem_affineOpen_twistCore_indexAt 0
  g i j := twistTransition 1 j i
  continuousOn_g i j :=
    (contMDiffOn_twistTransition 1 j i 0).continuousOn.mono (inter_comm _ _).subset
  g_ne_zero hi hj := twistTransition_ne_zero 1 hj hi
  g_mul_g _ hj _ := twistTransition_mul_twistTransition 1 _ _ hj

@[simp]
theorem twistScalarCocycle_U :
    (twistScalarCocycle (𝕜 := 𝕜) (n := n)).U = affineOpen :=
  (rfl)

@[simp]
theorem twistScalarCocycle_indexAt (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    (twistScalarCocycle (𝕜 := 𝕜) (n := n)).indexAt x = (twistCore 0).indexAt x :=
  (rfl)

@[simp]
theorem twistScalarCocycle_g (i j : Fin (n + 1)) :
    (twistScalarCocycle (𝕜 := 𝕜) (n := n)).g i j = twistTransition 1 j i :=
  (rfl)

/-- The line bundle `𝒪(k)` is the line bundle of `twistScalarCocycle` and `k`. -/
theorem twistCore_eq_lineBundleCore (k : ℤ) :
    twistCore k = (twistScalarCocycle (𝕜 := 𝕜) (n := n)).lineBundleCore k := by
  refine VectorBundleCore.ext (funext fun i ↦ ?_) (funext fun x ↦ ?_)
    (funext fun i ↦ funext fun j ↦ funext fun x ↦ ?_)
  · rw [twistCore_baseSet, SymplecticGeometry.ScalarCocycle.lineBundleCore_baseSet,
      twistScalarCocycle_U]
  · rw [SymplecticGeometry.ScalarCocycle.lineBundleCore_indexAt, twistScalarCocycle_indexAt,
      twistCore_indexAt, twistCore_indexAt]
  · ext
    rw [twistCore_coordChange_apply,
      SymplecticGeometry.ScalarCocycle.lineBundleCore_coordChange_apply,
      twistScalarCocycle_g, twistTransition_def, twistTransition_def, zpow_one]

variable (k l : ℤ)

/-- The fibrewise isomorphism `𝒪(k + l) ≅ 𝒪(k) ⊗ 𝒪(l)`, `a ↦ a ⊗ 1` in every standard chart
(`tensorProduct_localTriv_twistCoreTensorEquiv`): the isomorphism
`ScalarCocycle.lineBundleCoreTensorEquiv` of `twistScalarCocycle`. It is continuous on total
spaces in both directions (`continuous_twistCoreTensorEquiv` and
`continuous_twistCoreTensorEquiv_symm`). -/
def twistCoreTensorEquiv (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    (twistCore (k + l)).Fiber x ≃L[𝕜] (twistCore k).Fiber x ⊗[𝕜] (twistCore l).Fiber x :=
  -- The fibres of both cores are `𝕜`, so the types agree up to unfolding `Fiber`.
  twistScalarCocycle.lineBundleCoreTensorEquiv k l x

theorem twistCoreTensorEquiv_def (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    twistCoreTensorEquiv k l x = twistScalarCocycle.lineBundleCoreTensorEquiv k l x :=
  (rfl)

/-- `twistCoreTensorEquiv` sends `v` to `v ⊗ 1`. -/
theorem twistCoreTensorEquiv_apply (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) (v : 𝕜) :
    twistCoreTensorEquiv k l x v =
      TensorProduct.tmul 𝕜 (M := (twistCore k).Fiber x) (N := (twistCore l).Fiber x) v (1 : 𝕜) := by
  rw [twistCoreTensorEquiv_def, twistCore_eq_lineBundleCore k, twistCore_eq_lineBundleCore l]
  exact twistScalarCocycle.lineBundleCoreTensorEquiv_apply k l x v

/-- The inverse of `twistCoreTensorEquiv` sends `a ⊗ b` to `a * b`. -/
theorem twistCoreTensorEquiv_symm_apply (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) (a b : 𝕜) :
    (twistCoreTensorEquiv k l x).symm
        (TensorProduct.tmul 𝕜 (M := (twistCore k).Fiber x) (N := (twistCore l).Fiber x) a b) =
      a * b := by
  rw [twistCoreTensorEquiv_def, twistCore_eq_lineBundleCore k, twistCore_eq_lineBundleCore l]
  exact twistScalarCocycle.lineBundleCoreTensorEquiv_symm_apply k l x a b

/-- **`twistCoreTensorEquiv` in a standard chart.** Over the standard affine open `U_i`, read
through the charts `i` of `𝒪(k + l)`, `𝒪(k)` and `𝒪(l)`, `twistCoreTensorEquiv` is
`a ↦ a ⊗ 1`. -/
theorem tensorProduct_localTriv_twistCoreTensorEquiv (i : Fin (n + 1))
    {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)} (hx : x ∈ affineOpen i) (v : 𝕜) :
    (Pretrivialization.tensorProduct 𝕜 ((twistCore k).localTriv i) ((twistCore l).localTriv i)
        ⟨x, twistCoreTensorEquiv k l x v⟩).2 =
      TauCeti.ProjectiveTensor.tmulL 𝕜 𝕜 𝕜 ((twistCore (k + l)).localTriv i ⟨x, v⟩).2 1 := by
  simp only [twistCoreTensorEquiv_def]
  rw [twistCore_eq_lineBundleCore k, twistCore_eq_lineBundleCore l,
    twistCore_eq_lineBundleCore (k + l)]
  exact twistScalarCocycle.tensorProduct_localTriv_lineBundleCoreTensorEquiv k l hx v

variable [CompleteSpace 𝕜]

/-- `twistCoreTensorEquiv` is continuous on total spaces. -/
theorem continuous_twistCoreTensorEquiv :
    Continuous fun p : TotalSpace 𝕜 (twistCore (𝕜 := 𝕜) (n := n) (k + l)).Fiber ↦
      TotalSpace.mk' (TauCeti.ProjectiveTensor 𝕜 𝕜 𝕜)
        (E := fun x ↦ (twistCore (𝕜 := 𝕜) (n := n) k).Fiber x ⊗[𝕜] (twistCore l).Fiber x)
        p.proj (twistCoreTensorEquiv k l p.proj p.snd) := by
  simp only [twistCoreTensorEquiv_def]
  rw [twistCore_eq_lineBundleCore k, twistCore_eq_lineBundleCore l,
    twistCore_eq_lineBundleCore (k + l)]
  exact twistScalarCocycle.continuous_lineBundleCoreTensorEquiv k l

/-- The inverse of `twistCoreTensorEquiv` is continuous on total spaces. -/
theorem continuous_twistCoreTensorEquiv_symm :
    Continuous fun q : TotalSpace (TauCeti.ProjectiveTensor 𝕜 𝕜 𝕜)
        (fun x ↦ (twistCore (𝕜 := 𝕜) (n := n) k).Fiber x ⊗[𝕜] (twistCore l).Fiber x) ↦
      TotalSpace.mk' 𝕜 (E := (twistCore (k + l)).Fiber) q.proj
        ((twistCoreTensorEquiv k l q.proj).symm q.snd) :=
  TauCeti.continuous_bundle_symm _ (continuous_twistCoreTensorEquiv k l)

end Tensor

end Projectivization

end
