/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Topology.VectorBundle.Constructions
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle
public import TauCeti.Topology.Algebra.Module.Equiv.Pi
public import TauCeti.Topology.VectorBundle.Core.Trivial
public import TauCeti.Geometry.Manifold.VectorBundle.RestrictScalars
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Core.Section
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
public import SymplecticGeometry.LinearAlgebra.Projectivization.Basic
public import SymplecticGeometry.Topology.VectorBundle.Core.Basic
public import SymplecticGeometry.Topology.VectorBundle.Core.ScalarCocycle
public import TauCeti.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.TensorProduct.Basic

import Mathlib.Analysis.Analytic.Polynomial

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
* `Projectivization.twistPiCore k ι`: the bundle `𝒪(k) ⊗ 𝕜^ι`, the direct sum of `ι` copies of
  `𝒪(k)`, as a vector bundle core with model fibre `ι → 𝕜`, with the charts of `𝒪(k)` and
  transitions `twistTransition k i j • id`. It is analytic
  (`Projectivization.isContMDiff_twistPiCore`), and a section of it is `C^r` exactly when its
  coordinates in the standard charts are (`Projectivization.contMDiff_section_twistPiCore_iff`).
  For `𝕜 = ℂ`, it is also a smooth real vector bundle over the underlying real manifold, by
  restriction of scalars (the scoped instance `VectorBundle.ComplexToReal.vectorBundle` and Tau
  Ceti's `ContMDiffVectorBundle.restrictScalars_modelWithCornersSelf`); files using its real
  structure `open scoped VectorBundle.ComplexToReal`.
* `Projectivization.twistPiCoreOptionEquiv k ι x`: the splitting
  `𝒪(k) ⊗ 𝕜^{Option ι} ≅ 𝒪(k) ⊕ (𝒪(k) ⊗ 𝕜^ι)` into Mathlib's direct sum `×ᵇ` of bundles,
  continuous on total spaces in both directions, so that, by induction on `r`, `𝒪(k)^{⊕ r}` is
  an iterated direct sum (for the Whitney formula).
* `Projectivization.twistPiCoreCongr k ι e x`: the isomorphism `𝒪(k) ⊗ 𝕜^ι ≅ 𝒪(k) ⊗ 𝕜^ι'` that
  reindexes the coordinates along `e : ι ≃ ι'`, continuous on total spaces, so that
  `Option (Fin r)` above can be read as `Fin (r + 1)`.
* `Projectivization.twistPiCoreTrivializationOfIsEmpty`: for empty `ι`, `𝒪(k) ⊗ 𝕜^ι` has rank
  zero and is trivial.
* `Projectivization.twistCore_indexAt_eq`: the preferred chart of `𝒪(k)` at a point does not
  depend on `k`.
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

The core `twistPiCore`, its base sets and its smoothness instance follow Tau Ceti's
`Projectivization.twistCore` and `Projectivization.isContMDiff_twistCore`, with the scalar
multiplication `lsmul` replaced by a scalar multiple of the identity of `ι → 𝕜`;
`contMDiff_section_twistPiCore_iff` is the case of the library's
`VectorBundleCore.contMDiff_section_iff` for this core.

The fibres of a vector bundle core are its model fibre under the name `VectorBundleCore.Fiber`,
and the body of `twistCore` is not visible here. The fibrewise maps are therefore built on the
model fibres `𝕜` and `𝕜 × (ι → 𝕜)`, and their continuity on total spaces is checked in the
preferred trivializations of the target bundles; that of the inverse of `twistPiCoreOptionEquiv`
is proved directly, so that it needs no completeness of `𝕜`.

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

/-- A point of projective space lies in the standard affine open of the preferred chart of
`𝒪(k)` at that point. -/
theorem mem_affineOpen_twistCore_indexAt (k : ℤ) (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    x ∈ affineOpen ((twistCore k).indexAt x) :=
  twistCore_baseSet (𝕜 := 𝕜) k _ ▸ (twistCore k).mem_baseSet_at x

/-- The preferred chart of `𝒪(k)` at the coordinate point `[eᵢ]` is the chart `i`, the only
standard affine open that contains `[eᵢ]`. -/
@[simp]
theorem twistCore_indexAt_mk_single (k : ℤ) (i : Fin (n + 1)) :
    (twistCore (𝕜 := 𝕜) k).indexAt (mk 𝕜 (Pi.single i 1) (by simp)) = i :=
  (mk_single_mem_affineOpen_iff _ _).1 (mem_affineOpen_twistCore_indexAt k _)

/-- The preferred chart of `𝒪(k)` at a point does not depend on `k`: it is the chart of the
manifold structure there (`chartAt_eq_affineOpenPartialHomeomorph_twistCore_indexAt`). -/
theorem twistCore_indexAt_eq (k l : ℤ) (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    (twistCore k).indexAt x = (twistCore l).indexAt x := by
  refine affineOpen_injective (K := 𝕜) ?_
  have h := congrArg (fun e : OpenPartialHomeomorph _ (Fin n → 𝕜) ↦ e.toPartialEquiv.source)
    ((chartAt_eq_affineOpenPartialHomeomorph_twistCore_indexAt k x).symm.trans
      (chartAt_eq_affineOpenPartialHomeomorph_twistCore_indexAt l x))
  simpa only [affineOpenPartialHomeomorph_toPartialEquiv,
    affineChart_source] using h

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
  rw [VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def,
    twistCore_localTriv_apply, chartAt_eq_affineOpenPartialHomeomorph_twistCore_indexAt (d : ℤ),
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

/-! ### The bundles `𝒪(k) ⊗ 𝕜^ι` -/

section Pi

/-- The vector bundle `𝒪(k) ⊗ 𝕜^ι`, that is, the direct sum of `ι` copies of `𝒪(k)`, on
projective space `ℙ 𝕜 (Fin (n + 1) → 𝕜)`, as a vector bundle core with model fibre `ι → 𝕜`. It
has the charts of `𝒪(k)`, and its coordinate change from the chart `i` to the chart `j` is
multiplication of every coordinate by `twistTransition k i j`. -/
def twistPiCore (k : ℤ) (ι : Type*) [Fintype ι] :
    VectorBundleCore 𝕜 (ℙ 𝕜 (Fin (n + 1) → 𝕜)) (ι → 𝕜) (Fin (n + 1)) where
  baseSet i := affineOpen i
  isOpen_baseSet i := isOpen_affineOpen i
  indexAt x := (twistCore (𝕜 := 𝕜) k).indexAt x
  mem_baseSet_at x := mem_affineOpen_twistCore_indexAt k x
  coordChange i j x := twistTransition k i j x • ContinuousLinearMap.id 𝕜 (ι → 𝕜)
  coordChange_self i x hx v := by simp [twistTransition_self k hx]
  continuousOn_coordChange i j :=
    (contMDiffOn_twistTransition k i j 0).continuousOn.smul continuousOn_const
  coordChange_comp i j l x hx v := by
    simp [smul_smul, mul_comm (twistTransition k i j x),
      twistTransition_mul_twistTransition k i l hx.1.2]

variable (k : ℤ) (ι : Type*) [Fintype ι]

/-- The chart `i` of `𝒪(k) ⊗ 𝕜^ι` is defined over the standard affine open `U_i`. -/
theorem twistPiCore_baseSet (i : Fin (n + 1)) :
    (twistPiCore (𝕜 := 𝕜) k ι).baseSet i = affineOpen i :=
  (rfl)

/-- The chart `i` of `𝒪(k) ⊗ 𝕜^ι` is trivial over the standard affine open `U_i`. -/
@[simp]
theorem twistPiCore_localTriv_baseSet (i : Fin (n + 1)) :
    ((twistPiCore (𝕜 := 𝕜) k ι).localTriv i).baseSet = affineOpen i :=
  (rfl)

/-- The preferred chart of `𝒪(k) ⊗ 𝕜^ι` at a point is that of `𝒪(k)`. -/
theorem twistPiCore_indexAt (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    (twistPiCore k ι).indexAt x = (twistCore k).indexAt x :=
  (rfl)

/-- The coordinate change of `𝒪(k) ⊗ 𝕜^ι` from the chart `i` to the chart `j` multiplies by the
transition function of `𝒪(k)`. -/
@[simp]
theorem twistPiCore_coordChange_apply (i j : Fin (n + 1)) (x : ℙ 𝕜 (Fin (n + 1) → 𝕜))
    (v : ι → 𝕜) : (twistPiCore k ι).coordChange i j x v = twistTransition k i j x • v :=
  (rfl)

/-- The chart `j` of `𝒪(k) ⊗ 𝕜^ι` reads a vector given in the preferred chart at its base point
through the coordinate change to the chart `j`, that is, multiplies each coordinate by
`twistTransition`. -/
theorem twistPiCore_localTriv_apply (j : Fin (n + 1))
    (p : TotalSpace (ι → 𝕜) (twistPiCore (𝕜 := 𝕜) (n := n) k ι).Fiber) :
    ((twistPiCore k ι).localTriv j p).2 =
      fun a ↦ twistTransition k ((twistCore k).indexAt p.proj) j p.proj * p.snd a :=
  (rfl)

/-- **`𝒪(k) ⊗ 𝕜^ι` is an analytic vector bundle**, as its transition functions are
analytic. -/
instance isContMDiff_twistPiCore :
    (twistPiCore (𝕜 := 𝕜) (n := n) k ι).IsContMDiff 𝓘(𝕜, Fin n → 𝕜) ω where
  contMDiffOn_coordChange i j :=
    ContMDiffOn.smul (contMDiffOn_twistTransition k i j ω) contMDiffOn_const

/-- **Sections of `𝒪(k) ⊗ 𝕜^ι` in the standard charts.** A section `s` of `𝒪(k) ⊗ 𝕜^ι` is `C^r`
exactly when, for every `j`, its coordinates
`x ↦ fun a ↦ twistTransition k ((twistCore k).indexAt x) j x * s x a` in the frame of the chart
`j` are `C^r` on the standard affine open `U_j`. -/
theorem contMDiff_section_twistPiCore_iff {r : ℕ∞ω}
    (s : ∀ x : ℙ 𝕜 (Fin (n + 1) → 𝕜), (twistPiCore k ι).Fiber x) :
    ContMDiff 𝓘(𝕜, Fin n → 𝕜) (𝓘(𝕜, Fin n → 𝕜).prod 𝓘(𝕜, ι → 𝕜)) r
        (fun x ↦ TotalSpace.mk' (ι → 𝕜) x (s x)) ↔
      ∀ j, ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, ι → 𝕜) r
        (fun x a ↦ twistTransition k ((twistCore k).indexAt x) j x * s x a) (affineOpen j) := by
  rw [VectorBundleCore.contMDiff_section_iff]
  refine forall_congr' fun j ↦ ?_
  rw [twistPiCore_baseSet]
  refine contMDiffOn_congr fun x _ ↦ funext fun a ↦ ?_
  have h := congrFun (twistPiCore_coordChange_apply k ι ((twistPiCore k ι).indexAt x) j x (s x)) a
  simp only [twistPiCore_indexAt] at h
  -- The fibre `(twistPiCore k ι).Fiber x` is `ι → 𝕜` only up to unfolding `VectorBundleCore.Fiber`,
  -- for which Mathlib states no lemma, so its scalar multiplication is evaluated by `exact`.
  exact h

/-- The fibrewise splitting `𝒪(k) ⊗ 𝕜^{Option ι} ≅ 𝒪(k) ⊕ (𝒪(k) ⊗ 𝕜^ι)`, which takes the
`none` coordinate to the first summand and the others to the second. It is continuous on total
spaces in both directions (`continuous_twistPiCoreOptionEquiv` and
`continuous_twistPiCoreOptionEquiv_symm`). -/
def twistPiCoreOptionEquiv (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    (twistPiCore k (Option ι)).Fiber x ≃L[𝕜]
      ((twistCore k).Fiber ×ᵇ (twistPiCore k ι).Fiber) x :=
  ContinuousLinearEquiv.piOptionEquivProd (M := fun _ ↦ 𝕜) 𝕜

/-- `twistPiCoreOptionEquiv` splits off the `none` coordinate. -/
@[simp]
theorem twistPiCoreOptionEquiv_apply (x : ℙ 𝕜 (Fin (n + 1) → 𝕜))
    (v : (twistPiCore k (Option ι)).Fiber x) :
    twistPiCoreOptionEquiv k ι x v = (v none, fun i ↦ v (some i)) :=
  ContinuousLinearEquiv.piOptionEquivProd_apply 𝕜 v

/-- The inverse of `twistPiCoreOptionEquiv` has the first summand as its `none` coordinate. -/
@[simp]
theorem twistPiCoreOptionEquiv_symm_apply_none (x : ℙ 𝕜 (Fin (n + 1) → 𝕜))
    (v : ((twistCore k).Fiber ×ᵇ (twistPiCore k ι).Fiber) x) :
    (twistPiCoreOptionEquiv k ι x).symm v none = v.1 :=
  congrFun (ContinuousLinearEquiv.piOptionEquivProd_symm_apply (M := fun _ ↦ 𝕜) 𝕜 v) none

/-- The inverse of `twistPiCoreOptionEquiv` has the second summand as its `some` coordinates. -/
@[simp]
theorem twistPiCoreOptionEquiv_symm_apply_some (x : ℙ 𝕜 (Fin (n + 1) → 𝕜))
    (v : ((twistCore k).Fiber ×ᵇ (twistPiCore k ι).Fiber) x) (i : ι) :
    (twistPiCoreOptionEquiv k ι x).symm v (some i) = v.2 i :=
  congrFun (ContinuousLinearEquiv.piOptionEquivProd_symm_apply (M := fun _ ↦ 𝕜) 𝕜 v) (some i)

/-- In the chart `i` of all three bundles, `twistPiCoreOptionEquiv` is
`ContinuousLinearEquiv.piOptionEquivProd`. -/
private theorem prod_localTriv_twistPiCoreOptionEquiv (i : Fin (n + 1))
    (p : TotalSpace (Option ι → 𝕜) (twistPiCore (𝕜 := 𝕜) (n := n) k (Option ι)).Fiber) :
    ((twistCore k).localTriv i).prod ((twistPiCore k ι).localTriv i)
        (TotalSpace.mk' (𝕜 × (ι → 𝕜)) (E := (twistCore k).Fiber ×ᵇ (twistPiCore k ι).Fiber)
          p.proj (twistPiCoreOptionEquiv k ι p.proj p.snd)) =
      (p.proj, ContinuousLinearEquiv.piOptionEquivProd (M := fun _ ↦ 𝕜) 𝕜
        ((twistPiCore k (Option ι)).localTriv i p).2) := by
  -- After the coordinates of `twistCore` are computed, both sides are the coordinate changes of
  -- `twistPiCore`, which are the scalar multiplications by `twistTransition`.
  ext
  · rfl
  · rw [twistPiCore_localTriv_apply]
    simp [Trivialization.Prod.toFun', twistPiCoreOptionEquiv_apply, twistCore_coordChange_apply,
      twistPiCore_indexAt]
  · rw [twistPiCore_localTriv_apply]
    simp [Trivialization.Prod.toFun', twistPiCoreOptionEquiv_apply, twistCore_coordChange_apply,
      twistPiCore_indexAt]

/-- `twistPiCoreOptionEquiv` is continuous on total spaces. -/
theorem continuous_twistPiCoreOptionEquiv :
    Continuous fun p : TotalSpace (Option ι → 𝕜)
        (twistPiCore (𝕜 := 𝕜) (n := n) k (Option ι)).Fiber ↦
      TotalSpace.mk' (𝕜 × (ι → 𝕜)) (E := (twistCore k).Fiber ×ᵇ (twistPiCore k ι).Fiber) p.proj
        (twistPiCoreOptionEquiv k ι p.proj p.snd) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj _ _).continuousAt, ?_⟩
  set i := (twistCore (𝕜 := 𝕜) (n := n) k).indexAt p₀.proj
  simp only [FiberBundle.prod_trivializationAt', VectorBundleCore.trivializationAt,
    ← VectorBundleCore.localTrivAt_def, twistPiCore_indexAt]
  simp only [prod_localTriv_twistPiCoreOptionEquiv]
  exact (ContinuousLinearEquiv.continuous _).continuousAt.comp
    (continuous_snd.continuousAt.comp
      (((twistPiCore k (Option ι)).localTriv i).continuousAt
        (((twistPiCore k (Option ι)).mem_localTriv_source (i := i) p₀).2
          (mem_affineOpen_twistCore_indexAt k p₀.proj))))

/-- In the chart `i` of all three bundles, the inverse of `twistPiCoreOptionEquiv` is the inverse
of `ContinuousLinearEquiv.piOptionEquivProd`. -/
private theorem localTriv_twistPiCoreOptionEquiv_symm (i : Fin (n + 1))
    (q : TotalSpace (𝕜 × (ι → 𝕜))
      ((twistCore (𝕜 := 𝕜) (n := n) k).Fiber ×ᵇ (twistPiCore k ι).Fiber)) :
    (twistPiCore k (Option ι)).localTriv i
        (TotalSpace.mk' (Option ι → 𝕜) (E := (twistPiCore k (Option ι)).Fiber) q.proj
          ((twistPiCoreOptionEquiv k ι q.proj).symm q.snd)) =
      (q.proj, (ContinuousLinearEquiv.piOptionEquivProd (M := fun _ ↦ 𝕜) 𝕜).symm
        (((twistCore k).localTriv i).prod ((twistPiCore k ι).localTriv i) q).2) := by
  -- As in `prod_localTriv_twistPiCoreOptionEquiv`, both sides are scalar multiplications by
  -- `twistTransition` once the coordinates of `twistCore` are computed.
  ext j
  · rfl
  · cases j
    · simp only [Trivialization.Prod.toFun', Trivialization.prod_apply,
        VectorBundleCore.localTriv_apply, ContinuousLinearEquiv.piOptionEquivProd_symm_apply]
      exact (congrArg (twistTransition k ((twistCore k).indexAt q.proj) i q.proj * ·)
        (twistPiCoreOptionEquiv_symm_apply_none k ι q.proj q.snd)).trans
          (twistCore_coordChange_apply k _ i q.proj q.snd.1).symm
    · simp only [Trivialization.Prod.toFun', Trivialization.prod_apply,
        VectorBundleCore.localTriv_apply, ContinuousLinearEquiv.piOptionEquivProd_symm_apply]
      exact congrArg (twistTransition k ((twistCore k).indexAt q.proj) i q.proj * ·)
        (twistPiCoreOptionEquiv_symm_apply_some k ι q.proj q.snd _)

/-- The inverse of `twistPiCoreOptionEquiv` is continuous on total spaces. -/
theorem continuous_twistPiCoreOptionEquiv_symm :
    Continuous fun q : TotalSpace (𝕜 × (ι → 𝕜))
        ((twistCore (𝕜 := 𝕜) (n := n) k).Fiber ×ᵇ (twistPiCore k ι).Fiber) ↦
      TotalSpace.mk' (Option ι → 𝕜) (E := (twistPiCore k (Option ι)).Fiber) q.proj
        ((twistPiCoreOptionEquiv k ι q.proj).symm q.snd) := by
  refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj _ _).continuousAt, ?_⟩
  set i := (twistCore (𝕜 := 𝕜) (n := n) k).indexAt q₀.proj
  simp only [VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def,
    twistPiCore_indexAt]
  simp only [localTriv_twistPiCoreOptionEquiv_symm]
  have hq₀ : q₀ ∈ (((twistCore (𝕜 := 𝕜) (n := n) k).localTriv i).prod
      ((twistPiCore k ι).localTriv i)).source := by
    simp [mem_affineOpen_twistCore_indexAt k q₀.proj, i]
  exact (ContinuousLinearEquiv.continuous _).continuousAt.comp
    (continuous_snd.continuousAt.comp
      ((((twistCore k).localTriv i).prod ((twistPiCore k ι).localTriv i)).continuousAt hq₀))

/-- For empty `ι`, the rank-zero bundle `𝒪(k) ⊗ 𝕜^ι` is trivial: its total space is the product
of the base with the zero-dimensional space `ι → 𝕜`. -/
def twistPiCoreTrivializationOfIsEmpty [IsEmpty ι] :
    Trivialization (ι → 𝕜) (π (ι → 𝕜) (twistPiCore (𝕜 := 𝕜) (n := n) k ι).Fiber) :=
  (twistPiCore k ι).globalTrivializationOfCoordChangeEqId fun _ _ _ _ _ ↦ Subsingleton.elim _ _

/-- The trivialization `twistPiCoreTrivializationOfIsEmpty` is defined over the whole base. -/
@[simp]
theorem twistPiCoreTrivializationOfIsEmpty_baseSet [IsEmpty ι] :
    (twistPiCoreTrivializationOfIsEmpty (𝕜 := 𝕜) (n := n) k ι).baseSet = univ :=
  VectorBundleCore.globalTrivializationOfCoordChangeEqId_baseSet _ _

/-- The trivialization `twistPiCoreTrivializationOfIsEmpty` keeps the base point and the
coordinate in the preferred chart. -/
@[simp]
theorem twistPiCoreTrivializationOfIsEmpty_apply [IsEmpty ι]
    (p : TotalSpace (ι → 𝕜) (twistPiCore (𝕜 := 𝕜) (n := n) k ι).Fiber) :
    twistPiCoreTrivializationOfIsEmpty k ι p = (p.proj, p.snd) :=
  VectorBundleCore.globalTrivializationOfCoordChangeEqId_apply _ _ p

/-- The trivialization `twistPiCoreTrivializationOfIsEmpty` is linear on fibres. -/
instance [IsEmpty ι] : (twistPiCoreTrivializationOfIsEmpty (𝕜 := 𝕜) (n := n) k ι).IsLinear 𝕜 :=
  VectorBundleCore.globalTrivializationOfCoordChangeEqId_isLinear _ _

/-- The fibrewise isomorphism `𝒪(k) ⊗ 𝕜^ι ≅ 𝒪(k) ⊗ 𝕜^ι'` induced by a bijection `e : ι ≃ ι'`,
which moves the coordinate at `a` to `e a`. It is continuous on total spaces
(`continuous_twistPiCoreCongr`). -/
def twistPiCoreCongr {ι' : Type*} [Fintype ι'] (e : ι ≃ ι') (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    (twistPiCore k ι).Fiber x ≃L[𝕜] (twistPiCore k ι').Fiber x :=
  ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) e

/-- `twistPiCoreCongr k ι e` moves the coordinate at `a` to `e a`. -/
@[simp]
theorem twistPiCoreCongr_apply {ι' : Type*} [Fintype ι'] (e : ι ≃ ι')
    (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) (v : (twistPiCore k ι).Fiber x) (a : ι) :
    twistPiCoreCongr k ι e x v (e a) = v a :=
  ContinuousLinearEquiv.piCongrLeft_apply_apply (R := 𝕜) (φ := fun _ ↦ 𝕜) e v a

/-- `twistPiCoreCongr` is continuous on total spaces: in every standard chart it is the constant
map `ContinuousLinearEquiv.piCongrLeft`, which commutes with the scalar coordinate changes. -/
theorem continuous_twistPiCoreCongr {ι' : Type*} [Fintype ι'] (e : ι ≃ ι') :
    Continuous fun p : TotalSpace (ι → 𝕜) (twistPiCore (𝕜 := 𝕜) (n := n) k ι).Fiber ↦
      TotalSpace.mk' (ι' → 𝕜) (E := (twistPiCore k ι').Fiber) p.proj
        (twistPiCoreCongr k ι e p.proj p.snd) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj _ _).continuousAt, ?_⟩
  set i := (twistCore (𝕜 := 𝕜) (n := n) k).indexAt p₀.proj
  simp only [VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def,
    twistPiCore_indexAt]
  have h (p : TotalSpace (ι → 𝕜) (twistPiCore (𝕜 := 𝕜) (n := n) k ι).Fiber) :
      ((twistPiCore k ι').localTriv i
          (TotalSpace.mk' (ι' → 𝕜) (E := (twistPiCore k ι').Fiber) p.proj
            (twistPiCoreCongr k ι e p.proj p.snd))).2 =
        ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) e ((twistPiCore k ι).localTriv i p).2 := by
    rw [twistPiCore_localTriv_apply, twistPiCore_localTriv_apply]
    exact (map_smul (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) e) _ p.snd).symm
  refine ContinuousAt.congr ?_ (Filter.Eventually.of_forall fun p ↦ (h p).symm)
  exact (ContinuousLinearEquiv.continuous _).continuousAt.comp
    (continuous_snd.continuousAt.comp
      (((twistPiCore k ι).localTriv i).continuousAt
        (((twistPiCore k ι).mem_localTriv_source (i := i) p₀).2
          (mem_affineOpen_twistCore_indexAt k p₀.proj))))

end Pi

section RestrictScalars

open scoped VectorBundle.ComplexToReal

variable (k : ℤ) (ι : Type*) [Fintype ι]

/-- `𝒪(k) ⊗ ℂ^ι` on complex projective space is a smooth real vector bundle over the underlying
real manifold. -/
instance :
    ContMDiffVectorBundle ∞ (ι → ℂ) (twistPiCore (𝕜 := ℂ) (n := n) k ι).Fiber 𝓘(ℝ, Fin n → ℂ) :=
  have : ContMDiffVectorBundle ∞ (ι → ℂ) (twistPiCore (𝕜 := ℂ) (n := n) k ι).Fiber
      𝓘(ℂ, Fin n → ℂ) :=
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
      twistCore_indexAt_eq k 0]
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
