/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
public import TauCeti.Geometry.Manifold.Orientation.Preserving
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Wedge.Basic

/-!
# Naturality of the fibre integral on a product, the projection formula, fibrewise invariance

How the fibre integral `SymplecticGeometry.prodFiberIntegral o` over a compact oriented `F` meets
pull-backs along maps of the base. For a map `f : B' → B`, the product map `Prod.map f id` sends
the lift `(v, 0)` of a base vector to the lift `(df v, 0)` and fixes the vertical vectors
`(0, w)`, so the integrand of the pull-back of `α` at `b'` is the integrand of `α` at `f b'` on
the vectors `df v`. Integrating over `F` gives that the fibre integral commutes with pull-back.

With `f` the inclusion of an open subset `U` of `B` (`U` as a manifold, `f = Subtype.val`), this
says that the fibre integral of the restriction of `α` to `U × F` is the restriction of the
fibre integral of `α` to `U`.

For a form `β` on `B`, the pull-back `Prod.fst^* β` vanishes as soon as one of its arguments is a
vertical vector `(0, w)`. So on the lifts `(v, 0)` followed by vertical vectors, the shuffle sum
of `Prod.fst^* β ∧ α` keeps only the shuffles that hand base vectors to `β`
(`ContinuousAlternatingMap.pairedWedge_apply_append_eq_sum_of_forall`), and the integrand of the
wedge at `b` is a shuffle sum of integrands of `α` with coefficients from `β` at `b`. Integrating
over `F` term by term gives the projection formula
`∫_F Prod.fst^* β ∧ α = β ∧ ∫_F α`, with no sign since the base vectors come first.

Let `Φ : B × F → B × F` satisfy `Prod.fst ∘ Φ = Prod.fst`, so that it maps each fibre `{b} × F`
to itself by its slice `y ↦ (Φ (b, y)).2`. Its derivative fixes the base component of a tangent
vector, so it sends the lift `(v, 0)` to `(v, 0)` plus a vertical vector, and a vertical vector
`(0, w)` to `(0, w')`, `w'` the image of `w` under the derivative of the slice. An alternating map
of `r + m` vectors does not see vertical vectors added to its first `r` arguments when its last
`m` are vertical, since the vertical space has dimension `m`
(`ContinuousAlternatingMap.map_append_add_of_mem`). So the integrand of the pull-back of `α`
along `Φ` at `b` is the pull-back of the integrand of `α` along the slice. When the slices are
orientation-preserving diffeomorphisms, change of variables over `F`
(`Topology.IsOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt`) shows that
the fibre integral is invariant under `Φ`. The slice hypothesis is stated by membership in
`Diffeomorph.orientationPreservingSubgroup`, as the coordinate changes of an oriented atlas give
it.

## Main results

* `SymplecticGeometry.prodFiberIntegrand_mpullback_prodMap`: the integrand of the pull-back of `α`
  along `Prod.map f id` at `b'` on `v` is that of `α` at `f b'` on `df v`.
* `SymplecticGeometry.prodFiberIntegral_mpullback_prodMap`: for smooth `f : B' → B`, the fibre
  integral of the pull-back of `α` along `Prod.map f id` is the pull-back along `f` of the fibre
  integral of `α`.
* `SymplecticGeometry.prodFiberIntegrand_wedge_mpullback_fst`: the integrand of
  `Prod.fst^* β ∧ α` at `b` on `v` as a shuffle sum of integrands of `α`.
* `SymplecticGeometry.prodFiberIntegral_wedge_mpullback_fst`: the projection formula, the fibre
  integral of `Prod.fst^* β ∧ α` is `β ∧ prodFiberIntegral o α`.
* `SymplecticGeometry.prodFiberIntegrand_mpullback_of_fst_eq`: for `Φ` over the identity of `B`,
  the integrand of the pull-back of `α` along `Φ` at `b` is the pull-back of that of `α` along the
  slice of `Φ` over `b`.
* `SymplecticGeometry.prodFiberIntegral_mpullback_of_fst_eq`: the fibre integral is invariant
  under smooth maps over the identity of `B` whose slices are orientation-preserving
  diffeomorphisms.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6.
-/

public section

noncomputable section

open Function
open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

variable {E H E' H' E'' H'' B F B' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace F] [ChartedSpace H' F]
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {I' : ModelWithCorners ℝ E'' H''} [TopologicalSpace B'] [ChartedSpace H'' B'] {r m : ℕ}

/-- **The integrand of a pull-back along a map of the base.** For `f : B' → B` differentiable at
`b`, the integrand at `b` on `v` of the pull-back of `α` along `Prod.map f id` is the integrand of
`α` at `f b` on the vectors `df v`. -/
theorem prodFiberIntegrand_mpullback_prodMap {f : B' → B} {b : B'}
    (hf : MDifferentiableAt I' I f b) (α : RoughForm (I.prod J) (B × F) ℝ (r + m))
    (v : Fin r → TangentSpace I' b) :
    prodFiberIntegrand (mpullback (I'.prod J) (I.prod J) (Prod.map f id) α) b v =
      prodFiberIntegrand α (f b) fun i ↦ mfderiv I' I f b (v i) := by
  funext y
  ext w
  rw [prodFiberIntegrand_apply, prodFiberIntegrand_apply, mpullback_apply]
  congr 1
  funext p
  rw [Manifold.mfderiv_prodMap_apply (p := (b, y)) hf mdifferentiableAt_id]
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) p <;>
    simp only [Fin.append_left, Fin.append_right, mfderiv_id, ContinuousLinearMap.id_apply,
      map_zero, id_eq]

/-- **The integrand of a wedge with a form from the base.** For a form `β` of degree `p` on `B`
and a form `α` of degree `q + m` on `B × F`, the integrand at `b` on `v` of
`Prod.fst^* β ∧ α`, read in degree `(p + q) + m`, is the shuffle sum over `v` of the integrands
of `α`: `∑ σ, (p! q!)⁻¹ sign σ β_b(v_{σ(1)}, …, v_{σ(p)}) •
prodFiberIntegrand α b (v_{σ(p+1)}, …, v_{σ(p+q)})`. -/
theorem prodFiberIntegrand_wedge_mpullback_fst [IsManifold I 1 B] [IsManifold J 1 F] {p q : ℕ}
    (β : SmoothForm I B ℝ p) (α : SmoothForm (I.prod J) (B × F) ℝ (q + m)) (b : B)
    (v : Fin (p + q) → TangentSpace I b) :
    prodFiberIntegrand (LinearEquiv.cast (R := ℝ)
      (M := fun k ↦ SmoothForm (I.prod J) (B × F) ℝ k) (Nat.add_assoc p q m).symm
        (SmoothForm.wedge (SmoothForm.mpullback Prod.fst contMDiff_fst β) α)).val b v =
      ∑ σ : Equiv.Perm (Fin (p + q)),
        (((p.factorial : ℝ) * (q.factorial : ℝ))⁻¹ * (Equiv.Perm.sign σ : ℝ) *
          β.val b fun i ↦ v (σ (Fin.castAdd q i))) •
            prodFiberIntegrand α.val b fun j ↦ v (σ (Fin.natAdd p j)) := by
  funext y
  ext w
  rw [prodFiberIntegrand_apply, SmoothForm.cast_apply, SmoothForm.coe_wedge,
    RoughForm.wedge_def, RoughForm.wedgeWith_apply']
  set e := Manifold.tangentSpaceProdEquiv (I := I) (J := J) (b, y)
  have happ {n : ℕ} (u : Fin n → TangentSpace I b) :
      (fun s ↦ e.symm (Fin.append (fun i ↦ (u i, 0)) (fun j ↦ (0, w j)) s)) =
        Fin.append (fun i ↦ e.symm (u i, 0)) (fun j ↦ e.symm (0, w j)) := by
    funext s
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) s <;> simp
  have hfst (x : TangentSpace I b × TangentSpace J y) :
      mfderiv (I.prod J) I Prod.fst (b, y) (e.symm x) = x.1 := by
    rw [TauCeti.mfderiv_fst_apply, Manifold.tangentSpaceProdEquiv_symm_apply]
  have hφ (z : Fin p → TangentSpace (I.prod J) (b, y)) (i : Fin p) (j : Fin m)
      (hz : z i = e.symm (0, w j)) :
      (SmoothForm.mpullback Prod.fst contMDiff_fst β).val (b, y) z = 0 := by
    rw [SmoothForm.coe_mpullback, mpullback_apply]
    exact (β.val b).map_coord_zero i (by rw [hz, hfst])
  rw [happ, Function.comp_def,
    ContinuousAlternatingMap.pairedWedge_apply_append_eq_sum_of_forall _ _ _ _ _ _ hφ]
  simp only [Finset.sum_apply, ContinuousAlternatingMap.sum_apply, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [prodFiberIntegrand_apply, happ, SmoothForm.coe_mpullback, mpullback_apply]
  simp only [hfst, ContinuousLinearMap.mul_apply', Units.smul_def, zsmul_eq_mul, smul_eq_mul]
  ring

/-- **The integrand of a pull-back along a fibrewise map.** Let `Φ : B × F → B × F` cover the
identity of `B`, `Prod.fst ∘ Φ = Prod.fst`, and be differentiable at each point of the fibre over
`b`, and let the tangent spaces of `F` have dimension at most `m`. Then the integrand at `b` on
`v` of the pull-back of `α` along `Φ` is the pull-back of the integrand of `α` at `b` on `v`
along the slice `y ↦ (Φ (b, y)).2`. -/
theorem prodFiberIntegrand_mpullback_of_fst_eq [FiniteDimensional ℝ E'] {Φ : B × F → B × F}
    (hfst : Prod.fst ∘ Φ = Prod.fst) {b : B}
    (hd : ∀ y, MDifferentiableAt (I.prod J) (I.prod J) Φ (b, y))
    (hm : Module.finrank ℝ E' ≤ m) (α : RoughForm (I.prod J) (B × F) ℝ (r + m))
    (v : Fin r → TangentSpace I b) :
    prodFiberIntegrand (mpullback (I.prod J) (I.prod J) Φ α) b v =
      mpullback J J (fun y ↦ (Φ (b, y)).2) (prodFiberIntegrand α b v) := by
  funext y
  ext w
  have hpt : Φ (b, y) = (b, (Φ (b, y)).2) := Prod.ext (congrFun hfst (b, y)) rfl
  -- `dΦ` keeps the base component of a vector, and on a vertical vector `(0, w)` it is the
  -- derivative of the slice on `w`.
  have h1 (x : TangentSpace (I.prod J) (b, y)) :
      (mfderiv (I.prod J) (I.prod J) Φ (b, y) x).1 = x.1 := by
    have h := mfderiv_comp_apply (I' := I.prod J) (I'' := I) (b, y) mdifferentiableAt_fst (hd y) x
    rw [mfderiv_fst_apply, hfst, mfderiv_fst_apply] at h
    exact h.symm
  have h2 (w : TangentSpace J y) : (mfderiv (I.prod J) (I.prod J) Φ (b, y) (0, w)).2 =
      mfderiv J J (fun y ↦ (Φ (b, y)).2) y w :=
    ((hd y).mfderiv_snd_apply _).symm.trans
      (MDifferentiableAt.mfderiv_uncurry_apply_zero_mk (f := fun b y ↦ (Φ (b, y)).2)
        (hd y).snd w)
  rw [prodFiberIntegrand_apply, mpullback_apply, mpullback_apply, prodFiberIntegrand_apply]
  -- The vertical vectors at `Φ (b, y)` form a subspace of dimension at most `m`.
  let V : Submodule ℝ (TangentSpace (I.prod J) (Φ (b, y))) :=
    LinearMap.range (LinearMap.inr ℝ E E')
  have hV : Module.finrank ℝ V ≤ m := (LinearMap.finrank_range_le _).trans hm
  have : Module.Finite ℝ V := LinearMap.finiteDimensional_range _
  have hvec : (fun p ↦ mfderiv (I.prod J) (I.prod J) Φ (b, y)
      ((Manifold.tangentSpaceProdEquiv (b, y)).symm
        (Fin.append (fun i ↦ (v i, 0)) (fun j ↦ (0, w j)) p))) =
      Fin.append ((fun i ↦ ((v i, 0) : E × E')) +
          fun i ↦ (0, (mfderiv (I.prod J) (I.prod J) Φ (b, y) (v i, 0)).2))
        (fun j ↦ ((0, mfderiv J J (fun y ↦ (Φ (b, y)).2) y (w j)) : E × E')) := by
    funext p
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) p <;>
      simp only [Fin.append_left, Fin.append_right] <;>
      rw [Manifold.tangentSpaceProdEquiv_symm_apply] <;>
      refine Prod.ext ?_ ?_
    all_goals first
      | exact (h1 _).trans (add_zero _).symm
      | exact (zero_add _).symm
      | exact h1 _
      | exact h2 _
  have hu (i : Fin r) :
      ((0, (mfderiv (I.prod J) (I.prod J) Φ (b, y) (v i, 0)).2) : E × E') ∈ V := ⟨_, rfl⟩
  have hw (j : Fin m) :
      ((0, mfderiv J J (fun y ↦ (Φ (b, y)).2) y (w j)) : E × E') ∈ V := ⟨_, rfl⟩
  rw [hvec]
  -- The vertical parts of the images of the lifts `(v i, 0)` do not change the value.
  refine (ContinuousAlternatingMap.map_append_add_of_mem (α (Φ (b, y))) hV _ hu hw).trans ?_
  rw [← hpt]
  simp only [Manifold.tangentSpaceProdEquiv_symm_apply]
  -- The two sides differ by an eta-expansion.
  rfl

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [FiniteDimensional ℝ E'']
  [IsManifold I ∞ B] [IsManifold J ∞ F] [IsManifold I' ∞ B'] [CompactSpace F] [T2Space F]

section Boundaryless

variable [I.Boundaryless] [I'.Boundaryless]

/-- **The fibre integral commutes with pull-back along maps of the base.** For a smooth map
`f : B' → B` and a smooth form `α` of degree `r + m` on `B × F`, the fibre integral of the
pull-back of `α` along `Prod.map f id : B' × F → B × F` is the pull-back along `f` of the fibre
integral of `α`. For the inclusion of an open subset of `B`, this is the restriction of the fibre
integral to that subset. -/
theorem prodFiberIntegral_mpullback_prodMap (o : Manifold.Orientation J F (Fin m)) {f : B' → B}
    (hf : ContMDiff I' I ∞ f) (α : SmoothForm (I.prod J) (B × F) ℝ (r + m)) :
    prodFiberIntegral o (SmoothForm.mpullback (Prod.map f id) (hf.prodMap contMDiff_id) α) =
      SmoothForm.mpullback f hf (prodFiberIntegral o α) :=
  SmoothBundleForm.ext fun b v ↦ by
    rw [prodFiberIntegral_apply, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback,
      mpullback_apply, prodFiberIntegral_apply,
      prodFiberIntegrand_mpullback_prodMap ((hf b).mdifferentiableAt (by simp))]

/-- **The projection formula on a product.** For a smooth form `β` of degree `p` on `B` and a
smooth form `α` of degree `q + m` on `B × F`, the fibre integral of `Prod.fst^* β ∧ α`, read in
degree `(p + q) + m`, is `β ∧ prodFiberIntegral o α`. -/
theorem prodFiberIntegral_wedge_mpullback_fst {p q : ℕ} (o : Manifold.Orientation J F (Fin m))
    (β : SmoothForm I B ℝ p) (α : SmoothForm (I.prod J) (B × F) ℝ (q + m)) :
    prodFiberIntegral o (LinearEquiv.cast (R := ℝ)
      (M := fun k ↦ SmoothForm (I.prod J) (B × F) ℝ k) (Nat.add_assoc p q m).symm
        (SmoothForm.wedge (SmoothForm.mpullback Prod.fst contMDiff_fst β) α)) =
      SmoothForm.wedge β (prodFiberIntegral o α) :=
  SmoothBundleForm.ext fun b v ↦ by
    have hint (u : Fin q → TangentSpace I b) (c : ℝ) :
        IntegrableTopForm (c • prodFiberIntegrand α.val b u) :=
      ((isSmoothForm_prodFiberIntegrand α.isSmoothForm b u).smul c).integrableTopForm
        (isClosed_tsupport _).isCompact
        (Module.finBasisOfFinrankEq ℝ E' (by simpa using o.card_eq.symm))
    rw [prodFiberIntegral_apply, prodFiberIntegrand_wedge_mpullback_fst,
      integralTopForm_sum o _ _ fun σ _ ↦ hint _ _, SmoothForm.wedge_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [integralTopForm_smul, prodFiberIntegral_apply]
    simp only [Units.smul_def, zsmul_eq_mul, smul_eq_mul]
    ring

end Boundaryless

variable [BoundarylessManifold I B]

/-- **Invariance under fibrewise orientation-preserving diffeomorphisms.** Let
`Φ : B × F → B × F` be smooth and cover the identity of `B`, `Prod.fst ∘ Φ = Prod.fst`, and let
each slice `y ↦ (Φ (b, y)).2` be a diffeomorphism of `F` that preserves `o` at every point.
Then the fibre integral of the pull-back of `α` along `Φ` is the fibre integral of `α`. -/
theorem prodFiberIntegral_mpullback_of_fst_eq (o : Manifold.Orientation J F (Fin m))
    {Φ : B × F → B × F} (hΦ : ContMDiff (I.prod J) (I.prod J) ∞ Φ)
    (hfst : Prod.fst ∘ Φ = Prod.fst) {n : ℕ∞ω} {hn : n ≠ 0}
    (ho : ∀ b, ∃ φ ∈ Diffeomorph.orientationPreservingSubgroup hn o,
      ⇑φ = fun y ↦ (Φ (b, y)).2)
    (α : SmoothForm (I.prod J) (B × F) ℝ (r + m)) :
    prodFiberIntegral o (SmoothForm.mpullback Φ hΦ α) = prodFiberIntegral o α :=
  SmoothBundleForm.ext fun b v ↦ by
    obtain ⟨φ, hφ, hφΦ⟩ := ho b
    rw [prodFiberIntegral_apply, prodFiberIntegral_apply, SmoothForm.coe_mpullback,
      prodFiberIntegrand_mpullback_of_fst_eq hfst
        (fun y ↦ (hΦ (b, y)).mdifferentiableAt (by simp)) (by simpa using o.card_eq.symm.le),
      ← hφΦ]
    exact φ.toHomeomorph.isOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt
      (Diffeomorph.mem_orientationPreservingSubgroup_iff.mp hφ) (by simp)

end SymplecticGeometry
