/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Data.Bundle
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hom
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Prod
public import SymplecticGeometry.Topology.Algebra.Module.ComplexSmulI
public import SymplecticGeometry.Topology.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Complexification
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ComplexTangentBundle
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Topology
public import TauCeti.Topology.VectorBundle.Complex.Structure

/-!
# Complex structures on a vector bundle

Let `V` be a real vector bundle with model fibre `F` over a manifold `M`. A `Cⁿ` complex
structure on `V` (`SymplecticGeometry.Bundle.ContMDiffComplexStructure I n F V`) is a `Cⁿ`
section `J` of the endomorphism bundle of `V` with `J x ∘ J x = -1` in every fibre. For the
tangent bundle these are Tau Ceti's `TauCeti.ContMDiffAlmostComplexStructure`, and the API
here follows Tau Ceti's for that case, name for name. The proofs adapt Tau Ceti's for the tangent
bundle, in `TauCeti/Geometry/Symplectic/Manifold/AlmostComplex/ContMDiff.lean` and
`TauCeti/Geometry/Symplectic/Manifold/AlmostComplex/Topology.lean`.

## Main definitions

* `SymplecticGeometry.Bundle.ContMDiffComplexStructure`: a `Cⁿ` fibrewise complex structure.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.const`: the constant structure on a
  trivial bundle.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.pushforward`: the transport
  `Φ ∘ J ∘ Φ⁻¹` along a `Cⁿ` isomorphism of vector bundles `Φ`.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.pullback`: the structure `y ↦ J (f y)` on
  the pull-back bundle `f *ᵖ V` along a `Cⁿ` map `f`.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.prod`: the direct sum of two structures,
  on the direct-sum bundle `V₁ ×ᵇ V₂`.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.ofComplexModule`: multiplication by
  `Complex.I` on a complex vector bundle.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.toContinuousComplexStructure`: the
  underlying continuous structure, which makes `V` a complex vector bundle; for `n = 0` this is
  an equivalence (`continuousEquiv`).
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.frameTopology`: the topology induced by
  the compact-open `Cⁿ` topology on sections of the endomorphism bundle, in given frames.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.tangentEquiv`: on the tangent bundle,
  these are exactly Tau Ceti's almost complex structures
  `TauCeti.ContMDiffAlmostComplexStructure`.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.tangentHomeomorph`: for `n = ⊤`, the same
  identification with `TauCeti.SmoothAlmostComplexStructure`, as a homeomorphism of frame
  topologies.
* `TauCeti.SmoothAlmostComplexStructure.pullbackComplexStructure`: the pull-back of a smooth
  almost complex structure along a smooth map `f`, a smooth complex structure on `f *ᵖ TM`.

## Main results

* `isClosedEmbedding_toEndomorphism_frameTopology`: for covering frames, the complex structures
  form a closed subspace of the sections.
* `frameTopology_eq_of_covers`: for a locally compact model of the base, the topology does not
  depend on the covering frames.
* `toContinuousComplexStructure_tangentEquiv`: on the tangent bundle, the underlying continuous
  complex structure is the one Tau Ceti attaches to an almost complex structure.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §§3 and 14
-/

public section

noncomputable section

open _root_.Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace SymplecticGeometry.Bundle

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

variable (I) in
/-- A `Cⁿ` complex structure on the real vector bundle `V`: a `Cⁿ` section of the endomorphism
bundle of `V` whose value at every point squares to minus the identity. -/
structure ContMDiffComplexStructure (n : ℕ∞) (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F] (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
    [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle ℝ F V] where
  /-- The underlying `Cⁿ` section of the endomorphism bundle. -/
  toEndomorphism : Cₛ^n⟮I; F →L[ℝ] F, fun x ↦ V x →L[ℝ] V x⟯
  /-- The identity `J ∘ J = -1` in every fibre. -/
  square_neg : ∀ x, (toEndomorphism x).comp (toEndomorphism x) = -ContinuousLinearMap.id ℝ (V x)

namespace ContMDiffComplexStructure

variable {n m l : ℕ∞} {J K : ContMDiffComplexStructure I n F V}

/-- A complex structure is determined by its endomorphism section. -/
theorem toEndomorphism_injective : Function.Injective
    (toEndomorphism : ContMDiffComplexStructure I n F V →
      Cₛ^n⟮I; F →L[ℝ] F, fun x ↦ V x →L[ℝ] V x⟯) := by
  rintro ⟨J, hJ⟩ ⟨K, hK⟩ h
  subst h
  rfl

/-- A complex structure is applied as `J x v`. -/
instance : CoeFun (ContMDiffComplexStructure I n F V) fun _ ↦ ∀ x, V x →L[ℝ] V x :=
  ⟨fun J x ↦ J.toEndomorphism x⟩

/-- Two complex structures agree when they agree on every vector of every fibre. -/
@[ext]
theorem ext (h : ∀ (x : M) (v : V x), J x v = K x v) : J = K := by
  apply toEndomorphism_injective
  ext x v
  exact h x v

/-! ### The underlying continuous complex structure -/

/-- The underlying continuous complex structure. Its bundle
`J.toContinuousComplexStructure.Fiber` is `V` as a complex vector bundle, with `J` as
multiplication by `i`. -/
def toContinuousComplexStructure (J : ContMDiffComplexStructure I n F V) :
    TauCeti.Bundle.ContinuousComplexStructure F V where
  toFun := J
  comp_self := J.square_neg
  continuous := J.toEndomorphism.contMDiff.continuous

@[simp]
theorem toContinuousComplexStructure_apply (J : ContMDiffComplexStructure I n F V) (x : M) :
    J.toContinuousComplexStructure x = J x := (rfl)

theorem toContinuousComplexStructure_injective :
    Function.Injective (toContinuousComplexStructure : ContMDiffComplexStructure I n F V → _) :=
  fun J K h ↦ ext fun x v ↦ by
    simpa using congrArg (fun L : TauCeti.Bundle.ContinuousComplexStructure F V ↦ L x v) h

/-- Applying a complex structure twice negates a vector. -/
@[simp]
theorem apply_apply (J : ContMDiffComplexStructure I n F V) (x : M) (v : V x) :
    J x (J x v) = -v :=
  J.toContinuousComplexStructure.apply_apply x v

/-- The value of a complex structure at a point, as an almost complex structure on the
fibre. -/
def almostComplexStructureAt (J : ContMDiffComplexStructure I n F V) (x : M) :
    TauCeti.AlmostComplexStructure (V x) :=
  J.toContinuousComplexStructure.almostComplexStructureAt x

@[simp]
theorem toContinuousComplexStructure_almostComplexStructureAt
    (J : ContMDiffComplexStructure I n F V) (x : M) :
    J.toContinuousComplexStructure.almostComplexStructureAt x =
      J.almostComplexStructureAt x := (rfl)

theorem almostComplexStructureAt_toLinearMap (J : ContMDiffComplexStructure I n F V) (x : M) :
    (J.almostComplexStructureAt x).toLinearMap = (J.toEndomorphism x).toLinearMap :=
  LinearMap.ext fun v ↦ J.toContinuousComplexStructure.almostComplexStructureAt_apply x v

@[simp]
theorem almostComplexStructureAt_apply (J : ContMDiffComplexStructure I n F V) (x : M)
    (v : V x) : J.almostComplexStructureAt x v = J x v :=
  J.toContinuousComplexStructure.almostComplexStructureAt_apply x v

/-- Each fibrewise endomorphism of a complex structure is injective. -/
theorem injective (J : ContMDiffComplexStructure I n F V) (x : M) :
    Function.Injective (J x) := fun v w h ↦ by
  simpa using congrArg (J x) h

/-- Each fibrewise endomorphism of a complex structure is surjective. -/
theorem surjective (J : ContMDiffComplexStructure I n F V) (x : M) :
    Function.Surjective (J x) := fun v ↦ ⟨-J x v, by simp⟩

/-- On a bundle with nontrivial model fibre, no fibre of a complex structure is the identity:
the identity squares to itself, and `id ≠ -id` on a nonzero real vector space. -/
theorem toEndomorphism_ne_id [Nontrivial F] (J : ContMDiffComplexStructure I n F V) (x : M) :
    J.toEndomorphism x ≠ ContinuousLinearMap.id ℝ (V x) := by
  intro h
  have : Nontrivial (V x) :=
    ((trivializationAt F V x).continuousLinearEquivAt ℝ x
      (mem_baseSet_trivializationAt F V x)).toEquiv.nontrivial_congr.mpr inferInstance
  obtain ⟨v, hv⟩ := exists_ne (0 : V x)
  have hJv : J x (J x v) = -v := J.apply_apply x v
  have hxv : J x v = v := congrArg (fun A : V x →L[ℝ] V x ↦ A v) h
  rw [hxv, hxv] at hJv
  have h2 : (2 : ℝ) • v = 0 := by
    simpa [two_smul] using congrArg (v + ·) hJv
  exact hv ((smul_eq_zero.mp h2).resolve_left two_ne_zero)

/-- On a nonempty base, with nontrivial model fibre, the identity section is not the
endomorphism section of a complex structure. -/
theorem not_exists_toEndomorphism_eq_id [Nontrivial F] [Nonempty M] :
    ¬∃ J : ContMDiffComplexStructure I n F V,
      ∀ x, J.toEndomorphism x = ContinuousLinearMap.id ℝ (V x) := by
  rintro ⟨J, hJ⟩
  obtain ⟨x⟩ := ‹Nonempty M›
  exact J.toEndomorphism_ne_id x (hJ x)

/-! ### Regularity and negation -/

/-- The same complex structure, viewed at a lower regularity. -/
def ofLE (J : ContMDiffComplexStructure I n F V) (h : m ≤ n) :
    ContMDiffComplexStructure I m F V where
  toEndomorphism := ⟨J.toEndomorphism, J.toEndomorphism.contMDiff.of_le (by exact_mod_cast h)⟩
  square_neg := J.square_neg

@[simp]
theorem ofLE_toEndomorphism_apply (J : ContMDiffComplexStructure I n F V) (h : m ≤ n)
    (x : M) : (J.ofLE h).toEndomorphism x = J.toEndomorphism x := (rfl)

theorem ofLE_apply (J : ContMDiffComplexStructure I n F V) (h : m ≤ n) (x : M) (v : V x) :
    J.ofLE h x v = J x v := (rfl)

@[simp]
theorem ofLE_refl (J : ContMDiffComplexStructure I n F V) : J.ofLE le_rfl = J := by
  ext x v
  rfl

@[simp]
theorem ofLE_ofLE (J : ContMDiffComplexStructure I n F V) (h : m ≤ n) (h' : l ≤ m) :
    (J.ofLE h).ofLE h' = J.ofLE (h'.trans h) := by
  ext x v
  rfl

theorem ofLE_injective (h : m ≤ n) :
    Function.Injective (fun J : ContMDiffComplexStructure I n F V ↦ J.ofLE h) := by
  intro J K hJK
  ext x v
  exact congrArg (fun L : ContMDiffComplexStructure I m F V ↦ L x v) hJK

/-- The complex structure `-J`. -/
protected def neg (J : ContMDiffComplexStructure I n F V) : ContMDiffComplexStructure I n F V where
  toEndomorphism := -J.toEndomorphism
  square_neg x := by
    ext v
    simp

instance : Neg (ContMDiffComplexStructure I n F V) := ⟨ContMDiffComplexStructure.neg⟩

@[simp]
theorem neg_toEndomorphism (J : ContMDiffComplexStructure I n F V) :
    (-J).toEndomorphism = -J.toEndomorphism := (rfl)

/-- The value of `-J` at `x` is `-J x`. This is not a `simp` lemma: its left-hand side is
`(-J).toEndomorphism x`, which `simp` rewrites with `neg_toEndomorphism` first. -/
theorem neg_apply (J : ContMDiffComplexStructure I n F V) (x : M) : (-J) x = -J x := (rfl)

@[simp]
theorem neg_neg (J : ContMDiffComplexStructure I n F V) : -(-J) = J := by
  ext x v
  simp

@[simp]
theorem ofLE_neg (J : ContMDiffComplexStructure I n F V) (h : m ≤ n) :
    (-J).ofLE h = -(J.ofLE h) := by
  ext x v
  rfl

/-- Lowering the regularity does not change the underlying continuous complex structure. -/
@[simp]
theorem toContinuousComplexStructure_ofLE (J : ContMDiffComplexStructure I n F V) (h : m ≤ n) :
    (J.ofLE h).toContinuousComplexStructure = J.toContinuousComplexStructure :=
  TauCeti.Bundle.ContinuousComplexStructure.ext fun x v ↦ by
    rw [toContinuousComplexStructure_apply, toContinuousComplexStructure_apply, ofLE_apply]

/-! ### Continuous complex structures as structures of regularity `0` -/

/-- A continuous complex structure, as a complex structure of regularity `0`. -/
def ofContinuous (J : TauCeti.Bundle.ContinuousComplexStructure F V) :
    ContMDiffComplexStructure I 0 F V where
  toEndomorphism := ⟨J, contMDiff_zero_iff.2 J.continuous⟩
  square_neg := J.comp_self

/-- The value of `ofContinuous J` at `x` is `J x`. This is not a `simp` lemma: `simp` first
rewrites the cast `((0 : ℕ∞) : WithTop ℕ∞)` in the type of the section to `0`, after which
the left-hand side no longer matches. Use it with `rw` or `simp only`. -/
theorem ofContinuous_apply (J : TauCeti.Bundle.ContinuousComplexStructure F V) (x : M) :
    ofContinuous (I := I) J x = J x := (rfl)

@[simp]
theorem ofContinuous_toContinuousComplexStructure (J : ContMDiffComplexStructure I 0 F V) :
    ofContinuous J.toContinuousComplexStructure = J := (rfl)

@[simp]
theorem toContinuousComplexStructure_ofContinuous
    (J : TauCeti.Bundle.ContinuousComplexStructure F V) :
    (ofContinuous (I := I) J).toContinuousComplexStructure = J := (rfl)

/-- Complex structures of regularity `0` are the continuous complex structures. -/
def continuousEquiv :
    ContMDiffComplexStructure I 0 F V ≃ TauCeti.Bundle.ContinuousComplexStructure F V where
  toFun := toContinuousComplexStructure
  invFun := ofContinuous
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem continuousEquiv_apply (J : ContMDiffComplexStructure I 0 F V) :
    continuousEquiv J = J.toContinuousComplexStructure := (rfl)

@[simp]
theorem continuousEquiv_symm_apply (J : TauCeti.Bundle.ContinuousComplexStructure F V) :
    continuousEquiv.symm J = ofContinuous (I := I) J := (rfl)

/-! ### Constant structures on trivial bundles -/

section Const

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- The constant complex structure `J₀` on the trivial bundle `M × W`, for a complex structure
`J₀` on a finite-dimensional real normed space `W`. -/
def const (n : ℕ∞) (J₀ : TauCeti.AlmostComplexStructure W) :
    ContMDiffComplexStructure I n W (Bundle.Trivial M W) where
  toEndomorphism :=
    ⟨fun _ ↦ LinearMap.toContinuousLinearMap J₀.toLinearMap,
      TauCeti.contMDiff_hom_bundle_of_inCoordinates_eq_const
        (c := fun _ ↦ LinearMap.toContinuousLinearMap J₀.toLinearMap) fun _ _ _ _ ↦ by
          ext v
          simp [ContinuousLinearMap.inCoordinates]⟩
  square_neg _ := by
    ext v
    exact J₀.apply_apply v

@[simp]
theorem const_toEndomorphism_apply (n : ℕ∞) (J₀ : TauCeti.AlmostComplexStructure W) (x : M) :
    (const (I := I) (M := M) n J₀).toEndomorphism x =
      LinearMap.toContinuousLinearMap J₀.toLinearMap := (rfl)

theorem const_apply (n : ℕ∞) (J₀ : TauCeti.AlmostComplexStructure W) (x : M)
    (v : Bundle.Trivial M W x) : const (I := I) (M := M) n J₀ x v = J₀ v := (rfl)

end Const

/-! ### Transport along isomorphisms of vector bundles -/

section Pushforward

variable {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {V₁ V₂ V₃ : M → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul ℝ (V₁ x)]
  [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
  [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)] [∀ x, TopologicalSpace (V₃ x)]
  [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousSMul ℝ (V₃ x)]
  [TopologicalSpace (TotalSpace F₃ V₃)] [FiberBundle F₃ V₃] [VectorBundle ℝ F₃ V₃]
  {n : ℕ∞}

/-- The transport `Φ ∘ J ∘ Φ⁻¹` of a complex structure `J` on `V₁` along an isomorphism of
vector bundles `Φ : V₁ ≃ V₂` whose map of total spaces is `Cⁿ`. -/
def pushforward (Φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hΦ : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) n
      (fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ p.proj (Φ p.proj p.snd)))
    (J : ContMDiffComplexStructure I n F₁ V₁) : ContMDiffComplexStructure I n F₂ V₂ where
  toEndomorphism :=
    ContMDiffSection.clmComp
      ⟨fun x ↦ (Φ x : V₁ x →L[ℝ] V₂ x), (TauCeti.contMDiff_hom_bundle_iff _).2 hΦ⟩
      (J.toEndomorphism.clmComp ⟨fun x ↦ ((Φ x).symm : V₂ x →L[ℝ] V₁ x),
        contMDiff_hom_bundle_symm Φ hΦ⟩)
  square_neg x := by
    ext v
    simp

@[simp]
theorem pushforward_apply (Φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hΦ : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) n
      (fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ p.proj (Φ p.proj p.snd)))
    (J : ContMDiffComplexStructure I n F₁ V₁) (x : M) (v : V₂ x) :
    pushforward Φ hΦ J x v = Φ x (J x ((Φ x).symm v)) := by
  simp [pushforward]

@[simp]
theorem pushforward_refl
    (hΦ : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₁)) n
      (fun p : TotalSpace F₁ V₁ ↦
        TotalSpace.mk' F₁ p.proj (ContinuousLinearEquiv.refl ℝ (V₁ p.proj) p.snd)))
    (J : ContMDiffComplexStructure I n F₁ V₁) :
    pushforward (fun x ↦ ContinuousLinearEquiv.refl ℝ (V₁ x)) hΦ J = J := by
  ext x v
  simp

theorem pushforward_trans [FiniteDimensional ℝ F₂] (Φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (Ψ : ∀ x, V₂ x ≃L[ℝ] V₃ x)
    (hΦ : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) n
      (fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ p.proj (Φ p.proj p.snd)))
    (hΨ : ContMDiff (I.prod 𝓘(ℝ, F₂)) (I.prod 𝓘(ℝ, F₃)) n
      (fun p : TotalSpace F₂ V₂ ↦ TotalSpace.mk' F₃ p.proj (Ψ p.proj p.snd)))
    (hΦΨ : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₃)) n
      (fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₃ p.proj (((Φ p.proj).trans (Ψ p.proj)) p.snd)))
    (J : ContMDiffComplexStructure I n F₁ V₁) :
    pushforward (fun x ↦ (Φ x).trans (Ψ x)) hΦΨ J = pushforward Ψ hΨ (pushforward Φ hΦ J) := by
  ext x v
  simp

end Pushforward

/-! ### Pull-backs -/

section Pullback

variable {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {I' : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N] {n : ℕ∞}
  {K : Type*} [FunLike K N M] [ContinuousMapClass K N M]

/-- The pull-back of a complex structure `J` on `V` along a `Cⁿ` map `f : N → M`: the complex
structure on the pull-back bundle `f *ᵖ V` whose value at `y` is `J (f y)`. The map `f` is an
element of any type `K` of continuous maps, such as a bundled smooth map or a smooth embedding,
and the pull-back bundle carries that type's structure. -/
def pullback (J : ContMDiffComplexStructure I n F V) (f : K) (hf : ContMDiff I' I n f) :
    ContMDiffComplexStructure I' n F ((f : N → M) *ᵖ V) where
  toEndomorphism :=
    ⟨fun y ↦ J.toEndomorphism (f y), (Pullback.contMDiff_hom_section_iff f hf _).2
      (J.toEndomorphism.contMDiff.comp hf)⟩
  square_neg y := J.square_neg (f y)

theorem pullback_toEndomorphism (J : ContMDiffComplexStructure I n F V) (f : K)
    (hf : ContMDiff I' I n f) (y : N) :
    (J.pullback f hf).toEndomorphism y = J.toEndomorphism (f y) := (rfl)

/-- The pull-back at `y` sends a vector `v` of `V (f y)` to `J (f y) v`. As a `simp` lemma it
applies only to vectors of type `V (f y)`; a vector of type `(f *ᵖ V) y` stays in the pull-back
bundle, where the lemmas about the complex structure `J.pullback f hf` apply to it. -/
@[simp]
theorem pullback_apply (J : ContMDiffComplexStructure I n F V) (f : K)
    (hf : ContMDiff I' I n f) (y : N) (v : V (f y)) :
    J.pullback f hf y v = J (f y) v := (rfl)

/-- `J (f y)` applied to a vector `v` of the pull-back bundle `f *ᵖ V` at `y` is the pull-back
`J.pullback f hf` at `y` applied to `v`. This is not a `simp` lemma, since `hf` does not occur in
its left-hand side; `simp [J.apply_eq_pullback_apply f hf]` brings `J (f y)` on vectors of type
`(f *ᵖ V) y` to the pull-back, the counterpart of `pullback_apply` for them. -/
theorem apply_eq_pullback_apply (J : ContMDiffComplexStructure I n F V) (f : K)
    (hf : ContMDiff I' I n f) (y : N) (v : ((f : N → M) *ᵖ V) y) :
    J (f y) v = J.pullback f hf y v := (rfl)

/-- The pull-back at `y` acts as `J (f y)`. This is not a `simp` lemma: on vectors of type
`(f *ᵖ V) y` it would replace the pull-back by `J (f y)`, whose `simp` lemmas, such as
`apply_apply`, are stated for vectors of type `V (f y)` and do not apply to them, while
`pullback_apply` covers vectors of type `V (f y)`. -/
theorem coe_pullback (J : ContMDiffComplexStructure I n F V) (f : K)
    (hf : ContMDiff I' I n f) (y : N) :
    ⇑(J.pullback f hf y) = ⇑(J (f y)) := (rfl)

/-- With `apply_eq_pullback_apply`, `simp` applies `J (f y)` twice to a vector of the pull-back
bundle. -/
example (J : ContMDiffComplexStructure I n F V) (f : K) (hf : ContMDiff I' I n f) (y : N)
    (v : ((f : N → M) *ᵖ V) y) : J (f y) (J (f y) v) = -v := by
  simp [J.apply_eq_pullback_apply f hf]

theorem almostComplexStructureAt_pullback (J : ContMDiffComplexStructure I n F V)
    (f : K) (hf : ContMDiff I' I n f) (y : N) :
    (J.pullback f hf).almostComplexStructureAt y = J.almostComplexStructureAt (f y) :=
  TauCeti.AlmostComplexStructure.toLinearMap_injective <| by
    rw [almostComplexStructureAt_toLinearMap, almostComplexStructureAt_toLinearMap]
    rfl

/-- The almost complex structure of the pull-back at `y` acts as `J (f y)`; see `coe_pullback`. -/
@[simp]
theorem coe_almostComplexStructureAt_pullback (J : ContMDiffComplexStructure I n F V)
    (f : K) (hf : ContMDiff I' I n f) (y : N) :
    ⇑((J.pullback f hf).almostComplexStructureAt y) = ⇑(J (f y)) :=
  funext fun v ↦ almostComplexStructureAt_apply (J.pullback f hf) y v

/-- With `Bundle.Pullback.fun_eq_iff`, `simp` closes the equation of
`coe_almostComplexStructureAt_pullback`: it brings both sides to maps on `V (f y)`, while the
equation is stated between maps on `(f *ᵖ V) y`. -/
example (J : ContMDiffComplexStructure I n F V) (f : K) (hf : ContMDiff I' I n f) (y : N) :
    ⇑((J.pullback f hf).almostComplexStructureAt y) = ⇑(J (f y)) := by
  simp

/-- The pull-back of `-J` is `-(J.pullback f hf)`. This is not a `simp` lemma: it would rewrite the
left-hand side of `pullback_neg_apply`, which evaluates the pull-back of `-J` on vectors of type
`(f *ᵖ V) y`, while `pullback_apply` evaluates it on vectors of type `V (f y)`. -/
theorem pullback_neg (J : ContMDiffComplexStructure I n F V) (f : K) (hf : ContMDiff I' I n f) :
    (-J).pullback f hf = -(J.pullback f hf) := by
  ext y v
  rfl

/-- The pull-back of `-J` at `y` sends a vector `v` of `(f *ᵖ V) y` to `-(J.pullback f hf y v)`,
the negation taken in the pull-back bundle. -/
@[simp]
theorem pullback_neg_apply (J : ContMDiffComplexStructure I n F V) (f : K)
    (hf : ContMDiff I' I n f) (y : N) (v : ((f : N → M) *ᵖ V) y) :
    (-J).pullback f hf y v = -J.pullback f hf y v := (rfl)

/-- The complex bundle of the pull-back `J.pullback f hf` is the pull-back of the complex bundle of
`J`: at `y` both fibres are `V (f y)`, with `J (f y)` as multiplication by `i`, and this is the
identity of `V (f y)`, as a complex-linear equivalence. -/
def pullbackFiberEquiv (J : ContMDiffComplexStructure I n F V) (f : K)
    (hf : ContMDiff I' I n f) (y : N) :
    (J.pullback f hf).toContinuousComplexStructure.Fiber y ≃L[ℂ]
      ((f : N → M) *ᵖ J.toContinuousComplexStructure.Fiber) y :=
  -- The fibres of `(f *ᵖ J.toContinuousComplexStructure.Fiber) y` are, by definition, those of
  -- `J.toContinuousComplexStructure.Fiber (f y)`, which the closing `exact`s use.
  ContinuousLinearEquiv.complexOfMapISmul
    (W := ((f : N → M) *ᵖ J.toContinuousComplexStructure.Fiber) y)
    (((J.pullback f hf).toContinuousComplexStructure.fiberEquiv y).trans
      (J.toContinuousComplexStructure.fiberEquiv (f y)).symm) fun v ↦
    (J.toContinuousComplexStructure.fiberEquiv (f y)).injective <| by
      have h₁ := (J.pullback f hf).toContinuousComplexStructure.fiberEquiv_I_smul y v
      have h₂ (w : V (f y)) : J.toContinuousComplexStructure.fiberEquiv (f y)
          (Complex.I • (J.toContinuousComplexStructure.fiberEquiv (f y)).symm w) = J (f y) w := by
        rw [TauCeti.Bundle.ContinuousComplexStructure.fiberEquiv_I_smul,
          ContinuousLinearEquiv.apply_symm_apply, toContinuousComplexStructure_apply]
      rw [toContinuousComplexStructure_apply, coe_pullback] at h₁
      exact (((J.toContinuousComplexStructure.fiberEquiv (f y)).apply_symm_apply _).trans
        h₁).trans (h₂ _).symm

theorem pullbackFiberEquiv_apply (J : ContMDiffComplexStructure I n F V) (f : K)
    (hf : ContMDiff I' I n f) (y : N)
    (v : (J.pullback f hf).toContinuousComplexStructure.Fiber y) :
    J.pullbackFiberEquiv f hf y v = (J.toContinuousComplexStructure.fiberEquiv (f y)).symm
      ((J.pullback f hf).toContinuousComplexStructure.fiberEquiv y v) := by
  -- As in `pullbackFiberEquiv`, the `exact` reads the pull-back fibre as `V (f y)`.
  rw [pullbackFiberEquiv]
  exact congrFun (ContinuousLinearEquiv.coe_complexOfMapISmul _ _) v

/-- `pullbackFiberEquiv` is continuous on total spaces, for any complex model `G`. -/
theorem continuous_pullbackFiberEquiv [FiniteDimensional ℝ F] (G : Type*) [NormedAddCommGroup G]
    [NormedSpace ℂ G] [FiniteDimensional ℂ G] [Fact (Module.finrank ℝ F = 2 * Module.finrank ℂ G)]
    (J : ContMDiffComplexStructure I n F V) (f : K) (hf : ContMDiff I' I n f) :
    Continuous fun p : TotalSpace G (J.pullback f hf).toContinuousComplexStructure.Fiber ↦
      TotalSpace.mk' G (E := (f : N → M) *ᵖ J.toContinuousComplexStructure.Fiber) p.proj
        (J.pullbackFiberEquiv f hf p.proj p.snd) := by
  rw [(inducing_pullbackTotalSpaceEmbedding G J.toContinuousComplexStructure.Fiber
    f).continuous_iff]
  refine (FiberBundle.continuous_proj G _).prodMk <|
    ((J.toContinuousComplexStructure.totalSpaceHomeomorph G).symm.continuous.comp
      ((Pullback.continuous_lift F V f).comp
        ((J.pullback f hf).toContinuousComplexStructure.totalSpaceHomeomorph G).continuous)).congr
      fun p ↦ ?_
  rw [Function.comp_apply, Function.comp_apply,
    TauCeti.Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_apply]
  erw [Pullback.lift_mk, TauCeti.Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_symm_apply]
  simp only [pullbackFiberEquiv_apply]

end Pullback

/-! ### Direct sums -/

section Prod

variable {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₁ V₂ : M → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul ℝ (V₁ x)]
  [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
  [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  {n : ℕ∞}

/-- The direct sum of complex structures `J₁` on `V₁` and `J₂` on `V₂`: the complex structure on
the direct-sum bundle `V₁ ×ᵇ V₂` acting by `(v₁, v₂) ↦ (J₁ x v₁, J₂ x v₂)` on the fibre at `x`. -/
def prod (J₁ : ContMDiffComplexStructure I n F₁ V₁) (J₂ : ContMDiffComplexStructure I n F₂ V₂) :
    ContMDiffComplexStructure I n (F₁ × F₂) (V₁ ×ᵇ V₂) where
  toEndomorphism :=
    ⟨fun x ↦ (J₁.toEndomorphism x).prodMap (J₂.toEndomorphism x),
      (TauCeti.contMDiff_hom_bundle_iff _).2 <| by
        simpa only [ContinuousLinearMap.coe_prodMap'] using _root_.Bundle.Prod.contMDiff_prodMap
          (f₁ := fun x ↦ J₁.toEndomorphism x) (f₂ := fun x ↦ J₂.toEndomorphism x)
          ((TauCeti.contMDiff_hom_bundle_iff _).1 J₁.toEndomorphism.contMDiff)
          ((TauCeti.contMDiff_hom_bundle_iff _).1 J₂.toEndomorphism.contMDiff)⟩
  square_neg x := by
    ext v <;> simp

theorem prod_toEndomorphism (J₁ : ContMDiffComplexStructure I n F₁ V₁)
    (J₂ : ContMDiffComplexStructure I n F₂ V₂) (x : M) :
    (J₁.prod J₂).toEndomorphism x = (J₁.toEndomorphism x).prodMap (J₂.toEndomorphism x) := (rfl)

@[simp]
theorem prod_apply (J₁ : ContMDiffComplexStructure I n F₁ V₁)
    (J₂ : ContMDiffComplexStructure I n F₂ V₂) (x : M) (v : V₁ x × V₂ x) :
    J₁.prod J₂ x v = (J₁ x v.1, J₂ x v.2) := (rfl)

@[simp]
theorem almostComplexStructureAt_prod (J₁ : ContMDiffComplexStructure I n F₁ V₁)
    (J₂ : ContMDiffComplexStructure I n F₂ V₂) (x : M) :
    (J₁.prod J₂).almostComplexStructureAt x =
      (J₁.almostComplexStructureAt x).prod (J₂.almostComplexStructureAt x) :=
  TauCeti.AlmostComplexStructure.toLinearMap_injective <| LinearMap.ext fun v ↦ by
    simp [almostComplexStructureAt_toLinearMap]

@[simp]
theorem neg_prod_neg (J₁ : ContMDiffComplexStructure I n F₁ V₁)
    (J₂ : ContMDiffComplexStructure I n F₂ V₂) : (-J₁).prod (-J₂) = -(J₁.prod J₂) := by
  ext x v <;> rfl

@[simp]
theorem ofLE_prod (J₁ : ContMDiffComplexStructure I n F₁ V₁)
    (J₂ : ContMDiffComplexStructure I n F₂ V₂) {m : ℕ∞} (h : m ≤ n) :
    (J₁.prod J₂).ofLE h = (J₁.ofLE h).prod (J₂.ofLE h) := by
  ext x v <;> rfl

end Prod

/-! ### Multiplication by `Complex.I` on a complex vector bundle -/

section OfComplexModule

variable (I) in
/-- Fibrewise multiplication by `Complex.I`, as a complex structure on a complex vector bundle
`V`, viewed as a real vector bundle. Its regularity `n` is arbitrary: the section is constant in
every complex trivialization. -/
def ofComplexModule (n : ℕ∞) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedSpace ℂ F] (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    [∀ x, ContinuousConstSMul ℂ (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle ℝ F V] [VectorBundle ℂ F V] :
    ContMDiffComplexStructure I n F V where
  toEndomorphism :=
    ⟨fun x ↦ (Complex.smulIEquiv (V x) : V x →L[ℝ] V x), TauCeti.contMDiff_smulIEquiv_bundle⟩
  square_neg x := by
    ext v
    simp [smul_smul]

variable [NormedSpace ℂ F] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, ContinuousConstSMul ℂ (V x)] [VectorBundle ℂ F V]

@[simp]
theorem ofComplexModule_toEndomorphism (x : M) :
    (ofComplexModule I n F V).toEndomorphism x = (Complex.smulIEquiv (V x) : V x →L[ℝ] V x) :=
  (rfl)

theorem ofComplexModule_apply (x : M) (v : V x) :
    ofComplexModule I n F V x v = Complex.I • v :=
  Complex.smulIEquiv_apply v

/-- In each fibre, `ofComplexModule` is the almost complex structure of the complex module
`V x`. -/
@[simp]
theorem almostComplexStructureAt_ofComplexModule (x : M) :
    (ofComplexModule I n F V).almostComplexStructureAt x =
      TauCeti.AlmostComplexStructure.ofComplexModule (V x) :=
  TauCeti.AlmostComplexStructure.toLinearMap_injective <| LinearMap.ext fun v ↦ by
    simp

@[simp]
theorem ofLE_ofComplexModule {m : ℕ∞} (h : m ≤ n) :
    (ofComplexModule I n F V).ofLE h = ofComplexModule I m F V := by
  ext x v
  rfl

end OfComplexModule

/-! ### The topology on complex structures -/

section Topology

variable {n : ℕ∞} [IsManifold I n M] [ContMDiffVectorBundle n F V I]
  {ι : Type*}
  (e : ι → Trivialization (F →L[ℝ] F) (π (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- The compact-open `Cⁿ` topology on complex structures on `V`: the topology induced by the
topology `ContMDiffSection.frameTopology` of the endomorphism bundle in the frames `e` on the
sets `U`. -/
@[instance_reducible]
def frameTopology : TopologicalSpace (ContMDiffComplexStructure I n F V) :=
  .induced toEndomorphism (ContMDiffSection.frameTopology (I := I) (n := n) e U hU)

theorem frameTopology_def :
    frameTopology (I := I) (n := n) e U hU =
      (ContMDiffSection.frameTopology (I := I) (n := n) e U hU).induced
      (toEndomorphism : ContMDiffComplexStructure I n F V → _) := (rfl)

/-- The endomorphism section is an embedding for the frame topology. -/
theorem isEmbedding_toEndomorphism_frameTopology :
    let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
    let _ := frameTopology (I := I) (n := n) e U hU
    IsEmbedding (toEndomorphism : ContMDiffComplexStructure I n F V → _) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
  let _ := frameTopology (I := I) (n := n) e U hU
  exact ⟨.induced _, toEndomorphism_injective⟩

/-- A family of complex structures is continuous exactly when its family of endomorphism sections
is continuous. -/
theorem continuous_frameTopology_iff {P : Type*} [TopologicalSpace P]
    {J : P → ContMDiffComplexStructure I n F V} :
    let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
    let _ := frameTopology (I := I) (n := n) e U hU
    Continuous J ↔ Continuous (fun p ↦ (J p).toEndomorphism) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
  let _ := frameTopology (I := I) (n := n) e U hU
  exact (isEmbedding_toEndomorphism_frameTopology e U hU).isInducing.continuous_iff

/-- Complex structures converge exactly when their endomorphism sections converge. -/
theorem tendsto_frameTopology_iff {P : Type*} {l : Filter P}
    {J : P → ContMDiffComplexStructure I n F V} {J₀ : ContMDiffComplexStructure I n F V} :
    let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
    let _ := frameTopology (I := I) (n := n) e U hU
    Tendsto J l (𝓝 J₀) ↔ Tendsto (fun p ↦ (J p).toEndomorphism) l (𝓝 J₀.toEndomorphism) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
  let _ := frameTopology (I := I) (n := n) e U hU
  exact (isEmbedding_toEndomorphism_frameTopology e U hU).isInducing.tendsto_nhds_iff

/-- For a covering frame system, the value of a complex structure at a point depends
continuously on the structure. -/
theorem continuous_toEndomorphism_apply_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i) (x : M) :
    let _ := frameTopology (I := I) (n := n) e U hU
    Continuous (fun J : ContMDiffComplexStructure I n F V ↦ J.toEndomorphism x) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
  let _ := frameTopology (I := I) (n := n) e U hU
  exact (ContMDiffSection.continuous_eval_const (I := I) (n := n) e U hU hcover x).comp
    (isEmbedding_toEndomorphism_frameTopology e U hU).continuous

/-- For a covering frame system, the sections of the endomorphism bundle that square to `-1`
form a closed set, so the endomorphism section is a closed embedding. -/
theorem isClosedEmbedding_toEndomorphism_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
    let _ := frameTopology (I := I) (n := n) e U hU
    IsClosedEmbedding (toEndomorphism : ContMDiffComplexStructure I n F V → _) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
  let _ := frameTopology (I := I) (n := n) e U hU
  refine ⟨isEmbedding_toEndomorphism_frameTopology e U hU, ?_⟩
  -- The fibre `V x →L[ℝ] V x` is not normed, so the condition `J x ∘ J x = -1` is read in the
  -- trivialization of the endomorphism bundle at `x`, with values in `F →L[ℝ] F`. There, reading
  -- an endomorphism in coordinates is an algebra isomorphism, so the condition is unchanged.
  let c (x : M) : Cₛ^n⟮I; F →L[ℝ] F, fun x ↦ V x →L[ℝ] V x⟯ → (F →L[ℝ] F) := fun s ↦
    ContinuousLinearMap.inCoordinates F V F V x x x x (s x)
  have hrange : range (toEndomorphism : ContMDiffComplexStructure I n F V → _) =
      ⋂ x : M, {s | c x s * c x s = -1} := by
    ext s
    have h (x : M) : c x s * c x s = -1 ↔ s x * s x = -1 := by
      simp only [c, ContinuousLinearMap.inCoordinates_eq_conjContinuousAlgEquiv
        (mem_baseSet_trivializationAt F V x)]
      rw [← map_mul, ← map_one ((trivializationAt F V x).continuousLinearEquivAt ℝ x
        (mem_baseSet_trivializationAt F V x)).conjContinuousAlgEquiv, ← map_neg]
      exact EquivLike.apply_eq_iff_eq _
    simp only [mem_range, mem_iInter, mem_ofPred_eq, h]
    exact ⟨fun ⟨J, hJ⟩ ↦ hJ ▸ J.square_neg, fun h ↦ ⟨⟨s, h⟩, rfl⟩⟩
  rw [hrange]
  refine isClosed_iInter fun x ↦ ?_
  have hx : Continuous (c x) := by
    have h := ((trivializationAt (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x) x).continuousLinearMapAt
      ℝ x).continuous.comp
        (ContMDiffSection.continuous_eval_const (I := I) (n := n) e U hU hcover x)
    refine h.congr fun s ↦ ?_
    rw [Function.comp_apply, Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
      (e := trivializationAt (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x) x)
      (mem_baseSet_trivializationAt _ _ x), hom_trivializationAt_apply]
  exact isClosed_eq (f := fun s ↦ c x s * c x s)
    (isBoundedBilinearMap_comp.continuous.comp (hx.prodMk hx)) continuous_const

/-- A covering frame system gives a Hausdorff topology on complex structures. -/
theorem t2Space_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology (I := I) (n := n) e U hU
    T2Space (ContMDiffComplexStructure I n F V) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
  let _ := frameTopology (I := I) (n := n) e U hU
  let _ := ContMDiffSection.t2Space_frameTopology (I := I) (n := n) e U hU hcover
  exact (isEmbedding_toEndomorphism_frameTopology e U hU).t2Space

/-- For a locally compact model of the base (in particular a finite-dimensional one), the frame
topology on complex structures does not depend on the covering frames. -/
theorem frameTopology_eq_of_covers [LocallyCompactSpace EB] (hcover : ∀ x, ∃ i, x ∈ U i)
    {κ : Type*}
    (e' : κ → Trivialization (F →L[ℝ] F) (π (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x)))
    [∀ j, MemTrivializationAtlas (e' j)]
    (U' : κ → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (e' j).baseSet)
    (hcover' : ∀ x, ∃ j, x ∈ U' j) :
    frameTopology (I := I) (n := n) e U hU =
      frameTopology (I := I) (n := n) (F := F) (V := V) e' U' hU' := by
  rw [frameTopology_def, frameTopology_def,
    ContMDiffSection.frameTopology_eq_of_covers e U hU hcover e' U' hU' hcover']

/-- Negation of complex structures is continuous for the frame topology. -/
theorem continuous_neg_frameTopology :
    let _ := frameTopology (I := I) (n := n) e U hU
    Continuous (fun J : ContMDiffComplexStructure I n F V ↦ -J) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
  let _ := frameTopology (I := I) (n := n) e U hU
  let _ := ContMDiffSection.isTopologicalAddGroup_frameTopology (I := I) (n := n) e U hU
  refine (continuous_frameTopology_iff e U hU).mpr ?_
  simp only [neg_toEndomorphism]
  exact continuous_neg.comp (isEmbedding_toEndomorphism_frameTopology e U hU).continuous

end Topology

/-! ### The tangent bundle -/

section Tangent

variable [IsManifold I ∞ M] {n : ℕ∞}

/-- On the tangent bundle, complex structures of regularity `n` are Tau Ceti's almost complex
structures of regularity `n`: both consist of a `Cⁿ` section of the endomorphism bundle of `TM`
squaring to `-1`. -/
def tangentEquiv :
    ContMDiffComplexStructure I n EB (TangentSpace I : M → Type _) ≃
      TauCeti.ContMDiffAlmostComplexStructure I n M where
  toFun J := ⟨J.toEndomorphism, J.square_neg⟩
  invFun J := ⟨J.toEndomorphism, J.square_neg⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem tangentEquiv_toEndomorphism
    (J : ContMDiffComplexStructure I n EB (TangentSpace I : M → Type _)) :
    (tangentEquiv J).toEndomorphism = J.toEndomorphism := (rfl)

@[simp]
theorem tangentEquiv_symm_toEndomorphism (J : TauCeti.ContMDiffAlmostComplexStructure I n M) :
    (tangentEquiv.symm J).toEndomorphism = J.toEndomorphism := (rfl)

theorem tangentEquiv_apply (J : ContMDiffComplexStructure I n EB (TangentSpace I : M → Type _))
    (x : M) (v : TangentSpace I x) : tangentEquiv J x v = J x v := (rfl)

theorem tangentEquiv_symm_apply (J : TauCeti.ContMDiffAlmostComplexStructure I n M) (x : M)
    (v : TangentSpace I x) : tangentEquiv.symm J x v = J x v := (rfl)

/-- On the tangent bundle, the continuous complex structure of `J` is the one that Tau Ceti
attaches to the corresponding almost complex structure. -/
@[simp]
theorem toContinuousComplexStructure_tangentEquiv
    (J : ContMDiffComplexStructure I n EB (TangentSpace I : M → Type _)) :
    (tangentEquiv J).toContinuousComplexStructure = J.toContinuousComplexStructure := by
  ext x v
  simp

/-- On the tangent bundle, the continuous complex structure that Tau Ceti attaches to `J` is
that of the corresponding bundle complex structure. -/
@[simp]
theorem toContinuousComplexStructure_tangentEquiv_symm
    (J : TauCeti.ContMDiffAlmostComplexStructure I n M) :
    (tangentEquiv.symm J).toContinuousComplexStructure = J.toContinuousComplexStructure := by
  ext x v
  simp

@[simp]
theorem tangentEquiv_neg (J : ContMDiffComplexStructure I n EB (TangentSpace I : M → Type _)) :
    tangentEquiv (-J) = -tangentEquiv J := by
  ext x v
  simp

@[simp]
theorem tangentEquiv_symm_neg (J : TauCeti.ContMDiffAlmostComplexStructure I n M) :
    tangentEquiv.symm (-J) = -tangentEquiv.symm J :=
  tangentEquiv.injective <| by
    rw [tangentEquiv_neg, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

@[simp]
theorem tangentEquiv_ofLE {m : ℕ∞}
    (J : ContMDiffComplexStructure I n EB (TangentSpace I : M → Type _)) (h : m ≤ n) :
    tangentEquiv (J.ofLE h) = (tangentEquiv J).ofLE h := by
  ext x v
  simp

@[simp]
theorem almostComplexStructureAt_tangentEquiv
    (J : ContMDiffComplexStructure I n EB (TangentSpace I : M → Type _)) (x : M) :
    (tangentEquiv J).almostComplexStructureAt x = J.almostComplexStructureAt x := by
  ext v
  simp

variable {ι : Type*}
  (e : ι → Trivialization (EB →L[ℝ] EB)
    (π (EB →L[ℝ] EB) (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- On the tangent bundle, smooth complex structures and Tau Ceti's smooth almost complex
structures are homeomorphic, for the frame topologies in the same frames: the map is
`tangentEquiv` followed by `TauCeti.ContMDiffAlmostComplexStructure.smoothEquiv`. -/
def tangentHomeomorph :
    let _ := frameTopology (I := I) (n := ⊤) e U hU
    let _ := TauCeti.SmoothAlmostComplexStructure.frameTopology e U hU
    ContMDiffComplexStructure I ⊤ EB (TangentSpace I : M → Type _) ≃ₜ
      TauCeti.SmoothAlmostComplexStructure I M := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
  let _ := frameTopology (I := I) (n := ⊤) e U hU
  let _ := TauCeti.SmoothAlmostComplexStructure.frameTopology e U hU
  exact (tangentEquiv.trans
    TauCeti.ContMDiffAlmostComplexStructure.smoothEquiv).toHomeomorphOfIsInducing
    ((TauCeti.SmoothAlmostComplexStructure.isEmbedding_toEndomorphism_frameTopology
      e U hU).isInducing.of_comp_iff.mp
      (by simpa [Function.comp_def] using
        (isEmbedding_toEndomorphism_frameTopology (n := ⊤) e U hU).isInducing))

@[simp]
theorem tangentHomeomorph_apply
    (J : ContMDiffComplexStructure I ⊤ EB (TangentSpace I : M → Type _)) :
    tangentHomeomorph e U hU J = TauCeti.ContMDiffAlmostComplexStructure.smoothEquiv
      (tangentEquiv J) := (rfl)

@[simp]
theorem tangentHomeomorph_symm_apply (J : TauCeti.SmoothAlmostComplexStructure I M) :
    let _ := frameTopology (I := I) (n := ⊤) e U hU
    let _ := TauCeti.SmoothAlmostComplexStructure.frameTopology e U hU
    (tangentHomeomorph e U hU).symm J =
      tangentEquiv.symm (TauCeti.ContMDiffAlmostComplexStructure.smoothEquiv.symm J) := (rfl)

end Tangent

end ContMDiffComplexStructure

end SymplecticGeometry.Bundle

/-! ### Pull-back of an almost complex structure along a smooth map -/

namespace TauCeti.SmoothAlmostComplexStructure

open SymplecticGeometry.Bundle

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M] [IsManifold I ∞ M]
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {I' : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
  {K : Type*} [FunLike K N M] [ContinuousMapClass K N M]

@[simp]
theorem toContMDiff_neg (J : SmoothAlmostComplexStructure I M) (n : ℕ∞) :
    (-J).toContMDiff n = -J.toContMDiff n := by
  ext x v
  simp

/-- The pull-back of a smooth almost complex structure `J` on `M` along a smooth map
`f : N → M`: the smooth complex structure on the pull-back bundle `f *ᵖ TM` over `N` whose value
at `y` is `J (f y)`: the pull-back `ContMDiffComplexStructure.pullback` of the bundle complex
structure of `J` on the tangent bundle. The map `f` is an element of any type of continuous
maps, such as a bundled smooth map or a smooth embedding, and the pull-back bundle carries that
type's structure. -/
def pullbackComplexStructure (J : SmoothAlmostComplexStructure I M) (f : K)
    (hf : ContMDiff I' I ∞ f) :
    ContMDiffComplexStructure I' ⊤ EB ((f : N → M) *ᵖ (TangentSpace I)) :=
  (ContMDiffComplexStructure.tangentEquiv.symm (J.toContMDiff ⊤)).pullback f hf

theorem pullbackComplexStructure_def (J : SmoothAlmostComplexStructure I M) (f : K)
    (hf : ContMDiff I' I ∞ f) :
    J.pullbackComplexStructure f hf =
      (ContMDiffComplexStructure.tangentEquiv.symm (J.toContMDiff ⊤)).pullback f hf :=
  (rfl)

/-- The endomorphism section of the pull-back of `J` along `f` is `J` at `f y`. -/
theorem pullbackComplexStructure_toEndomorphism (J : SmoothAlmostComplexStructure I M) (f : K)
    (hf : ContMDiff I' I ∞ f) (y : N) :
    (J.pullbackComplexStructure f hf).toEndomorphism y = J.toEndomorphism (f y) := by
  rw [pullbackComplexStructure_def, ContMDiffComplexStructure.pullback_toEndomorphism,
    ContMDiffComplexStructure.tangentEquiv_symm_toEndomorphism,
    toContMDiff_toEndomorphism_apply]

/-- The pull-back of `J` along `f` acts at `y` as `J (f y)`. This is not a `simp` lemma: on
vectors of type `(f *ᵖ TM) y` it would replace the pull-back by `J (f y)`, whose `simp` lemmas
are stated for vectors of type `TangentSpace I (f y)` and do not apply to them, while
`pullbackComplexStructure_apply` covers vectors of type `TangentSpace I (f y)`. -/
theorem coe_pullbackComplexStructure (J : SmoothAlmostComplexStructure I M) (f : K)
    (hf : ContMDiff I' I ∞ f) (y : N) :
    ⇑(J.pullbackComplexStructure f hf y) = J (f y) := by
  rw [pullbackComplexStructure_def, ContMDiffComplexStructure.coe_pullback]
  ext v
  rw [ContMDiffComplexStructure.tangentEquiv_symm_apply, toContMDiff_apply]

/-- The pull-back of `J` along `f` sends a vector `v` of `TangentSpace I (f y)` to `J (f y) v`.
As a `simp` lemma it applies only to vectors of that type; for vectors of the pull-back bundle
`(f *ᵖ TM) y` see `apply_eq_pullbackComplexStructure_apply`. -/
@[simp]
theorem pullbackComplexStructure_apply (J : SmoothAlmostComplexStructure I M) (f : K)
    (hf : ContMDiff I' I ∞ f) (y : N) (v : TangentSpace I (f y)) :
    J.pullbackComplexStructure f hf y v = J (f y) v :=
  congrFun (J.coe_pullbackComplexStructure f hf y) v

/-- `J (f y)` applied to a vector `v` of the pull-back bundle `(f *ᵖ TM) y` is the pull-back of
`J` along `f` at `y` applied to `v`. This is not a `simp` lemma, since `hf` does not occur in its
left-hand side; `simp [J.apply_eq_pullbackComplexStructure_apply f hf]` brings `J (f y)` on
vectors of type `(f *ᵖ TM) y` to the pull-back, the counterpart of
`pullbackComplexStructure_apply` for them. -/
theorem apply_eq_pullbackComplexStructure_apply (J : SmoothAlmostComplexStructure I M) (f : K)
    (hf : ContMDiff I' I ∞ f) (y : N) (v : ((f : N → M) *ᵖ (TangentSpace I)) y) :
    J (f y) v = J.pullbackComplexStructure f hf y v :=
  (congrFun (J.coe_pullbackComplexStructure f hf y) v).symm

/-- With `apply_eq_pullbackComplexStructure_apply`, `simp` applies `J (f y)` twice to a vector of
the pull-back bundle. -/
example (J : SmoothAlmostComplexStructure I M) (f : K) (hf : ContMDiff I' I ∞ f) (y : N)
    (v : ((f : N → M) *ᵖ (TangentSpace I)) y) : J (f y) (J (f y) v) = -v := by
  simp [J.apply_eq_pullbackComplexStructure_apply f hf]

/-- The almost complex structure of the pull-back of `J` along `f` at `y` is that of `J` at
`f y`. -/
theorem almostComplexStructureAt_pullbackComplexStructure (J : SmoothAlmostComplexStructure I M)
    (f : K) (hf : ContMDiff I' I ∞ f) (y : N) :
    (J.pullbackComplexStructure f hf).almostComplexStructureAt y =
      J.almostComplexStructureAt (f y) := by
  rw [pullbackComplexStructure_def, ContMDiffComplexStructure.almostComplexStructureAt_pullback]
  refine AlmostComplexStructure.toLinearMap_injective ?_
  rw [ContMDiffComplexStructure.almostComplexStructureAt_toLinearMap,
    almostComplexStructureAt_toLinearMap,
    ContMDiffComplexStructure.tangentEquiv_symm_toEndomorphism, toContMDiff_toEndomorphism_apply]

/-- The almost complex structure of the pull-back of `J` along `f` at `y` acts as `J (f y)`; see
`coe_pullbackComplexStructure`. -/
@[simp]
theorem coe_almostComplexStructureAt_pullbackComplexStructure
    (J : SmoothAlmostComplexStructure I M) (f : K) (hf : ContMDiff I' I ∞ f) (y : N) :
    ⇑((J.pullbackComplexStructure f hf).almostComplexStructureAt y) = J (f y) := by
  rw [pullbackComplexStructure_def,
    ContMDiffComplexStructure.coe_almostComplexStructureAt_pullback]
  ext v
  rw [ContMDiffComplexStructure.tangentEquiv_symm_apply, toContMDiff_apply]

/-- With `Bundle.Pullback.fun_eq_iff`, `simp` closes the equation of
`coe_almostComplexStructureAt_pullbackComplexStructure`. -/
example (J : SmoothAlmostComplexStructure I M) (f : K) (hf : ContMDiff I' I ∞ f) (y : N) :
    ⇑((J.pullbackComplexStructure f hf).almostComplexStructureAt y) = J (f y) := by
  simp

/-- The pull-back of `-J` is minus the pull-back of `J`. This is not a `simp` lemma: it would
rewrite the left-hand side of `pullbackComplexStructure_neg_apply`. -/
theorem pullbackComplexStructure_neg (J : SmoothAlmostComplexStructure I M) (f : K)
    (hf : ContMDiff I' I ∞ f) :
    (-J).pullbackComplexStructure f hf = -(J.pullbackComplexStructure f hf) := by
  rw [pullbackComplexStructure_def, pullbackComplexStructure_def, toContMDiff_neg,
    ContMDiffComplexStructure.tangentEquiv_symm_neg, ContMDiffComplexStructure.pullback_neg]

/-- The pull-back of `-J` at `y` sends a vector `v` of `(f *ᵖ TM) y` to minus the pull-back of
`J` at `y` applied to `v`, the negation taken in the pull-back bundle. -/
@[simp]
theorem pullbackComplexStructure_neg_apply (J : SmoothAlmostComplexStructure I M) (f : K)
    (hf : ContMDiff I' I ∞ f) (y : N) (v : ((f : N → M) *ᵖ (TangentSpace I)) y) :
    (-J).pullbackComplexStructure f hf y v = -J.pullbackComplexStructure f hf y v := by
  rw [pullbackComplexStructure_neg, ContMDiffComplexStructure.neg_apply, _root_.neg_apply]

end TauCeti.SmoothAlmostComplexStructure

end
