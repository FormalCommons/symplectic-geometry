/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.Restrict
public import TauCeti.Geometry.Manifold.RegularValue.Level
public import TauCeti.Topology.Algebra.ProperAction.Basic
public import TauCeti.Geometry.Manifold.FiberBundle.Principal.Quotient

/-!
# The circle bundle of a regular level

Let a commutative Lie group `G`, such as `Circle`, act smoothly on a boundaryless manifold `M`,
and let `f : M → F` be a smooth `G`-invariant map with regular value `c`. The level
`{x // f x = c}` carries Tau Ceti's atlas `TauCeti.regularLevelChartedSpace`. This file restricts
the action to the level by inverses, `g` acting as `x ↦ g⁻¹ • x`, which is an action because `G`
is commutative (`SymplecticGeometry.levelInvMulAction`). Tau Ceti's bundle of orbits
`TauCeti.orbitRelFiber` of a left action acts on the right by `x · g = g⁻¹ • x`; for the action by
inverses this right action is `x · g = g • x`, the action of `G` on `M`, which is the convention of
`Geometry/Symplectic/Coupling/`. The restricted action is

* smooth for the regular-level atlas (`SymplecticGeometry.contMDiffSMul_levelInvMulAction`), as
  the inclusion of the level is a smooth embedding
  (`TauCeti.isSmoothEmbedding_coe_regularLevel`), by
  `Manifold.IsSmoothEmbedding.contMDiffSMul`;
* free when `G` acts freely at the points of the level
  (`SymplecticGeometry.isCancelSMul_levelInvMulAction`);
* proper when `G` is compact and `M` Hausdorff (`TauCeti.properSMul_of_compactSpace`).

These are the hypotheses of Tau Ceti's `TauCeti/Geometry/Manifold/FiberBundle/Principal/Quotient`,
so the orbits of the level form a smooth principal `G`-bundle `orbitRelFiber G {x // f x = c}`
over the orbit space (`ProperSMul.orbitRelFiberBundle`, `ProperSMul.principalBundle_orbitRelFiber`,
`ProperSMul.contMDiffFiberBundle_orbitRelFiber`), and `ProperSMul.orbitRelFiberDiffeomorph`
identifies its total space with the level, equivariantly and over the orbit projection. The orbit
space is Hausdorff (Mathlib's `t2Space_quotient_mulAction_of_properSMul`), compact when the level
is, and a boundaryless finite-dimensional manifold modelled on `ProperSMul.QuotientModelSpace`; so
it is a base as in `Geometry/Symplectic/Coupling/Basic.lean`. The example at the end of the file
checks this.

**Bundled instances.** None of the structures above is a global instance on `{x // f x = c}`:
the action depends on the proof of invariance, the atlases on the models and on the regularity
proofs. The structure `SymplecticGeometry.IsFreeRegularLevel G I f c n` bundles these proofs (the
smoothness of `f` at the points of the level, at order `∞`, the regularity of `c`, the dimension
`n`, the invariance of `f` and the freeness of the action on the level), and the type synonym
`SymplecticGeometry.FreeRegularLevel IG h` of the level, for `h` such a proof and `IG` the model
of `G`, carries all of them as instances: the atlas `TauCeti.regularLevelChartedSpace` and its
manifold structure, the action `levelInvMulAction` and its smoothness, properness and freeness, the
slice charts `ProperSMul.orbitRelQuotientChartedSpace` of the orbit space, and Tau Ceti's fibre,
principal and smooth bundle structures of `orbitRelFiber G (FreeRegularLevel IG h)`. A statement
about the bundle of a level then takes a proof `h` and needs no local instances; the band
theorems and the converse of minimal coupling in `Geometry/Symplectic/Coupling/Converse.lean` are
stated this way, for `G = Circle`. The inclusion into `M` is `FreeRegularLevel.val`, a
topological and a smooth embedding (`FreeRegularLevel.isEmbedding_val`,
`FreeRegularLevel.isSmoothEmbedding_val`), so the level is compact exactly when `{x | f x = c}` is
(`FreeRegularLevel.compactSpace_iff`).

## Main definitions and results

* `SymplecticGeometry.levelInvMulAction`: the action by inverses of a commutative group on a level
  of an invariant map, with `SymplecticGeometry.coe_levelInvMulAction_smul`.
* `SymplecticGeometry.contMDiffSMul_levelInvMulAction`: it is smooth for the regular-level atlas.
* `SymplecticGeometry.isCancelSMul_levelInvMulAction`: it is free where `G` acts freely.
* `SymplecticGeometry.IsFreeRegularLevel`, `SymplecticGeometry.FreeRegularLevel`: a free invariant
  regular level, and the level with the instances above and the principal bundle of its orbits.
* `SymplecticGeometry.FreeRegularLevel.val_orbitRelFiberDiffeomorph_op_smul`: Tau Ceti's
  diffeomorphism of the total space with the level carries the right action of `G` to the action
  of `G` on `M`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.1
  (the circle bundle of a regular level of a free circle action, in minimal coupling).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Corollary 5.14 (regular level sets) and Theorem 21.10 (the quotient manifold
  theorem).
-/

public section

open MulAction MulOpposite TauCeti
open scoped ContDiff Manifold

namespace SymplecticGeometry

/-! ### The action on a level by inverses -/

section Action

variable {G M F : Type*} [CommGroup G] [MulAction G M] {f : M → F}

variable (c : F) in
/-- The action of a commutative group `G` on a level `{x // f x = c}` of a `G`-invariant map `f`
by inverses: `g` moves `x` to `g⁻¹ • x`. Tau Ceti's bundle of orbits `TauCeti.orbitRelFiber`
acts on the right by `x · g = g⁻¹ • x`, so for this action its right action is `x · g = g • x`. -/
@[instance_reducible]
def levelInvMulAction (hinv : ∀ (g : G) (x : M), f (g • x) = f x) :
    MulAction G {x : M // f x = c} where
  smul g x := ⟨g⁻¹ • (x : M), (hinv _ _).trans x.property⟩
  one_smul x := Subtype.ext <| by
    -- The goal is stated with the `smul` field being defined; `change` reads it on `M`.
    change (1 : G)⁻¹ • (x : M) = x
    rw [inv_one, one_smul]
  mul_smul g h x := Subtype.ext <| by
    -- As above, `change` reads the `smul` field on `M`.
    change (g * h)⁻¹ • (x : M) = g⁻¹ • h⁻¹ • (x : M)
    rw [mul_inv, mul_smul]

variable (hinv : ∀ (g : G) (x : M), f (g • x) = f x) {c : F}

/-- The action `levelInvMulAction` is the action of `G` on `M` by inverses. -/
@[simp]
theorem coe_levelInvMulAction_smul (g : G) (x : {x : M // f x = c}) :
    letI := levelInvMulAction c hinv
    ((g • x : {x : M // f x = c}) : M) = g⁻¹ • (x : M) :=
  (rfl)

/-- **Freeness on the level.** If `G` acts freely at every point of the level, then it acts
freely on the level by `levelInvMulAction`. -/
theorem isCancelSMul_levelInvMulAction (hfree : ∀ x, f x = c → stabilizer G x = ⊥) :
    letI := levelInvMulAction c hinv
    IsCancelSMul G {x : M // f x = c} :=
  letI := levelInvMulAction c hinv
  isCancelSMul_iff_stabilizer_eq_bot.2 fun x ↦ (Subgroup.eq_bot_iff_forall _).2 fun g hg ↦ by
    have hg' : g⁻¹ ∈ stabilizer G (x : M) := by
      rw [mem_stabilizer_iff, ← coe_levelInvMulAction_smul hinv, (mem_stabilizer_iff).1 hg]
    rwa [hfree x x.property, Subgroup.mem_bot, inv_eq_one] at hg'

end Action

/-! ### Smoothness on a regular level -/

section Smooth

variable {𝕜 : Type*} [RCLike 𝕜] {m : ℕ∞ω}
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [CommGroup G] [LieGroup IG m G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I m M]
  [MulAction G M] [ContMDiffSMul IG I m G M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {f : M → F} {c : F} {n : ℕ}

/-- **The action on a regular level is `C^m`.** Let `1 ≤ m`. For the regular-level atlas of
`{x // f x = c}`, the action `levelInvMulAction` by inverses of a commutative Lie group `G`
acting `C^m` on `M` is `C^m`. -/
theorem contMDiffSMul_levelInvMulAction (hm : 1 ≤ m)
    (hf : ∀ x, f x = c → ContMDiffAt I 𝓘(𝕜, F) m f x)
    (hreg : IsRegularValue I 𝓘(𝕜, F) f c) (hn : Module.finrank 𝕜 E - Module.finrank 𝕜 F = n)
    (hinv : ∀ (g : G) (x : M), f (g • x) = f x) :
    letI := regularLevelChartedSpace (fun x hx ↦ (hf x hx).of_le hm) hreg hn
    letI := levelInvMulAction c hinv
    ContMDiffSMul IG 𝓘(𝕜, Fin n → 𝕜) m G {x : M // f x = c} :=
  letI := regularLevelChartedSpace (fun x hx ↦ (hf x hx).of_le hm) hreg hn
  letI := levelInvMulAction c hinv
  (isSmoothEmbedding_coe_regularLevel hm hf hreg hn).contMDiffSMul
    (contMDiff_inv IG m) fun g x ↦ coe_levelInvMulAction_smul hinv g x

end Smooth

/-! ### The bundled free regular level -/

section Bundled

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [CommGroup G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MulAction G M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (G I) in
/-- The level `{x // f x = c}` of `f : M → F` is a **free invariant regular level** of dimension
`n` for the action of `G` on `M` when `f` is smooth at the points of the level, `c` is a regular
value of `f`, `dim E - dim F = n` for the models `E` of `M` and `F`, `f` is `G`-invariant, and `G`
acts freely at the points of the level. -/
structure IsFreeRegularLevel (f : M → F) (c : F) (n : ℕ) : Prop where
  /-- `f` is smooth at the points of the level. -/
  contMDiffAt : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ, F) ∞ f x
  /-- `c` is a regular value of `f`. -/
  isRegularValue : IsRegularValue I 𝓘(ℝ, F) f c
  /-- The level has dimension `n`. -/
  finrank_sub : Module.finrank ℝ E - Module.finrank ℝ F = n
  /-- `f` is invariant under the action of `G`. -/
  apply_smul : ∀ (g : G) (x : M), f (g • x) = f x
  /-- `G` acts freely at the points of the level. -/
  stabilizer_eq_bot : ∀ x, f x = c → stabilizer G x = ⊥

variable {f : M → F} {c : F} {n : ℕ}

/-- The level `{x // f x = c}` of a free invariant regular level `h`, for the model `IG` of the
group. Its type determines `h` and `IG`, so the regular-level atlas, the action
`levelInvMulAction` of `G` by inverses, the slice charts of its orbit space and Tau Ceti's
principal bundle structure of `orbitRelFiber G` are instances on it. -/
@[expose, nolint unusedArguments]
def FreeRegularLevel (_IG : ModelWithCorners ℝ EG HG) (_h : IsFreeRegularLevel G I f c n) :
    Type _ := {x : M // f x = c}

namespace FreeRegularLevel

variable {h : IsFreeRegularLevel G I f c n}

instance : TopologicalSpace (FreeRegularLevel IG h) :=
  inferInstanceAs (TopologicalSpace {x : M // f x = c})

/-- The inclusion of the level into `M`. -/
def val (x : FreeRegularLevel IG h) : M := Subtype.val (p := fun x ↦ f x = c) x

variable (IG h) in
/-- A point `x` of `M` with `f x = c`, as a point of the level. -/
def mk (x : M) (hx : f x = c) : FreeRegularLevel IG h := (⟨x, hx⟩ : {x : M // f x = c})

theorem val_def : (val : FreeRegularLevel IG h → M) = Subtype.val (p := fun x ↦ f x = c) :=
  (rfl)

variable (IG h) in
theorem mk_def (x : M) (hx : f x = c) : mk IG h x hx = (⟨x, hx⟩ : {x : M // f x = c}) :=
  (rfl)

@[simp]
theorem val_mk (x : M) (hx : f x = c) : val (mk IG h x hx) = x := (rfl)

/-- The points of the level lie on the level. -/
theorem apply_val (x : FreeRegularLevel IG h) : f (val x) = c :=
  Subtype.prop (p := fun x ↦ f x = c) x

@[simp]
theorem mk_val (x : FreeRegularLevel IG h) : mk IG h (val x) (apply_val x) = x := (rfl)

theorem val_injective : Function.Injective (val : FreeRegularLevel IG h → M) :=
  Subtype.val_injective (p := fun x ↦ f x = c)

@[ext]
theorem ext {x y : FreeRegularLevel IG h} (hxy : val x = val y) : x = y :=
  val_injective hxy

/-- The image of the inclusion is the level `{x | f x = c}`. -/
@[simp]
theorem range_val : Set.range (val : FreeRegularLevel IG h → M) = {x | f x = c} :=
  Subtype.range_coe_subtype

@[fun_prop, continuity]
theorem continuous_val : Continuous (val : FreeRegularLevel IG h → M) :=
  continuous_subtypeVal (p := fun x ↦ f x = c)

/-- The inclusion of the level into `M` is a topological embedding. -/
theorem isEmbedding_val : Topology.IsEmbedding (val : FreeRegularLevel IG h → M) :=
  Topology.IsEmbedding.subtypeVal (p := fun x ↦ f x = c)

/-- The level is compact exactly when `{x | f x = c}` is a compact subset of `M`. -/
theorem compactSpace_iff : CompactSpace (FreeRegularLevel IG h) ↔ IsCompact {x | f x = c} := by
  rw [← isCompact_univ_iff, isEmbedding_val.isCompact_iff, Set.image_univ, range_val]

instance [T2Space M] : T2Space (FreeRegularLevel IG h) :=
  inferInstanceAs (T2Space {x : M // f x = c})

/-- The action `levelInvMulAction` of `G` on the level, by inverses. -/
instance : MulAction G (FreeRegularLevel IG h) := levelInvMulAction c h.apply_smul

/-- The action of `G` on the level is the action of `G` on `M` by inverses. -/
@[simp]
theorem val_smul (g : G) (x : FreeRegularLevel IG h) : val (g • x) = g⁻¹ • val x :=
  coe_levelInvMulAction_smul h.apply_smul g x

instance : IsCancelSMul G (FreeRegularLevel IG h) :=
  isCancelSMul_levelInvMulAction h.apply_smul h.stabilizer_eq_bot

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless]

/-- The regular-level atlas `TauCeti.regularLevelChartedSpace` of the level. -/
noncomputable instance : ChartedSpace (Fin n → ℝ) (FreeRegularLevel IG h) :=
  regularLevelChartedSpace (fun x hx ↦ (h.contMDiffAt x hx).of_le (by simp)) h.isRegularValue
    h.finrank_sub

variable [IsManifold I ∞ M]

instance : IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ (FreeRegularLevel IG h) :=
  isManifold_regularLevel (by simp) h.contMDiffAt h.isRegularValue h.finrank_sub

/-- The inclusion of the level into `M` is a smooth embedding. -/
theorem isSmoothEmbedding_val :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin n → ℝ) I ∞ (val : FreeRegularLevel IG h → M) :=
  isSmoothEmbedding_coe_regularLevel (by simp) h.contMDiffAt h.isRegularValue h.finrank_sub

variable [TopologicalSpace G] [ChartedSpace HG G] [LieGroup IG ∞ G] [ContMDiffSMul IG I ∞ G M]

instance : ContMDiffSMul IG 𝓘(ℝ, Fin n → ℝ) ∞ G (FreeRegularLevel IG h) :=
  contMDiffSMul_levelInvMulAction (by simp) h.contMDiffAt h.isRegularValue h.finrank_sub
    h.apply_smul

instance : ContinuousSMul G (FreeRegularLevel IG h) :=
  ContMDiffSMul.continuousSMul (I := IG) (I' := 𝓘(ℝ, Fin n → ℝ)) ∞

instance [CompactSpace G] [T2Space M] : ProperSMul G (FreeRegularLevel IG h) :=
  properSMul_of_compactSpace G _

variable [FiniteDimensional ℝ EG] [CompactSpace G] [T2Space M]

/-- The slice charts `ProperSMul.orbitRelQuotientChartedSpace` of the orbit space of the level. -/
noncomputable instance : ChartedSpace (ProperSMul.QuotientModelSpace EG (Fin n → ℝ))
    (orbitRel.Quotient G (FreeRegularLevel IG h)) :=
  ProperSMul.orbitRelQuotientChartedSpace IG G 𝓘(ℝ, Fin n → ℝ) (FreeRegularLevel IG h)

/-- Tau Ceti's fibre bundle structure `ProperSMul.orbitRelFiberBundle` on the orbits of the
level. -/
noncomputable instance : FiberBundle G (orbitRelFiber G (FreeRegularLevel IG h)) :=
  ProperSMul.orbitRelFiberBundle IG G 𝓘(ℝ, Fin n → ℝ) (FreeRegularLevel IG h)

instance : PrincipalBundle G (orbitRelFiber G (FreeRegularLevel IG h)) :=
  ProperSMul.principalBundle_orbitRelFiber

instance : ContMDiffFiberBundle ∞ G (orbitRelFiber G (FreeRegularLevel IG h))
    𝓘(ℝ, ProperSMul.QuotientModelSpace EG (Fin n → ℝ)) IG :=
  ProperSMul.contMDiffFiberBundle_orbitRelFiber

/-- Tau Ceti's diffeomorphism `ProperSMul.orbitRelFiberDiffeomorph` of the total space of the
bundle of orbits with the level intertwines the right action of `G` on the total space with the
action of `G` on `M`, read on the level. -/
theorem val_orbitRelFiberDiffeomorph_op_smul (g : G)
    (p : ManifoldTotalSpace G (orbitRelFiber G (FreeRegularLevel IG h))) :
    val (ProperSMul.orbitRelFiberDiffeomorph IG G 𝓘(ℝ, Fin n → ℝ) _ (op g • p)) =
      g • val (ProperSMul.orbitRelFiberDiffeomorph IG G 𝓘(ℝ, Fin n → ℝ) _ p) := by
  rw [ProperSMul.orbitRelFiberDiffeomorph_op_smul, val_smul, inv_inv]

end FreeRegularLevel

/- For a smooth action of a compact commutative Lie group `G` on a boundaryless Hausdorff
finite-dimensional manifold `M`, free on a regular level of a smooth invariant map, the instances
on `FreeRegularLevel` make the orbits of the level a smooth principal `G`-bundle over a Hausdorff
boundaryless finite-dimensional manifold, compact when the level is, whose total space is
diffeomorphic to the level, equivariantly and over the orbit projection. -/
example
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [CommGroup G] [LieGroup IG ∞ G]
    [CompactSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MulAction G M] [ContMDiffSMul IG I ∞ G M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : M → F} {c : F} {n : ℕ} (h : IsFreeRegularLevel G I f c n) :
    PrincipalBundle G (orbitRelFiber G (FreeRegularLevel IG h)) ∧
      ContMDiffFiberBundle ∞ G (orbitRelFiber G (FreeRegularLevel IG h))
        𝓘(ℝ, ProperSMul.QuotientModelSpace EG (Fin n → ℝ)) IG ∧
      IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace EG (Fin n → ℝ)) ∞
        (orbitRel.Quotient G (FreeRegularLevel IG h)) ∧
      (𝓘(ℝ, ProperSMul.QuotientModelSpace EG (Fin n → ℝ))).Boundaryless ∧
      FiniteDimensional ℝ (ProperSMul.QuotientModelSpace EG (Fin n → ℝ)) ∧
      T2Space (orbitRel.Quotient G (FreeRegularLevel IG h)) ∧
      (CompactSpace (FreeRegularLevel IG h) →
        CompactSpace (orbitRel.Quotient G (FreeRegularLevel IG h))) ∧
      ∀ (g : G) (p : ManifoldTotalSpace G (orbitRelFiber G (FreeRegularLevel IG h))),
        FreeRegularLevel.val
            (ProperSMul.orbitRelFiberDiffeomorph IG G 𝓘(ℝ, Fin n → ℝ) _ (op g • p)) =
            g • FreeRegularLevel.val
              (ProperSMul.orbitRelFiberDiffeomorph IG G 𝓘(ℝ, Fin n → ℝ) _ p) ∧
          Quotient.mk _ (ProperSMul.orbitRelFiberDiffeomorph IG G 𝓘(ℝ, Fin n → ℝ) _ p) =
            ((ManifoldTotalSpace.homeomorph G _).symm p).proj :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    fun _ ↦ inferInstance, fun g p ↦ ⟨FreeRegularLevel.val_orbitRelFiberDiffeomorph_op_smul g p,
      ProperSMul.quotientMk_orbitRelFiberDiffeomorph p⟩⟩

end Bundled

end SymplecticGeometry

end
