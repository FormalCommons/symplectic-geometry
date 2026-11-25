/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.Restrict
public import TauCeti.Geometry.Manifold.RegularValue.Level
public import TauCeti.Topology.Algebra.ProperAction.Basic
public import SymplecticGeometry.Geometry.Manifold.GroupAction.PrincipalBundle

/-!
# The circle bundle of a regular level

Let a commutative Lie group `G`, such as `Circle`, act smoothly on a boundaryless manifold `M`,
and let `f : M → F` be a smooth `G`-invariant map with regular value `c`. The level
`{x // f x = c}` carries Tau Ceti's atlas `TauCeti.regularLevelChartedSpace`. This file restricts
the action to the level, written as a right action as principal bundles in Tau Ceti act: since
`G` is commutative, `op g • x = g • x` is an action of `Gᵐᵒᵖ`
(`SymplecticGeometry.levelOpMulAction`). The restricted action is

* smooth for the regular-level atlas (`SymplecticGeometry.contMDiffSMul_levelOpMulAction`), as
  the inclusion of the level is a smooth embedding
  (`TauCeti.isSmoothEmbedding_coe_regularLevel`), by
  `Manifold.IsSmoothEmbedding.contMDiffSMul`;
* free when `G` acts freely at the points of the level
  (`SymplecticGeometry.isCancelSMul_levelOpMulAction`);
* proper when `G` is compact and `M` Hausdorff
  (`SymplecticGeometry.properSMul_levelOpMulAction`, by `TauCeti.properSMul_of_compactSpace`).

These are the hypotheses of `GroupAction/PrincipalBundle.lean`, so the orbits of the level form a
smooth principal `G`-bundle `orbitFiber Gᵐᵒᵖ {x // f x = c}` over the orbit space, and Tau Ceti's
`TauCeti.MapFiber.Atlas.totalSpaceDiffeomorph` identifies its total space with the level,
equivariantly and over the orbit projection. The orbit space is Hausdorff (Mathlib's
`t2Space_quotient_mulAction_of_properSMul`), compact when the level is, and a boundaryless
finite-dimensional manifold modelled on `ProperSMul.QuotientModelSpace`; so it is a base as in
`Geometry/Symplectic/Coupling/Basic.lean`. The example at the end of the file checks this.

**Bundled instances.** None of the structures above is a global instance on `{x // f x = c}`:
the action depends on the proof of invariance, the atlases on the models and on the regularity
proofs. The structure `SymplecticGeometry.IsFreeRegularLevel G I f c n` bundles these proofs (the
smoothness of `f` at the points of the level, at order `∞`, the regularity of `c`, the dimension
`n`, the invariance of `f` and the freeness of the action on the level), and the type synonym
`SymplecticGeometry.FreeRegularLevel IG h` of the level, for `h` such a proof and `IG` the model
of `G`, carries all of them as instances: the atlas `TauCeti.regularLevelChartedSpace` and its
manifold structure, the action `levelOpMulAction` and its smoothness, properness and freeness, the
slice charts `ProperSMul.orbitRelQuotientChartedSpace` of the orbit space, and the fibre, principal
and smooth bundle structures of `orbitFiber Gᵐᵒᵖ (FreeRegularLevel IG h)` from
`GroupAction/PrincipalBundle.lean`. A statement about the bundle of a level, such as the converse
of minimal coupling, then needs only `attribute [local instance] MulOpposite.chartedSpace`, for
the charts of `G` on `Gᵐᵒᵖ`. The inclusion into `M` is `FreeRegularLevel.val`, a smooth embedding
(`FreeRegularLevel.isSmoothEmbedding_val`), and `FreeRegularLevel.totalSpaceDiffeomorph` is Tau
Ceti's diffeomorphism of the total space with the level.

## Main definitions and results

* `SymplecticGeometry.levelOpMulAction`: the right action of a commutative group on a level of an
  invariant map, with `SymplecticGeometry.coe_levelOpMulAction_smul`.
* `SymplecticGeometry.continuousSMul_levelOpMulAction`, `contMDiffSMul_levelOpMulAction`: it is
  continuous, and smooth for the regular-level atlas.
* `SymplecticGeometry.isCancelSMul_levelOpMulAction`: it is free where `G` acts freely.
* `SymplecticGeometry.properSMul_levelOpMulAction`: it is proper for compact `G`.
* `SymplecticGeometry.IsFreeRegularLevel`, `SymplecticGeometry.FreeRegularLevel`: a free invariant
  regular level, and the level with the instances above and the principal bundle of its orbits.
* `SymplecticGeometry.FreeRegularLevel.totalSpaceDiffeomorph`, with `totalSpaceDiffeomorph_smul`
  and `mk_totalSpaceDiffeomorph`: the total space of that bundle is the level, with
  `totalSpaceDiffeomorph_apply` and `totalSpaceDiffeomorph_symm_mk` saying what it does on points.

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

/-! ### The right action on a level -/

section Action

variable {G M F : Type*} [CommGroup G] [MulAction G M] {f : M → F}

variable (c : F) in
/-- The right action of a commutative group `G` on a level `{x // f x = c}` of a `G`-invariant
map `f`, written as an action of `Gᵐᵒᵖ`: `op g` moves `x` to `g • x`. -/
@[instance_reducible]
def levelOpMulAction (hinv : ∀ (g : G) (x : M), f (g • x) = f x) :
    MulAction Gᵐᵒᵖ {x : M // f x = c} where
  smul g x := ⟨unop g • (x : M), (hinv _ _).trans x.property⟩
  one_smul x := Subtype.ext (one_smul G (x : M))
  mul_smul g h x := Subtype.ext <| by
    -- The goal is stated with the `smul` field being defined; `change` reads it on `M`.
    change unop (g * h) • (x : M) = unop g • unop h • (x : M)
    rw [unop_mul, mul_comm, mul_smul]

variable (hinv : ∀ (g : G) (x : M), f (g • x) = f x) {c : F}

/-- The action `levelOpMulAction` is the action of `G` on `M`, read through `unop`. -/
@[simp]
theorem coe_levelOpMulAction_smul (g : Gᵐᵒᵖ) (x : {x : M // f x = c}) :
    letI := levelOpMulAction c hinv
    ((g • x : {x : M // f x = c}) : M) = unop g • (x : M) :=
  (rfl)

/-- **Freeness on the level.** If `G` acts freely at every point of the level, then `Gᵐᵒᵖ` acts
freely on it. -/
theorem isCancelSMul_levelOpMulAction (hfree : ∀ x, f x = c → stabilizer G x = ⊥) :
    letI := levelOpMulAction c hinv
    IsCancelSMul Gᵐᵒᵖ {x : M // f x = c} :=
  letI := levelOpMulAction c hinv
  isCancelSMul_iff_stabilizer_eq_bot.2 fun x ↦ (Subgroup.eq_bot_iff_forall _).2 fun g hg ↦ by
    have hg' : unop g ∈ stabilizer G (x : M) := by
      rw [mem_stabilizer_iff, ← coe_levelOpMulAction_smul hinv, (mem_stabilizer_iff).1 hg]
    rw [hfree x x.property, Subgroup.mem_bot] at hg'
    rw [← op_unop g, hg', op_one]

variable [TopologicalSpace G] [TopologicalSpace M] [ContinuousSMul G M]

/-- The action `levelOpMulAction` is continuous, for the subspace topology of the level. -/
theorem continuousSMul_levelOpMulAction :
    letI := levelOpMulAction c hinv
    ContinuousSMul Gᵐᵒᵖ {x : M // f x = c} :=
  letI := levelOpMulAction c hinv
  ⟨((continuous_unop.comp continuous_fst).smul
    (continuous_subtypeVal.comp continuous_snd)).subtype_mk _⟩

/-- **Properness on the level.** A compact group acts properly on a level of an invariant map in a
Hausdorff space. -/
theorem properSMul_levelOpMulAction [CompactSpace G] [T2Space M] :
    letI := levelOpMulAction c hinv
    ProperSMul Gᵐᵒᵖ {x : M // f x = c} :=
  letI := levelOpMulAction c hinv
  haveI := continuousSMul_levelOpMulAction (c := c) hinv
  properSMul_of_compactSpace Gᵐᵒᵖ _

end Action

/-! ### Smoothness on a regular level -/

section Smooth

attribute [local instance] MulOpposite.chartedSpace

variable {𝕜 : Type*} [RCLike 𝕜] {m : ℕ∞ω}
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [CommGroup G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I m M]
  [MulAction G M] [ContMDiffSMul IG I m G M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {f : M → F} {c : F} {n : ℕ}

/-- **The action on a regular level is `C^m`.** Let `1 ≤ m`. For the regular-level atlas of
`{x // f x = c}` and the charts of `G` on `Gᵐᵒᵖ`, the right action `levelOpMulAction` of a
commutative group `G` acting `C^m` on `M` is `C^m`. -/
theorem contMDiffSMul_levelOpMulAction (hm : 1 ≤ m)
    (hf : ∀ x, f x = c → ContMDiffAt I 𝓘(𝕜, F) m f x)
    (hreg : IsRegularValue I 𝓘(𝕜, F) f c) (hn : Module.finrank 𝕜 E - Module.finrank 𝕜 F = n)
    (hinv : ∀ (g : G) (x : M), f (g • x) = f x) :
    letI := regularLevelChartedSpace (fun x hx ↦ (hf x hx).of_le hm) hreg hn
    letI := levelOpMulAction c hinv
    ContMDiffSMul IG 𝓘(𝕜, Fin n → 𝕜) m Gᵐᵒᵖ {x : M // f x = c} :=
  letI := regularLevelChartedSpace (fun x hx ↦ (hf x hx).of_le hm) hreg hn
  letI := levelOpMulAction c hinv
  (isSmoothEmbedding_coe_regularLevel hm hf hreg hn).contMDiffSMul
    (contMDiff_unop IG m) fun g x ↦ coe_levelOpMulAction_smul hinv g x

end Smooth

/-! ### The bundled free regular level -/

section Bundled

attribute [local instance] MulOpposite.chartedSpace

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
group. Its type determines `h` and `IG`, so the regular-level atlas, the right action
`levelOpMulAction` of `Gᵐᵒᵖ`, the slice charts of its orbit space and the principal bundle
structure of `orbitFiber Gᵐᵒᵖ` are instances on it. -/
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

instance [T2Space M] : T2Space (FreeRegularLevel IG h) :=
  inferInstanceAs (T2Space {x : M // f x = c})

/-- The right action `levelOpMulAction` of `Gᵐᵒᵖ` on the level. -/
instance : MulAction Gᵐᵒᵖ (FreeRegularLevel IG h) := levelOpMulAction c h.apply_smul

/-- The action of `Gᵐᵒᵖ` on the level is the action of `G` on `M`, read through `unop`. -/
@[simp]
theorem val_smul (g : Gᵐᵒᵖ) (x : FreeRegularLevel IG h) : val (g • x) = unop g • val x :=
  coe_levelOpMulAction_smul h.apply_smul g x

instance : IsCancelSMul Gᵐᵒᵖ (FreeRegularLevel IG h) :=
  isCancelSMul_levelOpMulAction h.apply_smul h.stabilizer_eq_bot

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

variable [TopologicalSpace G] [ChartedSpace HG G] [ContMDiffSMul IG I ∞ G M]

instance : ContMDiffSMul IG 𝓘(ℝ, Fin n → ℝ) ∞ Gᵐᵒᵖ (FreeRegularLevel IG h) :=
  contMDiffSMul_levelOpMulAction (by simp) h.contMDiffAt h.isRegularValue h.finrank_sub
    h.apply_smul

instance : ContinuousSMul Gᵐᵒᵖ (FreeRegularLevel IG h) :=
  haveI := ContMDiffSMul.continuousSMul (I := IG) (I' := I) (G := G) (M := M) ∞
  continuousSMul_levelOpMulAction h.apply_smul

instance [CompactSpace G] [T2Space M] : ProperSMul Gᵐᵒᵖ (FreeRegularLevel IG h) :=
  haveI := ContMDiffSMul.continuousSMul (I := IG) (I' := I) (G := G) (M := M) ∞
  properSMul_levelOpMulAction h.apply_smul

variable [FiniteDimensional ℝ EG] [LieGroup IG ∞ G] [ContinuousInv G] [CompactSpace G]
  [T2Space M]

/-- The slice charts `ProperSMul.orbitRelQuotientChartedSpace` of the orbit space of the level. -/
noncomputable instance : ChartedSpace (ProperSMul.QuotientModelSpace EG (Fin n → ℝ))
    (orbitRel.Quotient Gᵐᵒᵖ (FreeRegularLevel IG h)) :=
  ProperSMul.orbitRelQuotientChartedSpace IG Gᵐᵒᵖ 𝓘(ℝ, Fin n → ℝ) (FreeRegularLevel IG h)

/-- The fibre bundle structure of `orbitFiber.atlas` on the orbits of the level. -/
noncomputable instance : FiberBundle G (orbitFiber Gᵐᵒᵖ (FreeRegularLevel IG h)) :=
  (orbitFiber.atlas IG G 𝓘(ℝ, Fin n → ℝ) (FreeRegularLevel IG h)).fiberBundle

instance : PrincipalBundle G (orbitFiber Gᵐᵒᵖ (FreeRegularLevel IG h)) :=
  orbitFiber.principalBundle IG G 𝓘(ℝ, Fin n → ℝ) (FreeRegularLevel IG h)

instance : ContMDiffFiberBundle ∞ G (orbitFiber Gᵐᵒᵖ (FreeRegularLevel IG h))
    𝓘(ℝ, ProperSMul.QuotientModelSpace EG (Fin n → ℝ)) IG :=
  (orbitFiber.atlas IG G 𝓘(ℝ, Fin n → ℝ) (FreeRegularLevel IG h)).contMDiffFiberBundle
    (orbitFiber.isContMDiff_atlas IG G 𝓘(ℝ, Fin n → ℝ) (FreeRegularLevel IG h))

variable (IG h) in
/-- The smooth diffeomorphism `TauCeti.MapFiber.Atlas.totalSpaceDiffeomorph` from the total space
of the orbit bundle of the level to the level, `⟨q, x⟩ ↦ x`. -/
noncomputable def totalSpaceDiffeomorph :
    ManifoldTotalSpace G (orbitFiber Gᵐᵒᵖ (FreeRegularLevel IG h)) ≃ₘ⟮
      𝓘(ℝ, ProperSMul.QuotientModelSpace EG (Fin n → ℝ)).prod IG, 𝓘(ℝ, Fin n → ℝ)⟯
      FreeRegularLevel IG h :=
  (orbitFiber.atlas IG G 𝓘(ℝ, Fin n → ℝ) (FreeRegularLevel IG h)).totalSpaceDiffeomorph
    (orbitFiber.isContMDiff_atlas IG G 𝓘(ℝ, Fin n → ℝ) (FreeRegularLevel IG h))

variable (IG h) in
theorem totalSpaceDiffeomorph_def :
    totalSpaceDiffeomorph IG h =
      (orbitFiber.atlas IG G 𝓘(ℝ, Fin n → ℝ) (FreeRegularLevel IG h)).totalSpaceDiffeomorph
        (orbitFiber.isContMDiff_atlas IG G 𝓘(ℝ, Fin n → ℝ) (FreeRegularLevel IG h)) :=
  (rfl)

/-- The diffeomorphism `totalSpaceDiffeomorph` sends a point of the fibre over an orbit to itself,
as a point of the level. -/
theorem totalSpaceDiffeomorph_apply
    (p : ManifoldTotalSpace G (orbitFiber Gᵐᵒᵖ (FreeRegularLevel IG h))) :
    totalSpaceDiffeomorph IG h p = ((ManifoldTotalSpace.homeomorph G _).symm p).snd.val :=
  (MapFiber.Atlas.totalSpaceDiffeomorph_apply _ p).trans (MapFiber.totalSpaceHomeomorph_apply _)

/-- Read in `M`, the diffeomorphism `totalSpaceDiffeomorph` sends a point of the fibre over an
orbit to that point of `M`. -/
@[simp]
theorem val_totalSpaceDiffeomorph_homeomorph
    (z : Bundle.TotalSpace G (orbitFiber Gᵐᵒᵖ (FreeRegularLevel IG h))) :
    val (totalSpaceDiffeomorph IG h (ManifoldTotalSpace.homeomorph G _ z)) = val z.snd.val := by
  rw [totalSpaceDiffeomorph_apply, Homeomorph.symm_apply_apply]

/-- The inverse of `totalSpaceDiffeomorph` sends the point `mk x hx` of the level to itself, as a
point of the fibre over its orbit. -/
@[simp]
theorem totalSpaceDiffeomorph_symm_mk (x : M) (hx : f x = c) :
    (totalSpaceDiffeomorph IG h).symm (mk IG h x hx) =
      ManifoldTotalSpace.homeomorph G _ ⟨Quotient.mk _ (mk IG h x hx), ⟨mk IG h x hx, rfl⟩⟩ :=
  (MapFiber.Atlas.totalSpaceDiffeomorph_symm_apply _ _).trans
    (congrArg _ (MapFiber.totalSpaceHomeomorph_symm_apply _))

/-- The diffeomorphism `totalSpaceDiffeomorph` is equivariant for the right action of `G`. -/
theorem totalSpaceDiffeomorph_smul (g : Gᵐᵒᵖ)
    (p : ManifoldTotalSpace G (orbitFiber Gᵐᵒᵖ (FreeRegularLevel IG h))) :
    totalSpaceDiffeomorph IG h (g • p) = g • totalSpaceDiffeomorph IG h p :=
  MapFiber.Atlas.totalSpaceDiffeomorph_smul (a := g) (x := p)
    (hproj := fun _ _ ↦ orbitRel.Quotient.quotient_smul_eq) _

/-- The diffeomorphism `totalSpaceDiffeomorph` lies over the orbit space: it carries the bundle
projection to the orbit projection. -/
theorem mk_totalSpaceDiffeomorph
    (p : ManifoldTotalSpace G (orbitFiber Gᵐᵒᵖ (FreeRegularLevel IG h))) :
    Quotient.mk _ (totalSpaceDiffeomorph IG h p) =
      ((ManifoldTotalSpace.homeomorph G _).symm p).proj :=
  MapFiber.Atlas.proj_totalSpaceDiffeomorph (x := p) _

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
    [ContinuousInv G] [CompactSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MulAction G M] [ContMDiffSMul IG I ∞ G M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : M → F} {c : F} {n : ℕ} (h : IsFreeRegularLevel G I f c n) :
    PrincipalBundle G (orbitFiber Gᵐᵒᵖ (FreeRegularLevel IG h)) ∧
      ContMDiffFiberBundle ∞ G (orbitFiber Gᵐᵒᵖ (FreeRegularLevel IG h))
        𝓘(ℝ, ProperSMul.QuotientModelSpace EG (Fin n → ℝ)) IG ∧
      IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace EG (Fin n → ℝ)) ∞
        (orbitRel.Quotient Gᵐᵒᵖ (FreeRegularLevel IG h)) ∧
      (𝓘(ℝ, ProperSMul.QuotientModelSpace EG (Fin n → ℝ))).Boundaryless ∧
      FiniteDimensional ℝ (ProperSMul.QuotientModelSpace EG (Fin n → ℝ)) ∧
      T2Space (orbitRel.Quotient Gᵐᵒᵖ (FreeRegularLevel IG h)) ∧
      (CompactSpace (FreeRegularLevel IG h) →
        CompactSpace (orbitRel.Quotient Gᵐᵒᵖ (FreeRegularLevel IG h))) ∧
      ∀ (g : Gᵐᵒᵖ) (p : ManifoldTotalSpace G (orbitFiber Gᵐᵒᵖ (FreeRegularLevel IG h))),
        FreeRegularLevel.totalSpaceDiffeomorph IG h (g • p) =
            g • FreeRegularLevel.totalSpaceDiffeomorph IG h p ∧
          Quotient.mk _ (FreeRegularLevel.totalSpaceDiffeomorph IG h p) =
            ((ManifoldTotalSpace.homeomorph G _).symm p).proj :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    fun _ ↦ inferInstance, fun g p ↦ ⟨FreeRegularLevel.totalSpaceDiffeomorph_smul g p,
      FreeRegularLevel.mk_totalSpaceDiffeomorph p⟩⟩

end Bundled

end SymplecticGeometry

end
