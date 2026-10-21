/-ai
If an endomap a is a retraction, then so is the catamorphism that recurses a on the leaves of the tree algebra and uses the algebra's own pairing on nodes.

Write g for that catamorphism and apply uniqueness of the catamorphism to the composite of g with itself. The composite is strict. On a leaf, two applications of the leaf law together with idempotence of a show that the composite acts as the leaf map of a. On a pair, two applications of the pairing law show that the composite acts as pairing of its own values. Uniqueness therefore identifies the composite with g.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.iSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.jSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.aSharpInner
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.aSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.ISharpComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.JSharpComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharp_fixedNbhd_elementIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.grel_inSharp_pairSharp_imp_idMap_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.idMap_rel_imp_grel_inSharp_pairSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.gMap_inSharp_pairSharp_eq_idMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.pair_principal_eq_principal_prodNbhd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.inSharp_principal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.pairSharp_principal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.gMap_eq_of_satisfies
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.jSharp_comp_iSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.aSharp_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap_id
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap_comp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap_self_eq_aSharpInner
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.JSharpComb_comp_ISharpComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.ISharpComb_comp_JSharpComb

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gMap_in
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gMap_pair
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gMap_strict
@[expose] public section

/-!
# Exercise 8.21 (Scott 1981, PRG-19)

> **Exercise 8.21.** Using the fixed-point construction, show that there is a continuous and
> computable operator `λa. a§`, such that if `a` is a finitary projection of `U`, then
> `D_{a§} ≅ (D_a)§`.

Here `D§` is Scott's tree algebra of Example 6.1 (`Dsharp`, already fully formalized with computable
combinators `in`/`pair`/`proj₀`/`proj₁` in `Example61.lean`/`Combinators77.lean`/`Exercise717.lean`,
and the universal catamorphism `g : D§ → E` of Exercise 7.17 Part 2, `gMap`).

## What is formalized here

**The construction of `a§`, and the properties that are tractable without new "uniqueness of
catamorphism" infrastructure.**

* **`U§ ⊴ U`** (`dsharpU_trianglelefteq_U`): since `dsharpPresentation` (Prop 7.7) makes `U§`
  effectively given, `theorem_8_8_b_strong` (Theorem 8.8(b)) hands it a *computable* projection
  pair `iSharp : U§ → U`, `jSharp : U → U§` into `U`, exactly as Definition 8.9 fixes `i₊/j₊`,
  `i_×/j_×`, `i_→/j_→` for `U+U`, `U×U`, `U→U`.

* **The operator itself** (`aSharp`). Scott's recipe for `a§`, read off Example 6.1's own
  defining equations `out(x§) = x`, `pair(x,y)`, is: recurse `a` on the `D`-summand and leave the
  pairing structure alone, i.e. `a§` should satisfy `a§(x§) = (a x)§` and
  `a§(⟨y,z⟩) = ⟨a§(y), a§(z)⟩`. But these are *exactly* the two defining equations
  (`gMap_in`/`gMap_pair`) of Exercise 7.17 Part 2's catamorphism `gMap u v` specialized to
  `u := in ∘ a` and `v := pair` (the tree algebra's own pairing) — so the "fixed-point
  construction" the exercise asks for is already on hand as `gMap`, and no new recursion needs to
  be built:
  ```
  aSharpInner a := gMap (inSharpMap.comp a) pairSharpMap hU : U§ → U§
  aSharp a      := iSharp ∘ aSharpInner a ∘ jSharp : U → U
  ```
  This mirrors Definition 8.9's own conjugation-through-a-projection-pair pattern for `+`, `×`, `→`.

* **Computable** (`aSharp_isComputable`): `gMap_isComputable` (the heart of Exercise 7.17 Part 2)
  applies directly, since `in`/`pair` are computable (`inSharp_isComputable`/
  `pairSharp_isComputable`) and composition of computable maps is computable
  (`comp_isComputable`); chaining through `iSharp`/`jSharp`'s own computability
  (`theorem_8_8_b_strong`) gives computability of `aSharp a` whenever `a` is computable.

* **`a ≤ I ⟹ a§ ≤ I`** (`aSharp_le_idMap_of_le`, half of "`a` a projection ⟹ `a§` a projection",
  Proposition 8.10's proof recipe `a ⊑ I ⟹ a+b ⊑ I+I = i∘j ⊑ I` transcribed to `§`): the new general
  tool is **`gMap_mono`** — monotonicity of the catamorphism in `u`, `v` — proved by a direct
  structural induction on the `GRel` derivation exactly parallel to `gRel_mono` (Exercise 7.17
  Part 2), using that `≤` on `ApproximableMap` unfolds to pointwise relation inclusion
  (`ApproximableMap.le_iff`). Combined with the new characterization
  **`gMap_inSharp_pairSharp_eq_idMap`** (`gMap in pair = I_{D§}`, proved by two structural
  inductions — on `GRel` and on `MemS` — mirroring `gMap_in`/`gMap_pair`'s own style) and
  `comp_mono_gen`, monotonicity of `a§` in `a` gives `a ≤ I → a§ ≤ I` cleanly.

* **Exercise 8.21(b) — the other half of "`a` a projection ⟹ `a§` a projection", idempotence**
  (`a = a∘a ⟹ a§ = a§∘a§`). Unlike `×`/`→`/`+` in `Proposition810.lean`, there is no elementwise
  closed form for `gMap`'s action on a *general* element of `D§` (its elements are potentially
  *infinite* trees, unlike `pair`/`fst`/`snd` or `curry`/`eval` which have one-step defining
  equations valid everywhere), so this needs a genuine **uniqueness-of-catamorphism** lemma
  (`gMap_eq_of_satisfies`: `k` strict, satisfying the two `g`-equations for `(u, v) ⟹ k = gMap u v`)
  — precisely Scott's own remark in the Example 6.1 discussion ("`g` is unique because the values
  on finite elements are fixed"), proved by induction on the `MemS`-derivation of the input
  neighbourhood (bridging `k`'s abstract relation to the assumed element-level equations via
  `rel_iff_mem_principal` and two small "principal of constructor = constructor of principals"
  identities, `inSharp_principal`/`pairSharp_principal`). Idempotence of `aSharpInner a`
  (`gMap_selfComp_eq_of_isRetraction`, proved in the same general form as the uniqueness lemma) then
  transports through the `U§ ⊴ U` projection pair exactly as `Proposition810.lean`'s
  `isRetraction_prodComb`/`isRetraction_arrowComb` do (`isRetraction_aSharp`), completing
  `isProjection_aSharp`: `a` a projection ⟹ `a§` a projection, in full.

* **Exercise 8.21(c) — the headline isomorphism `D_{a§} ≅ (D_a)§`.** The key realization is that
  `D ↦ D§` is *functorial* on morphisms, not just on domains: precomposing `inSharpMap` with any
  `f : D' → D` and recursing via `gMap` (`dsharpMap`) extends `f` to `D'§ → D§`, satisfying the
  functor laws `id§ = id` (`dsharpMap_id`, literally `gMap_inSharp_pairSharp_eq_idMap`) and
  `(f' ∘ f)§ = f'§ ∘ f§` (`dsharpMap_comp`, via `gMap_eq_of_satisfies` — verbatim
  `gMap_selfComp_eq_of_isRetraction`'s proof, but *without* needing a retraction hypothesis, since
  composing two different maps needs no idempotence). Transporting `iSharp`/`jSharp` through
  `dsharpMap`'s action on the injection/projection pair `(fixedNbhd_subsystem a).inj/.proj` of
  `D_a := fixedNbhd a ◁ U` (Proposition 6.12) produces a *new* projection pair
  `I : (D_a)§ → U`, `J : U → (D_a)§` (`ISharpComb`/`JSharpComb`) with `J ∘ I = I_{(D_a)§}`
  (`dsharpMap`'s functor laws applied to `j_a ∘ i_a = I_{D_a}`) and, when `a` is a finitary
  projection, `I ∘ J = a§` (the functor laws applied to `i_a ∘ j_a = a`, Theorem 8.6's
  `inj_comp_proj_eq_self`, noting `aSharpInner a` is literally `dsharpMap` applied to
  `i_a ∘ j_a = a`). `elementIsoOfProjectionPair` (`Proposition810b.lean`) then hands us
  `(D_a)§.Element ≅ Fix(a§)` directly — Scott's headline isomorphism, in the same "domain of a
  projection = its `toElementMap`-fixed-point set" convention `Proposition810b.lean` already uses
  for `D_{a+b} ≅ D_a+D_b` etc. This also re-proves `IsFinitary (a§)`, so combined with 8.21(a)/(b)'s
  `isProjection_aSharp`, `a` a *finitary* projection of `U` `⟹` `a§` a finitary projection, in full.

Axiom footprint: everything here mentions `U`, so (as with `Definition89.lean`/`Proposition810.lean`)
it inherits `U`'s own `Classical.choice` footprint — `⊆ {propext, Classical.choice, Quot.sound}`,
confirmed not new; `dsharpMap`/`dsharpMap_id` (mentioning no `U`) are fully choice-free
`⊆ {propext, Quot.sound}`, while `dsharpMap_comp` inherits `Classical.choice` from
`gMap_eq_of_satisfies` (matching 8.21(b)'s own baseline, nothing new).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-! ## `gMap` is monotone in `u`, `v` -/

/-! ## `gMap in pair = I_{D§}` -/

variable {hD : ∀ X, D.mem X → X.Nonempty}


/-! ## Uniqueness of the catamorphism (Exercise 8.21(b), step 1)

Scott's own justification for idempotence-transport ("`g` is unique because the values on finite
elements are fixed") is made precise here: any *strict* map `k : D^§ → E` satisfying the same two
defining equations as `gMap u v hD` (on the nose, at the *element* level) is literally equal to it as
an `ApproximableMap`. The proof works with `k`'s neighbourhood relation directly, by induction on the
`MemS`-derivation of the input neighbourhood `W` — mirroring `gMap_in`/`gMap_pair`'s own proof style,
using `rel_iff_mem_principal` to bridge between `k`'s abstract relation and the assumed *element*-level
equations at the principal element of each `MemS`-shape. Two small "principal of the constructor is
the constructor of principals" identities do the bridging work (`inSharp_principal`,
`pairSharp_principal`); the general `pair_principal_eq_principal_prodNbhd` (about `prod`, not
`Dsharp` specifically) underlies the second one. -/


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


/-- **Exercise 8.21(b)(2), general form.** If `a : D → D` is a retraction, so is the recursive
extension `gMap ((inSharpMap hD).comp a) (pairSharpMap hD) hD` of `a`'s tree algebra (`aSharpInner a`
specializes this at `D := U`). Applies `gMap_eq_of_satisfies` to `k := g.comp g` (`g` the catamorphism
itself): both defining equations of `k` reduce, via `gMap_in`/`gMap_pair` applied twice, to the
corresponding equation for `g` composed with `a`'s own idempotence. -/
theorem gMap_selfComp_eq_of_isRetraction {a : ApproximableMap D D} (ha : IsRetraction a) :
    (gMap ((inSharpMap hD).comp a) (pairSharpMap hD) hD).comp
        (gMap ((inSharpMap hD).comp a) (pairSharpMap hD) hD)
      = gMap ((inSharpMap hD).comp a) (pairSharpMap hD) hD := by
  set u : ApproximableMap D (Dsharp D hD) := (inSharpMap hD).comp a with hu_def
  set v : ApproximableMap (prod (Dsharp D hD) (Dsharp D hD)) (Dsharp D hD) :=
    pairSharpMap hD with hv_def
  set g : ApproximableMap (Dsharp D hD) (Dsharp D hD) := gMap u v hD with hg_def
  have hu_eq : ∀ y : D.Element, u.toElementMap y = inSharp D hD (a.toElementMap y) := by
    intro y; rw [hu_def, toElementMap_comp, inSharpMap_toElementMap]
  show g.comp g = g
  apply gMap_eq_of_satisfies
  · rw [hg_def]; exact isStrict_comp (gMap_strict hD) (gMap_strict hD)
  · intro x
    have e1 : g.toElementMap (inSharp D hD x) = u.toElementMap x := by
      rw [hg_def]; exact gMap_in hD x
    have e2 : g.toElementMap (u.toElementMap x) = u.toElementMap (a.toElementMap x) := by
      rw [hu_eq x, hg_def]; exact gMap_in hD (a.toElementMap x)
    calc (g.comp g).toElementMap (inSharp D hD x)
        = g.toElementMap (g.toElementMap (inSharp D hD x)) := toElementMap_comp _ _ _
      _ = g.toElementMap (u.toElementMap x) := by rw [e1]
      _ = u.toElementMap (a.toElementMap x) := e2
      _ = inSharp D hD (a.toElementMap (a.toElementMap x)) := hu_eq _
      _ = inSharp D hD (a.toElementMap x) := by rw [toElementMap_idem_of_isRetraction ha]
      _ = u.toElementMap x := (hu_eq x).symm
  · intro y z
    have e1 : g.toElementMap (pairSharp D hD y z)
        = v.toElementMap (pair (g.toElementMap y) (g.toElementMap z)) := by
      rw [hg_def]; exact gMap_pair hD y z
    have e2 : v.toElementMap (pair (g.toElementMap y) (g.toElementMap z))
        = pairSharp D hD (g.toElementMap y) (g.toElementMap z) := by
      rw [hv_def]; exact pairSharpMap_toElementMap hD _ _
    have e3 : g.toElementMap (pairSharp D hD (g.toElementMap y) (g.toElementMap z))
        = v.toElementMap
            (pair (g.toElementMap (g.toElementMap y)) (g.toElementMap (g.toElementMap z))) := by
      rw [hg_def]; exact gMap_pair hD _ _
    calc (g.comp g).toElementMap (pairSharp D hD y z)
        = g.toElementMap (g.toElementMap (pairSharp D hD y z)) := toElementMap_comp _ _ _
      _ = g.toElementMap (v.toElementMap (pair (g.toElementMap y) (g.toElementMap z))) := by
          rw [e1]
      _ = g.toElementMap (pairSharp D hD (g.toElementMap y) (g.toElementMap z)) := by rw [e2]
      _ = v.toElementMap
            (pair (g.toElementMap (g.toElementMap y)) (g.toElementMap (g.toElementMap z))) := e3
      _ = v.toElementMap (pair ((g.comp g).toElementMap y) ((g.comp g).toElementMap z)) := by
          rw [toElementMap_comp, toElementMap_comp]

/-! ## `U§ ⊴ U` -/


/-! ## The operator `λa. a§` -/


/-! ## Idempotence of `a§` (Exercise 8.21(b)) -/

/-! ## `Dsharp` is functorial (Exercise 8.21(c), step 1)

The tree-algebra construction `D ↦ D§` acts on morphisms too: precomposing the injection leaf-map
`inSharpMap` with any `f : D' → D` and recursing via `gMap` extends `f` to a map `D'§ → D§`,
satisfying the expected functor laws `id§ = id` (literally `gMap_inSharp_pairSharp_eq_idMap`) and
`(f' ∘ f)§ = f'§ ∘ f§` (`dsharpMap_comp`, via the catamorphism-uniqueness lemma
`gMap_eq_of_satisfies`, exactly parallel to `gMap_selfComp_eq_of_isRetraction`'s proof but without
needing a retraction hypothesis: composing two *different* maps needs no idempotence).
`aSharpInner a` is the special case `D₀ = D₁ = U`, `f := a`. -/

section DsharpFunctor

variable {γ δ ε : Type*} {D₀ : NeighborhoodSystem γ} {D₁ : NeighborhoodSystem δ}
  {D₂ : NeighborhoodSystem ε}
variable (hD₀ : ∀ X, D₀.mem X → X.Nonempty) (hD₁ : ∀ X, D₁.mem X → X.Nonempty)
  {hD₂ : ∀ X, D₂.mem X → X.Nonempty}


end DsharpFunctor

/-! ## Exercise 8.21(c): `D_{a§} ≅ (D_a)§`

For a *finitary projection* `a` of `U`, transport `iSharp`/`jSharp` through `dsharpMap`'s
functorial action on the injection/projection pair `(fixedNbhd_subsystem a).inj/.proj` of
`D_a := fixedNbhd a ◁ U` (Proposition 6.12), producing a genuine projection pair
`I : (D_a)§ → U`, `J : U → (D_a)§`. The functor laws `dsharpMap_id`/`dsharpMap_comp` turn
`j_a ∘ i_a = I_{D_a}` (Proposition 6.12's own `proj_comp_inj`) into `J ∘ I = I_{(D_a)§}`
immediately, and `i_a ∘ j_a = a` (Theorem 8.6's `inj_comp_proj_eq_self`, using that `a` is a
finitary projection) into `I ∘ J = a§` — exactly `aSharp`'s own definition, once one notices
`aSharpInner a` is literally `dsharpMap` applied to `i_a ∘ j_a = a`.
`elementIsoOfProjectionPair` (`Proposition810b.lean`) then hands us the isomorphism directly, in
the same "domain of a projection = its `toElementMap`-fixed-point set" convention already used
throughout `Proposition810b.lean` for `D_{a+b} ≅ D_a+D_b` etc. -/


end DomainTheory.NeighbourhoodSystems
