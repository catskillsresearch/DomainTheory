/-ai
This file gathers and re-exports the catamorphism relation of the universal strict map, the approximable map it determines, the certificate step and its evaluator, the domain, codomain, and master laws, the separation of a zero embedding from a paired embedding, the inversion lemmas at the master neighbourhood, at a zero embedding, and at a paired embedding, monotonicity and closure under intersection of the target, and the identification of the map's relation with the catamorphism relation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.GRel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gEval
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_dom
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_cod
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.embZero_ne_embPair_of_memS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_gamma_inv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_embZero_inv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_embPair_inv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_mono
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_interRight
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gMap_rel

@[expose] public section

/-!
# Exercise 7.17 (Scott 1981, PRG-19, §7) — Part 2: the universal strict mapping `g : D^§ → E`

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII.

> **Exercise 7.17.** … Prove also that if `E` is effectively given and `u : D → E` and
> `v : E × E → E` are computable, then the unique strict mapping `g : D^§ → E`, where
> `g(in x) = u(x)` and `g(pair(y, z)) = v(g(y), g(z))`, is a computable mapping.

This is the *catamorphism* (fold) out of the tree algebra `D^§ ≅ D + (D^§ × D^§)` (Example 6.1) into a
`T`-algebra structure `(E, [u, v])`. We build `g` directly as a neighbourhood relation `GRel u v`,
defined by recursion on the three `D^§`-neighbourhood shapes:

* `Γ            ↦ Δ_E`              (strict: `⊥ ↦ ⊥`);
* `0·X          ↦ u`'s relation on `X`;
* `1·P ∪ 2·Q    ↦ ∃ Z₁ Z₂, P g Z₁ ∧ Q g Z₂ ∧ ⟨Z₁,Z₂⟩ v Z`.

There is **no separate "top" clause**: because `u` and `v` are approximable (they relate `Δ ↦ Δ`),
`GRel u v W Δ_E` already holds for every `W ∈ 𝒟^§` (`gRel_master`). The three clauses give an
honest `ApproximableMap` (`gMap`), with the two defining equations
`gMap_in : g(in x) = u(x)` and `gMap_pair : g(pair y z) = v(⟨g y, g z⟩)`, and strictness
`gMap_strict`.

The **computability** (`gMap_isComputable`) is the heart of the exercise. The index relation
`R m k := GRel u v (V_m)(Y_k)` (`V` = `Vsharp` the `D^§` enumeration, `Y` = `Q`'s enumeration of `E`)
satisfies the recursive characterisation `gRel_index_*`. We realise it as the recursively-enumerable
existential `∃ cert` over a **stack-machine certificate**: a derivation is a postorder *program* of
push/pop instructions verified by a single primitive-recursive `foldCode`, exactly the device used for
`fix` in Theorem 7.6. (A per-`Vsharp`-index memo — as in `dsharpStep` — does **not** work here, since
`R` is a genuine relation: the same sub-neighbourhood may be folded to *different* outputs in different
parts of the tree, so the certificate must mirror the derivation tree.)

Data and the two equations are choice-free `⊆ {propext, Quot.sound}`; the `ComputableMap` proof and
the inversion lemmas route through `Classical` (`Set` reasoning over the arbitrary carriers `α`, `β`),
as everywhere in this layer.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

/-! ### The catamorphism relation `GRel u v`. -/

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-! ### Shape inversion lemmas. -/

/-! ### The `ApproximableMap` laws. -/

/-! ### The two defining equations and strictness. -/

/-! ### `Nat.pair` monotonicity (for the certificate measure).

The certificate is read by the `Proposition77` course-of-values memo (`gOf`/`rtbl`/`listGet`) over the
combined code `w = ⟨v, cert⟩`. A node's child code `⟨a.i, child-cert⟩` must be strictly `< w`. The
`Vsharp`-index strictly decreases (`a.i < v`) while the child-cert is only `≤ cert`, so we need
`Nat.pair` strictly monotone in its first argument (second fixed) and monotone in its second. -/

/-! ### The stack-machine / course-of-values certificate evaluator.

`R n m := GRel u v (V_n)(Q_m)` (`V` = `Vsharp`, `Q` = `Q.X`) satisfies the recursion: `n = 0`
folds to `Δ_E`; `n = 2a+1` folds via `u`; `n = 2a+2` is `∃ Z₁ Z₂, V_{a.1} g Z₁ ∧ V_{a.2} g Z₂ ∧
⟨Z₁,Z₂⟩ v Q_m`. A *derivation* is a finite tree (the same `V` may fold to *different* outputs in
different positions, so the witness must mirror the tree). We encode it as a single `cert` and verify
it with the `Proposition77` memo `gOf`/`rtbl` over `w = ⟨v, cert⟩`: at each node the two children's
results (`okBit`, `outIdx`) are read from the memo table by `listGet`. The step is fed the four
primitive-recursive `{0,1}`/index functions `fe` (`Q`-equality-to-`Δ`), `fU`/`fV` (the deciders of
`u`/`v`'s r.e. relations), and `mIdx` (`Q`'s master index). -/

/-! ### Computability of `g`. -/
end Exercise717
end DomainTheory.NeighbourhoodSystems
