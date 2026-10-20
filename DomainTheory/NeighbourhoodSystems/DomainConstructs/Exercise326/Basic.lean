module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.condGuard
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.TD
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.zero_ne_one
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.zero_ne_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.one_ne_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.Tmem_eq_zero
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.Tmem_eq_one
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.condGuard_zero
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.condGuard_one
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.condGuard_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond_components

@[expose] public section

/-!
# Exercise 3.26 (Scott 1981, PRG-19, §3) — the conditional operator `cond`

Scott asks: for every domain `D` there is an approximable mapping

`cond : T × D × D → D`

(the *conditional operator*) satisfying

* `cond(true,  x, y) = x`,
* `cond(false, x, y) = y`,
* `cond(⊥,     x, y) = ⊥`.

Here `T` is the truth domain of Example 1.2 (`Example12.neighborhoodSystem`), whose neighbourhoods
are `{Δ, {0}, {1}}` with `true = ↑{0}` (`Example23.trueElt`), `false = ↑{1}` (`falseElt`) and
`⊥ = {Δ}` (`botElt`). The product `T × D × D` is the tagged product of Exercise 3.14, modelled here
as `prod T (prod V V)` over the token type `T.Token ⊕ (α ⊕ α)`; a neighbourhood is
`0C ∪ 10X ∪ 110Y`, recovered from `W` by the projections `C = inl⁻¹ W`, `X = inl⁻¹ inr⁻¹ W`,
`Y = inr⁻¹ inr⁻¹ W`.

Scott's hint gives the relation directly:

```
0C ∪ 10X ∪ 110Y  cond  Z   iff   0 ∈ C and X ⊆ Z,  or
                                  1 ∈ C and Y ⊆ Z,  or
                                  0, 1 ∈ C and Δ ⊆ Z.
```

Since `T = {Δ, {0}, {1}}`, the three guards on `C` are *mutually exclusive and exhaustive*:
`0 ∈ C` (alone) means `C = {0}`, `1 ∈ C` (alone) means `C = {1}`, and `0, 1 ∈ C` means `C = Δ`. We
therefore phrase the relation with explicit equalities `C = {0} / {1} / Δ` (`condGuard`), which is
mathematically identical to Scott's membership form but makes the case analysis transparent and the
three identities clean.

Everything is **choice-free** in spirit; the only classical input is inherited from `T` (Example 1.2)
and from the project's `ext_of_toElementMap`/`Element.ext` machinery, as elsewhere in §3.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}


/-! ### Token-level facts about `T`'s three neighbourhoods `{0}`, `{1}`, `Δ`. -/






/-! ### The conditional relation. -/


variable (V : NeighborhoodSystem α)






@[simp] theorem cond_rel {W : Set (Example12.Token ⊕ (α ⊕ α))} {Z : Set α} :
    (cond V).rel W Z ↔ (prod TD (prod V V)).mem W ∧ V.mem Z ∧ condGuard V W Z := Iff.rfl

/-! ### Elementwise characterization, and the three defining identities. -/
end DomainTheory.NeighbourhoodSystems.Exercise326
