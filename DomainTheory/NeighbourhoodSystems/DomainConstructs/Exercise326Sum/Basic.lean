module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.condSumEmb
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.condSum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichGuard
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.Tmem_ge_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.Tmem_ge_zero
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.Tmem_ge_one
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.inter_in_zeroset
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.inter_in_oneset
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichGuard_left
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichGuard_right
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichGuard_masterC

@[expose] public section

/-!
# Exercise 3.26, continued (Scott 1981, PRG-19, §3) — the sum-valued conditional and `which`

This module completes Exercise 3.26 with the two follow-up operators Scott asks for:

* the **sum-valued conditional** `condSum : T × D₀ × D₁ → D₀ + D₁`, routing `true → in₀`,
  `false → in₁`, `⊥ → ⊥`. It is obtained for free by *composition*: feeding the two inputs through
  the injections `in₀, in₁` into the common domain `S = D₀ + D₁` and then applying the conditional
  `cond S : T × S × S → S` of Exercise 3.26. The three identities follow from `cond_true/false/bot`.

* the discriminator **`which : D₀ + D₁ → T`** reading the tag (`0X ↦ true`, `1Y ↦ false`,
  `Λ ↦ ⊥`), together with Scott's identity

  `cond(which x, in₀(out₀ x), in₁(out₁ x)) = x`   for all `x ∈ |D₀ + D₁|`.

The discriminator is built directly as a neighbourhood relation; its three guards on the truth
component are mutually exclusive because the three forms of a sum-neighbourhood (`Λ`-master, left
copy, right copy) are mutually exclusive (Exercise 3.18, using non-emptiness).
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-! ### The sum-valued conditional `condSum`. -/



/-! ### The discriminator `which : D₀ + D₁ → T`. -/











/-! ### Membership facts and the composite identity. -/
end DomainTheory.NeighbourhoodSystems.Exercise326
