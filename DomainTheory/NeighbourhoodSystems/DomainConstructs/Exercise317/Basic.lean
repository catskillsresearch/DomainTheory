/-ai
This file gathers and re-exports the encoding of binary strings into the infinite iterate of the truth system: the truth system and its tokens, bit neighbourhoods, the encoding set and its fiber and monotonicity lemmas, and the encoding and decoding maps.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.bitNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.f
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.g
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.T
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.Token
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.bitNbhd_mem
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.T_nbhd_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.mem_encSet
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.fiber_encSet_some
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.fiber_encSet_none
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet_mem
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet_anti
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet_agree
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.comparable_of_agree

@[expose] public section

/-!
# Exercise 3.17 (Scott 1981, PRG-19, §3) — `B` is a retract of `T^∞`

Using the binary system `B` (Example 1.B) and the three-element truth system `T` (Example 1.2),
Scott asks for a **one-one** approximable map `f : B → T^∞` and a map `g : T^∞ → B` with

`g ∘ f = I_B`  and  `f ∘ g ⊑ I_{T^∞}`,

i.e. `B` is a *retract* of `T^∞` (`f` a section, `g` a retraction). He then asks whether `B ≅ T^∞`
and `B ≅ T × B` (the point of the exercise being that retract ≠ isomorphism here).

**The encoding.** A binary string `σ = b₀b₁…b_{k-1}` (a neighbourhood `σΣ*` of `B`) is sent to the
`T^∞`-neighbourhood `encSet σ` that pins copy `i` to the truth value `bitNbhd bᵢ` (`{0}` for `false`,
`{1}` for `true`) for `i < k`, and leaves copies `i ≥ k` free (`Δ_T`). Concretely `encSet σ` is the
*pointwise* set `{(i, t) ∣ ∀ b, σ[i]? = some b → t ∈ bitNbhd b}`.

* `f` relates `σΣ*` to every `T^∞`-neighbourhood weaker than `encSet σ`;
* `g` relates a `T^∞`-neighbourhood `W` to `τΣ*` exactly when `W ⊆ encSet τ`, i.e. `W` already pins
  the first `|τ|` copies to `τ` (decoding the longest gap-free prefix).

`g ∘ f = I_B` (`gf_eq_id`) — decoding recovers the prefix, the key being
`prefix_of_encSet_subset` (`encSet σ ⊆ encSet τ ⟹ τ ⪯ σ`), which uses that `T`-neighbourhoods are
non-empty. `f ∘ g ⊑ I_{T^∞}` (`fg_le_id`) holds because re-encoding a decoded element can only lose
the post-gap information. Hence `f` is one-one (`f_injective`).
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap





/-! ### The encoding set `encSet σ`. -/








/-! ### Comparability and the prefix recovery lemma. -/



/-! ### The section `f : B → T^∞` and retraction `g : T^∞ → B`. -/



/-! ### `g ∘ f = I_B` and `f ∘ g ⊑ I_{T^∞}`. -/
end DomainTheory.NeighbourhoodSystems.Exercise317
