module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.bracket
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.tokenSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.toToken
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.ofToken
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.tokenIso
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.mem_bracket
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.bracket_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.principal_mem_bracket
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.bracket_inter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.bracket_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.bracket_injective
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.tokenSystem_mem

@[expose] public section

/-!
# Theorem 1.10 (Scott 1981, PRG-19, §1) — the element-token system `{[X]}`

Given any neighbourhood system `𝒟`, Scott replaces the tokens `Δ` by the *elements* `|𝒟|`
themselves: for `X ∈ 𝒟` put

`[X] = {x ∈ |𝒟| ∣ X ∈ x}`,

the set of elements that contain `X`. The family `{[X] ∣ X ∈ 𝒟}` is a neighbourhood system over
`|𝒟|`, and it determines a domain *isomorphic* to `|𝒟|` (Definition 1.9). "The rôle of the tokens
is simply to keep the inclusions (and intersections) of neighbourhoods sorted out."

We prove Scott's four facts:

* (1) `[Δ] = |𝒟|`                              — `bracket_master`;
* (2) `X, Y` consistent in `𝒟` iff `[X]∩[Y] ≠ ∅` — `bracket_inter_nonempty_iff`;
* (3) `[X] ∩ [Y] = [X ∩ Y]` (for `X, Y ∈ 𝒟`)   — `bracket_inter`;
* (4) `↑X ∈ [X]`                               — `principal_mem_bracket`;

together with the one-one (`bracket_injective`), inclusion-preserving (`bracket_subset_iff`)
correspondence `X ↦ [X]`, and finally the induced order-isomorphism `tokenIso : |𝒟| ≃o |{[X]}|`,
giving `𝒟 ≅ᴰ tokenSystem` (`isomorphic_tokenSystem`).

Everything is constructive (`[propext, Quot.sound]`): `[X]`-membership is just `x.mem X`, and the
filter laws mirror the constructive proofs for `principal`.
-/

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)








/-! ### The token system `{[X]}` and the isomorphism. -/





end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
