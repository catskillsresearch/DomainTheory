/-ai
The order isomorphism of Exercise 1.16 sends each cofinite filter to its set of excluded points and sends each set of excluded points to the filter of cofinite neighbourhoods whose complements lie in that set. The two inversion theorems supply the inverse laws. Filter inclusion holds exactly when the excluded sets are included. If the excluded set of the first filter is contained in that of the second and a neighbourhood belongs to the first, its finite complement consists of excluded points of the second, so the reconstruction lemma returns the neighbourhood itself to the second filter. Conversely, an excluded point is membership of a singleton complement, which the filter inclusion carries across.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteSystem_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.ofExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_ofExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.toExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_toExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_compl_singleton
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_compl_of_finite
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.subset_compl_singleton
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.toExcluded_ofExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.ofExcluded_toExcluded

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

/-- **Exercise 1.16 — `|𝒟| ≅ (𝒫(ℕ), ⊆)`.** The filter `x` corresponds to its excluded-point
set `toExcluded x`; inclusion of filters matches inclusion of excluded sets. -/
def cofiniteIso : cofiniteSystem.Element ≃o Set ℕ where
  toFun := toExcluded
  invFun := ofExcluded
  left_inv := ofExcluded_toExcluded
  right_inv := toExcluded_ofExcluded
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h Y hY
      have hfin : Yᶜ.Finite := x.sub hY
      have hsub : Yᶜ ⊆ toExcluded x' := by
        intro n hn
        have hx : x.mem (({n} : Set ℕ)ᶜ) :=
          x.up_mem hY (mem_compl_singleton n) (subset_compl_singleton hn)
        exact h (mem_toExcluded.mpr hx)
      have h2 := mem_compl_of_finite x' hfin (fun n hn => mem_toExcluded.mp (hsub hn))
      rwa [compl_compl] at h2
    · intro h n hn
      exact mem_toExcluded.mpr (h _ (mem_toExcluded.mp hn))

end Cofinite

end DomainTheory.NeighbourhoodSystems
