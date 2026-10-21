/-ai
The directed union of a nonempty directed family of elements is the element whose neighbourhoods are the neighbourhoods of members of the family. The master belongs to any chosen member. The intersection of neighbourhoods from two members belongs to a common upper bound in the family. An upward enlargement stays in the same member.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic.Set
import all Mathlib.Tactic.Set
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ApproximableMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace NeighborhoodSystem

/-- **Directed union of filters.** The union `⋃ S = {Z ∣ ∃ s ∈ S, Z ∈ s}` of a *non-empty directed*
family `S` of elements (any two members have an upper bound in `S`) is again an element. The only
non-trivial law is `inter_mem`: given `Z ∈ a` and `Z' ∈ b`, an upper bound `c ⊇ a, b` contains both,
hence `Z ∩ Z' ∈ c`. (Generalizes `chainUnion` of Exercise 1.24 from chains to directed sets; this is
the construction behind Exercise 2.11 and Scott's finiteness argument in Theorem 2.7.) -/
def sSupDirected (V : NeighborhoodSystem α) (S : Set V.Element) (hne : S.Nonempty)
    (hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c) : V.Element where
  mem Z := ∃ s ∈ S, s.mem Z
  sub := fun ⟨s, _, hs⟩ => s.sub hs
  master_mem := by obtain ⟨s, hs⟩ := hne; exact ⟨s, hs, s.master_mem⟩
  inter_mem := by
    rintro Z Z' ⟨a, haS, haZ⟩ ⟨b, hbS, hbZ⟩
    obtain ⟨c, hcS, hac, hbc⟩ := hdir a haS b hbS
    exact ⟨c, hcS, c.inter_mem (hac Z haZ) (hbc Z' hbZ)⟩
  up_mem := by
    rintro Z Z' ⟨a, haS, haZ⟩ hZ' hZZ'
    exact ⟨a, haS, a.up_mem haZ hZ' hZZ'⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
