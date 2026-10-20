module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.Basic

@[expose] public section


set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems



namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)








/-- `sInf F ⊑ x` for every `x ∈ F`. -/
theorem sInf_le (F : Set V.Element) (hF : F.Nonempty) {x : V.Element} (hx : x ∈ F) :
    V.sInf F hF ≤ x :=
  fun _ h => h x hx

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
