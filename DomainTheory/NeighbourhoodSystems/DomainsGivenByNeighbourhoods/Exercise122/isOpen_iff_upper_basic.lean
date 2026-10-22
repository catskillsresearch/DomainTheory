/-ai
A set of elements is open if and only if it is upward closed under approximation and every one of its points has a basic neighbourhood contained in the set.

An open set is upward closed, and openness is already the basic-neighbourhood condition. In the other direction, the basic-neighbourhood condition is openness.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Topology.Inseparable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.isOpen_isUpperSet

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.22 (characterization of open sets).** A subset `𝒰 ⊆ |𝒟|` is open iff
(i) it is upward closed under `⊑`, and (ii) every point of `𝒰` has a basic neighbourhood `[X]`
(`X ∈ x`) contained in `𝒰`. -/
theorem isOpen_iff_upper_basic (U : Set V.Element) :
    IsOpen U ↔
      (∀ ⦃x y : V.Element⦄, x ∈ U → x ≤ y → y ∈ U) ∧
        (∀ x ∈ U, ∃ X, x.mem X ∧ V.basicOpen X ⊆ U) := by
  constructor
  · intro hU
    exact ⟨V.isOpen_isUpperSet hU, hU.out⟩
  · rintro ⟨_, h2⟩
    exact ⟨h2⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
