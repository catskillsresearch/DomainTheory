/-ai
The two-point domain does not embed as a subdomain of its smash product with the one-point unit.

An embedding would supply a subsystem of the smash and an order isomorphism from the two-point domain onto that subsystem. Every neighbourhood of the subsystem equals its master: the subsystem inclusion sends it into the smash, every smash neighbourhood with the unit equals the smash master, and the subsystem master agrees with that master. A system whose only neighbourhood is its master has a single element. The principal element on the singleton of the empty string differs from the principal element on the universal set. The former contains that singleton, so equality would place the singleton in the master principal and force the universal set to be contained in the singleton. The string false lies in the universal set, and would then equal the empty string. The isomorphism would identify the two principal elements, because the subsystem has only one element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.subsingleton_element_of_only_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.otimes_unitPt_collapse

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}






variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}





















/-- **Exercise 6.27 (6).** `𝒟 ⊴ 𝒟 ⊗ ℰ` does **not** hold for all `𝒟, ℰ`: take `𝒟` two-point and
`ℰ = 𝟙`. Then `𝒟 ⊗ 𝟙` has a one-point element lattice while `𝒟` has two, so no isomorphism onto a
subsystem can exist. -/
theorem not_trianglelefteq_otimes :
    ¬ (twoPt ⊴ otimesTok twoPt unitPt) := by
  rintro ⟨D', hsub, ⟨e⟩⟩
  have hD'only : ∀ X, D'.mem X → X = D'.master := by
    intro X hX
    rw [otimes_unitPt_collapse X (hsub.sub hX)]; exact hsub.master_eq.symm
  have hss : Subsingleton D'.Element := subsingleton_element_of_only_master hD'only
  have hPmem : twoPt.mem ({[]} : Set Str) := Or.inr rfl
  have hne : twoPt.principal hPmem ≠ twoPt.principal twoPt.master_mem := by
    intro heq
    have h1 : (twoPt.principal hPmem).mem ({[]} : Set Str) := ⟨hPmem, subset_rfl⟩
    rw [heq] at h1
    obtain ⟨-, h2⟩ := h1
    exact absurd (Set.mem_singleton_iff.mp (h2 (Set.mem_univ ([false] : Str))) :
      ([false] : Str) = []) (by decide)
  exact hne (e.injective (hss.allEq (e (twoPt.principal hPmem))
    (e (twoPt.principal twoPt.master_mem))))

end Exercise627
end DomainTheory.NeighbourhoodSystems
