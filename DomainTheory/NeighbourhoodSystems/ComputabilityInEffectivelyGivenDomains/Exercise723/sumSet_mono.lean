/-ai
The Minkowski sum is monotone in each argument. If one set of natural numbers is contained in a second and a third is contained in a fourth, the sum of the first and third is contained in the sum of the second and fourth.

A witness that splits the summand into a member of the first set and a member of the third remains a witness after the two inclusions.
ai-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.halfIter_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic.notation16

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive

open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)

open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

theorem sumSet_mono {X X' Y Y' : Set ℕ} (hX : X ⊆ X') (hY : Y ⊆ Y') : X +ˢ Y ⊆ X' +ˢ Y' := by
  rintro k ⟨a, ha, b, hb, rfl⟩
  exact ⟨a, hX ha, b, hY hb, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise723
