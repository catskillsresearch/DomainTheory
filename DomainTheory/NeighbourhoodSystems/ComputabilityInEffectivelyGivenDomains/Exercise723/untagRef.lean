/-ai
The reference decoder sends a code to a list of natural numbers and a value so that tag of that list at that value returns the code. If the first component of the numeral decoding is zero, the result is the empty list paired with the second component. Otherwise it conses the predecessor of the first component onto the list returned by the recursive call on the second component, and keeps that call's value. The recursive argument is smaller because the numeral of the two components recovers the code, the first component is a successor, and the successor bound on numerals forces the second component below the code.
ai-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.halfIter_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.mem_elemSet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic.notation16

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive

open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)

open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

/-- `untagRef c = (ns, m)` with `tag ns m = c` (`tag_untagRef`). -/
def untagRef (c : ℕ) : List ℕ × ℕ :=
  if _h : (unnum c).1 = 0 then ([], (unnum c).2)
  else
    have hlt : (unnum c).2 < c := by
      have heq : num (unnum c).1 (unnum c).2 = c := by
        have h := numP_unnum c
        simpa [numP] using h
      obtain ⟨k, hk⟩ : ∃ k, (unnum c).1 = k + 1 := ⟨(unnum c).1 - 1, by omega⟩
      rw [hk] at heq
      have hb := num_succ_left_gt k (unnum c).2
      omega
    (((unnum c).1 - 1) :: (untagRef (unnum c).2).1, (untagRef (unnum c).2).2)
termination_by c
decreasing_by all_goals exact hlt

end DomainTheory.NeighbourhoodSystems.Exercise723
