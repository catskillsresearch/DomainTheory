/-ai
The intersection of two neighbourhoods of Example 1.4 equals one of the seven neighbourhoods, or is empty.

Classify both arguments by the membership criterion and rewrite each intersection by the corresponding intersection identity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf10
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf11
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.master_inter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.inter_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left_inter_leaf00
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00_inter_left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left_inter_leaf01
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01_inter_left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right_inter_leaf10
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf10_inter_right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right_inter_leaf11
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf11_inter_right
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left_inter_right
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right_inter_left
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left_inter_leaf10
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf10_inter_left
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left_inter_leaf11
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf11_inter_left
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right_inter_leaf00
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00_inter_right
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right_inter_leaf01
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01_inter_right
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00_inter_leaf01
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01_inter_leaf00
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00_inter_leaf10
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf10_inter_leaf00
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00_inter_leaf11
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf11_inter_leaf00
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01_inter_leaf10
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf10_inter_leaf01
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01_inter_leaf11
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf11_inter_leaf01
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf10_inter_leaf11
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf11_inter_leaf10

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

/-- Every binary intersection of two neighbourhoods is again a neighbourhood, or is empty
(the tree's "nested-or-disjoint" property). -/
theorem inter_eq (X Y : Set Token) (hX : mem X) (hY : mem Y) :
    X ∩ Y = master ∨ X ∩ Y = left ∨ X ∩ Y = right ∨ X ∩ Y = leaf00 ∨
      X ∩ Y = leaf01 ∨ X ∩ Y = leaf10 ∨ X ∩ Y = leaf11 ∨ X ∩ Y = (∅ : Set Token) := by
  rcases (mem_iff X).mp hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [master_inter, inter_master, Set.inter_self,
      left_inter_right, right_inter_left, left_inter_leaf10, leaf10_inter_left,
      left_inter_leaf11, leaf11_inter_left, right_inter_leaf00, leaf00_inter_right,
      right_inter_leaf01, leaf01_inter_right, leaf00_inter_leaf01, leaf01_inter_leaf00,
      leaf00_inter_leaf10, leaf10_inter_leaf00, leaf00_inter_leaf11, leaf11_inter_leaf00,
      leaf01_inter_leaf10, leaf10_inter_leaf01, leaf01_inter_leaf11, leaf11_inter_leaf01,
      leaf10_inter_leaf11, leaf11_inter_leaf10,
      left_inter_leaf00, leaf00_inter_left, left_inter_leaf01, leaf01_inter_left,
      right_inter_leaf10, leaf10_inter_right, right_inter_leaf11, leaf11_inter_right,
      true_or, or_true]

end DomainTheory.NeighbourhoodSystems.Example14
