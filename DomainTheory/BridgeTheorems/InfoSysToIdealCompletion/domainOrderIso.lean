/-ai
The order isomorphism of an information system with the ideal completion of its finite elements sends an element to the ideal of its finite approximants and sends an ideal to the element it determines. The two composites are the identity. If the ideal of x is contained in the ideal of y, then x, rewritten as the directed supremum of its finite approximants, lies under y, because each finite approximant of x belongs to the ideal of y and therefore lies under the element determined by that ideal. The converse is monotonicity of the ideal associated with an element.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
import all Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.FiniteElement
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.toIdeal
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.ofIdeal
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.le_ofIdeal_of_mem
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.ofIdeal_toIdeal
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.toIdeal_ofIdeal
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.toIdeal_mono

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- Order isomorphism: domain elements ↔ ideals of finite elements. -/
noncomputable def domainOrderIso : A.Element ≃o Ideal (FiniteElement A) where
  toFun := toIdeal A
  invFun := ofIdeal A
  left_inv := ofIdeal_toIdeal A
  right_inv := toIdeal_ofIdeal A
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      -- x ≤ y from toIdeal x ≤ toIdeal y via algebraicity
      rw [← ofIdeal_toIdeal A x, ← ofIdeal_toIdeal A y]
      refine A.directedSup_le _ _ _ ?_
      intro z hz
      obtain ⟨z', hz', rfl⟩ := hz
      exact le_ofIdeal_of_mem A (h hz')
    · exact toIdeal_mono A

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
