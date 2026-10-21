/-ai
The ideal of finite approximants of the element determined by an ideal I of finite elements is I itself.

By extensionality of ideals it is enough to compare carriers. If a finite element y is a finite approximant of the element determined by I, then y lies under that element. Writing y as the closure of a consistent finite set, compactness of closures against the nonempty directed carrier of I supplies a member of that carrier above the closure. That member is a finite element of I, and the lower-set property of I puts y in I. Conversely, a member of I lies under the element determined by I, so it is a finite approximant of that element.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
import all Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.FiniteElement
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.mem_finiteApproximants_of_le
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.le_of_mem_finiteApproximants
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.toIdeal
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.idealCarrier
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.nonempty_idealCarrier
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.directed_idealCarrier
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.ofIdeal
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.le_ofIdeal_of_mem

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45.compact_closure
@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem toIdeal_ofIdeal (I : Ideal (FiniteElement A)) : toIdeal A (ofIdeal A I) = I := by
  refine Ideal.ext ?_
  ext y
  constructor
  · intro hy
    have hle : (y : A.Element) ≤ ofIdeal A I := le_of_mem_finiteApproximants A hy
    rcases y with ⟨yval, ⟨u, hu, rfl⟩⟩
    obtain ⟨z, hz, hcle⟩ :=
      A.compact_closure (idealCarrier A I) (nonempty_idealCarrier A I)
        (directed_idealCarrier A I) hu hle
    obtain ⟨z', hz', rfl⟩ := hz
    exact I.lower hcle hz'
  · intro hy
    exact mem_finiteApproximants_of_le A (le_ofIdeal_of_mem A hy)

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
