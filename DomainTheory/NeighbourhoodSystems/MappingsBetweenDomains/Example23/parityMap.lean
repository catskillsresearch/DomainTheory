/-ai
The parity map relates a binary neighbourhood X to a neighbourhood Y of the two-token domain when X is the cone of a prefix and Y belongs to the element selected by scanning that prefix. Domain and codomain membership follow from the cone and from that element. The empty prefix, whose scan selects bottom, relates the master neighbourhoods. On the right, a cone has one prefix, so the two scan values agree and their element is closed under intersection. For monotonicity, the smaller domain neighbourhood is a longer cone, the scanned value only rises along that prefix, and the codomain neighbourhood may be enlarged inside the selected element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.T
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.botElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.valElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan_true
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.scan_false
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.valElt_scan_mono

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **Example 2.3 — the parity mapping `f : B → T`.** `X f Y` iff `X` is the cone `σΣ*` of some
prefix `σ` and `Y` is approximated by the parity verdict `valElt (scan σ)`. Definition 2.1:
(i) the empty prefix scans to `none = ⊥`, and `⊥` contains `Δ_T`; (ii) for a fixed cone the verdict
is a *single* filter (cones have a unique prefix), closed under `∩`; (iii) extending the prefix only
sharpens the verdict (`valElt_scan_mono`). -/
def parityMap : ApproximableMap B T where
  rel X Y := ∃ σ, X = cone σ ∧ (valElt (scan σ)).mem Y
  rel_dom := fun ⟨σ, hX, _⟩ => ⟨σ, hX⟩
  rel_cod := fun ⟨_, _, hY⟩ => (valElt _).sub hY
  master_rel := by
    refine ⟨[], cone_nil.symm, ?_⟩
    show (botElt).mem Example12.master
    rfl
  inter_right := by
    rintro X Y Y' ⟨σ, hX, hY⟩ ⟨σ', hX', hY'⟩
    have hσ : σ = σ' := cone_injective (hX ▸ hX')
    subst hσ
    exact ⟨σ, hX, (valElt (scan σ)).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' ⟨σ, hX, hY⟩ hX'X hYY' hX'mem hY'mem
    obtain ⟨σ', hX'cone⟩ := hX'mem
    have hpre : σ <+: σ' := by
      apply cone_subset_cone.mp
      rw [← hX'cone, ← hX]; exact hX'X
    have hYmem' : (valElt (scan σ)).mem Y' := (valElt (scan σ)).up_mem hY hY'mem hYY'
    exact ⟨σ', hX'cone, valElt_scan_mono hpre Y' hYmem'⟩

end DomainTheory.NeighbourhoodSystems.Example23
