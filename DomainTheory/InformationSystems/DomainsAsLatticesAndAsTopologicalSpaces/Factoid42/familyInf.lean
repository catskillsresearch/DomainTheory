module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42.familyInfCarrier

@[expose] public section

namespace DomainTheory.InformationSystems
namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Factoid 4.2.** Meet of a nonempty family of elements (set-theoretic intersection). -/
def familyInf (S : Set sys.Element) (hne : S.Nonempty) : sys.Element where
  carrier := sys.familyInfCarrier S
  consistent := by
    intro Y hY
    obtain ⟨x₀, hx₀⟩ := hne
    have hYx : (Y : Set α) ⊆ x₀.carrier := fun a ha => (hY ha) x₀ hx₀
    exact x₀.consistent Y hYx
  closed := by
    intro Y a hY hEnt x hx
    have hYx : (Y : Set α) ⊆ x.carrier := fun b hb => (hY hb) x hx
    exact x.closed Y a hYx hEnt

theorem familyInf.le (S : Set sys.Element) (hne : S.Nonempty) {x : sys.Element}
    (hx : x ∈ S) : sys.familyInf S hne ≤ x :=
  fun _a ha => ha x hx

end InfoSys
end DomainTheory.InformationSystems
