module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.retractBasis_directed

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem retractBasis_directedSubset {a : Pomega} (ha : Retract a)
    (x : Fixpoints (funOf a)) :
    DirectedSubset (retractBasis a x) := by
  have h := retractBasis_directed ha x
  refine ⟨⟨h.out.1, ?_⟩⟩
  intro y hy z hz
  obtain ⟨w, hw, hyw, hzw⟩ := h.out.2 hy hz
  exact ⟨w, hw, hyw, hzw⟩

end DomainTheory.DataTypesAsLattices
