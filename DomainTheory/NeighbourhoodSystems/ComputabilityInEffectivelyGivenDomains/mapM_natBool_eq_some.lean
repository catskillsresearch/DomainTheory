module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.boolNat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.natBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.natBool_eq_some_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

theorem mapM_natBool_eq_some (l : List ℕ) (σ : List Bool)
    (h : l.mapM natBool = some σ) : l = σ.map boolNat := by
  induction l generalizing σ with
  | nil => rw [List.mapM_nil] at h; simpa using h.symm
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hnx : natBool x with
    | none => simp [hnx] at h
    | some b =>
      cases htx : xs.mapM natBool with
      | none => simp [hnx, htx] at h
      | some ys =>
        simp only [hnx, htx] at h
        obtain rfl : σ = b :: ys := by simpa using h.symm
        simp [ih ys htx, (natBool_eq_some_iff x b).mp hnx]

end Exercise722

end DomainTheory.NeighbourhoodSystems
