/-ai
An active index decodes to some expression.

Unfold activity and split on decoding. Failure contradicts activity, and success supplies the expression.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

theorem ssysActive_exists_decode {n : ℕ} (hn : ssysActive n = true) :
    ∃ e, SExpr.decode n = some e := by
  unfold ssysActive at hn
  cases hdec : SExpr.decode n with
  | none => simp [hdec] at hn
  | some e => exact ⟨e, rfl⟩

end Exercise722

end DomainTheory.NeighbourhoodSystems
