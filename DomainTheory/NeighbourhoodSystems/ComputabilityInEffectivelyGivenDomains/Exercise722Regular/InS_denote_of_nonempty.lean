module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
import all Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722











/-- **Soundness.** A *non-empty* denotation is a member of `S`. (Non-emptiness is needed only for the
intersection generator, where `InS.inter` demands it; it propagates down to subterms because
`concat`/`∩` are non-empty only when their parts are.) -/
theorem InS_denote_of_nonempty : ∀ {e : SExpr}, (denote e).Nonempty → InS (denote e)
  | .sigma, _ => InS.univ
  | .single σ, _ => InS.singleton σ
  | .cat a b, h => by
    rw [denote_cat] at h ⊢
    obtain ⟨w, x, hx, y, hy, _⟩ := h
    exact InS.mul (InS_denote_of_nonempty ⟨x, hx⟩) (InS_denote_of_nonempty ⟨y, hy⟩)
  | .cap a b, h => by
    rw [denote_cap] at h ⊢
    have ha : (denote a).Nonempty := h.mono Set.inter_subset_left
    have hb : (denote b).Nonempty := h.mono Set.inter_subset_right
    exact InS.inter (InS_denote_of_nonempty ha) (InS_denote_of_nonempty hb) h

end Exercise722
end DomainTheory.NeighbourhoodSystems
