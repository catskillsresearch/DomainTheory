/-ai
The directed join of the truncations is the identity map on the infinite iterate.

The maps agree on an element once they contain the same neighbourhoods. If a neighbourhood of the descent is witnessed at stage n, the n-th truncation lies below the element: rewritten as the sequence of its components, the truncation keeps those components before n and is bottom afterwards, so the neighbourhood belongs to the element. Conversely, if the neighbourhood belongs to the element, the cofinite-master condition supplies an index N beyond which every fibre is the master, and every component lies in the corresponding fibre. At stage N the truncation contains the neighbourhood, using the component before N and, from N onward, the bottom, which contains the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.component_bot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.imap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descSeq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise618.descMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_toElementMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.rho_apply

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **`⋃ₙ ρₙ = I`.** Every `z` is the directed union of its truncations: the cofinite-`Δ` structure
of `𝒟^∞` means each neighbourhood of `z` is already realised by a finite truncation. -/
theorem iSupRho_eq_id : descMap (imap V) = idMap (iterSys V) := by
  apply ext_of_toElementMap
  intro z
  rw [toElementMap_idMap]
  apply Element.ext
  intro Y
  rw [descMap_toElementMap]
  constructor
  · rintro ⟨n, hn⟩
    have hle : (descSeq (imap V) n).toElementMap z ≤ z := by
      rw [rho_apply]
      have hz : z = ofSeq (fun i => component z i) := (ofSeq_component z).symm
      conv_rhs => rw [hz]
      apply ofSeq_mono
      intro i
      show (if i < n then component z i else V.bot) ≤ component z i
      split
      · exact le_rfl
      · exact V.bot_le _
    exact hle Y hn
  · intro hzY
    have hY : (iterSys V).mem Y := z.sub hzY
    obtain ⟨N, hN⟩ := hY.2
    have hcomp : ∀ i, (component z i).mem (fiber Y i) := by
      have h := hzY
      rw [← ofSeq_component z] at h
      rw [mem_ofSeq] at h
      exact h.2
    refine ⟨N, ?_⟩
    rw [rho_apply, mem_ofSeq]
    refine ⟨hY, fun i => ?_⟩
    show (if i < N then component z i else V.bot).mem (fiber Y i)
    by_cases h : i < N
    · rw [ite_eq_left h]; exact hcomp i
    · rw [ite_eq_right h, hN i (not_lt.mp h)]; exact V.bot.master_mem

end Exercise618

end DomainTheory.NeighbourhoodSystems
