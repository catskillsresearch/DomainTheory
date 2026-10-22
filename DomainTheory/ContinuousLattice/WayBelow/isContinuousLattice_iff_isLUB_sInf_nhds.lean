module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
import DomainTheory.ContinuousLattice.WayBelow.WayBelowu2ele
import DomainTheory.ContinuousLattice.WayBelow.sInf_wayBelow
public import Mathlib.Data.Set.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]


/-- **Scott 1972, Proposition 2.4.** A complete lattice is continuous iff every element is the
supremum of the infima of its open neighbourhoods: `y = ⊔ {⊓U : y ∈ U open}`. This is Scott's
alternate form of Definition 2.3. -/
theorem isContinuousLattice_iff_isLUB_sInf_nhds :
    ContinuousLattice D ↔
      ∀ y : D, IsLUB {a : D | ∃ U, ScottOpen U ∧ y ∈ U ∧ a = sInf U} y := by
  constructor
  · intro h y
    refine ⟨?_, ?_⟩
    · rintro a ⟨U, hU, hyU, rfl⟩
      exact (sInf_wayBelow hU hyU).le
    · intro b hb
      refine (h.out y).2 ?_
      intro x hx
      obtain ⟨U, hU, hyU, hsub⟩ := hx
      have hxle : x ≤ sInf U := le_sInf fun _ hz => Set.mem_Ici.1 (hsub hz)
      exact hxle.trans (hb ⟨U, hU, hyU, rfl⟩)
  · intro h
    refine { out := ?_ }
    intro y
    refine ⟨fun x hx => hx.le, ?_⟩
    intro b hb
    refine (h y).2 ?_
    rintro a ⟨U, hU, hyU, rfl⟩
    exact hb (sInf_wayBelow hU hyU)

end DomainTheory.ContinuousLattice
