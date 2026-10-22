/-ai
In a continuous lattice, way-below interpolates: if a is way below c, some b satisfies a way below b and b way below c.

Let M be the set of elements m for which some x is way above m and way below c. The set M is directed. Given two such witnesses, directedness of the elements way below c produces a common upper bound still way below c, and directedness of the elements way below that bound, after the original elements are pushed up by monotonicity on the right, produces a common upper bound in M. The set M is nonempty because bottom is way below a and a is way below c. Its supremum is c: every member lies below c because way-below implies the order, while continuity writes c as the supremum of the elements way below it and each of those as the supremum of the elements way below it, all of which lie in M. Thus a is way below the supremum of the nonempty directed set M, so a is way below some member of M. That member is way below some x that is way below c, and monotonicity on the right gives a way below x.
ai-/
module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.Basic
public import DomainTheory.ContinuousLattice.WayBelow.WayBelowu2ele
public import DomainTheory.ContinuousLattice.WayBelow.bot_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.WayBelowu2etrans_le
public import DomainTheory.ContinuousLattice.WayBelow.wayBelow_sSup_iff
public import DomainTheory.ContinuousLattice.WayBelow.IsContinuousLatticeu2esSup_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.directedOn_wayBelow

@[expose] public section


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]


/-- **Interpolation property of `≪`.** In a continuous lattice, the way-below relation
interpolates: `a ≪ c` implies there is some `b` with `a ≪ b ≪ c`.

The proof runs Scott's standard argument: the set `M = {m | ∃ x, m ≪ x ∧ x ≪ c}` is directed
(using directedness of `{· ≪ x}` twice) and has supremum `c` (using continuity twice). Hence
`a ≪ c = ⊔M` with `M` directed forces `a ≪ m` for some `m ∈ M`, say `m ≪ x ≪ c`; then
`a ≪ m ≤ x` gives `a ≪ x ≪ c`, so `b := x` works. -/
theorem wayBelow_interpolate (hD : ContinuousLattice D) {a c : D} (hac : a ≪ c) :
    ∃ b, a ≪ b ∧ b ≪ c := by
  set M : Set D := {m | ∃ x, m ≪ x ∧ x ≪ c} with hM
  have hMdir : DirectedOn (· ≤ ·) M := by
    rintro m₁ ⟨x₁, hm₁x₁, hx₁c⟩ m₂ ⟨x₂, hm₂x₂, hx₂c⟩
    obtain ⟨x₃, hx₃c, hx₁₃, hx₂₃⟩ := directedOn_wayBelow c x₁ hx₁c x₂ hx₂c
    obtain ⟨m₃, hm₃x₃, hm₁m₃, hm₂m₃⟩ :=
      directedOn_wayBelow x₃ m₁ (hm₁x₁.trans_le hx₁₃) m₂ (hm₂x₂.trans_le hx₂₃)
    exact ⟨m₃, ⟨x₃, hm₃x₃, hx₃c⟩, hm₁m₃, hm₂m₃⟩
  have hMne : M.Nonempty := ⟨⊥, a, bot_wayBelow a, hac⟩
  have hsupM : sSup M = c := by
    refine le_antisymm (sSup_le ?_) ?_
    · rintro m ⟨x, hmx, hxc⟩
      exact hmx.le.trans hxc.le
    · rw [← hD.sSup_wayBelow c]
      refine sSup_le fun x hxc => ?_
      rw [← hD.sSup_wayBelow x]
      exact sSup_le fun m hmx => le_sSup ⟨x, hmx, hxc⟩
  rw [← hsupM] at hac
  obtain ⟨m, ⟨x, hmx, hxc⟩, ham⟩ := (wayBelow_sSup_iff hMne hMdir).1 hac
  exact ⟨x, ham.trans_le hmx.le, hxc⟩

end DomainTheory.ContinuousLattice
